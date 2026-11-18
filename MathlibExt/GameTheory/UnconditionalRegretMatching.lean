/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.BlackwellApproachability
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! # Unconditional regret matching is Hannan-consistent (expected-payoff form)

A decision maker with finite action set `A` faces an opponent's actions `b ∈ B` and pays the cost
`c a b`. Its *regret vector* for having played `a` against `b` has coordinates
`c a b − c k b`, `k ∈ A`, the saving it would have made with `k`. *Unconditional regret
matching* (Hart and Mas-Colell 2000, Theorem B; Hart 2005, §10.1) plays each action with
probability proportional to the positive part of the corresponding coordinate of the average
regret vector, and uniformly when no regret is positive.

Hart and Mas-Colell's proof is Blackwell's approachability theorem for the nonpositive orthant
of regret vectors: the nearest point of the orthant to `x` is `min(x, 0)`, the outer normal is
`x⁺`, and regret matching is exactly the mixed action that keeps the next expected regret vector
in the half-space through `min(x, 0)` with normal `x⁺`. This file carries out that argument for
expected payoffs, with `BlackwellApproachability.infDist_average_le`: against every sequence of
opponent actions, every average regret is at most `2R / √n` after `n` rounds, where `R` bounds
the norms of the regret vectors. Passing to realised payoffs (Hannan consistency proper) needs a
strong law of large numbers and is not done here.

## Main results

* `inner_posPart_mixedPayoff_urm`: regret matching satisfies Blackwell's condition for the
  orthant with equality.
* `average_regret_le_of_urm`: the `2R / √n` bound on the average expected regrets.

## References

* S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium",
  Econometrica 68(5) (2000), 1127–1150: §3, Theorem B and §4(c).
* S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430: §10.1, (10)–(11),
  Proposition 4.
-/

namespace MathlibExt.GameTheory.UnconditionalRegretMatching

open Finset Metric MathlibExt.GameTheory.BlackwellApproachability

variable {A B : Type*} [Fintype A]

/-- The **regret vector** of having played `a` against `b`: its `k`-th coordinate is the cost
`c a b − c k b` saved by playing `k` instead (Hart 2005, (10)–(11), in cost form). -/
def regretVector (c : A → B → ℝ) (a : A) (b : B) : EuclideanSpace ℝ A :=
  WithLp.toLp 2 fun k => c a b - c k b

/-- **Unconditional regret matching** (Hart and Mas-Colell 2000, Theorem B; Hart 2005, §10.1):
given the average regret vector `x`, play `k` with probability `x_k⁺ / ∑ₗ x_l⁺`, and uniformly
when no regret is positive. -/
noncomputable def urm (x : EuclideanSpace ℝ A) (k : A) : ℝ :=
  if 0 < ∑ l, max (x l) 0 then max (x k) 0 / ∑ l, max (x l) 0 else (Fintype.card A : ℝ)⁻¹

/-- The positive part `x⁺` of a vector, coordinatewise. -/
def posPart (x : EuclideanSpace ℝ A) : EuclideanSpace ℝ A := WithLp.toLp 2 fun k => max (x k) 0

/-- The negative part `min(x, 0)` of a vector, coordinatewise: the nearest point of the
nonpositive orthant. -/
def negPart (x : EuclideanSpace ℝ A) : EuclideanSpace ℝ A := WithLp.toLp 2 fun k => min (x k) 0

/-- The nonpositive orthant. -/
def orthant : Set (EuclideanSpace ℝ A) := {y | ∀ k, y k ≤ 0}

omit [Fintype A] in
private theorem sum_apply' {ι : Type*} (s : Finset ι) (f : ι → EuclideanSpace ℝ A) (k : A) :
    (∑ a ∈ s, f a) k = ∑ a ∈ s, f a k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, PiLp.add_apply, ih]

/-- Regret-matching probabilities are nonnegative. -/
theorem urm_nonneg (x : EuclideanSpace ℝ A) (k : A) : 0 ≤ urm x k := by
  unfold urm
  split_ifs with h
  · exact div_nonneg (le_max_right _ _) h.le
  · positivity

/-- Regret-matching probabilities add up to `1`. -/
theorem sum_urm [Nonempty A] (x : EuclideanSpace ℝ A) : ∑ k, urm x k = 1 := by
  unfold urm
  split_ifs with h
  · rw [← sum_div, div_self h.ne']
  · simp [Fintype.card_ne_zero]

/-- The `k`-th coordinate of the expected regret vector of the weights `q`:
`∑ₐ q(a) c(a, b) − (∑ₐ q(a)) c(k, b)`. -/
theorem mixedPayoff_regretVector_apply (c : A → B → ℝ) (q : A → ℝ) (b : B) (k : A) :
    mixedPayoff (regretVector c) q b k = ∑ a, q a * c a b - (∑ a, q a) * c k b := by
  simp only [mixedPayoff, sum_apply', PiLp.smul_apply, regretVector, smul_eq_mul, mul_sub,
    sum_sub_distrib, sum_mul]

omit [Fintype A] in
/-- `x − min(x, 0) = x⁺`. -/
theorem sub_negPart (x : EuclideanSpace ℝ A) : x - negPart x = posPart x := by
  ext k
  simp only [PiLp.sub_apply, negPart, posPart, PiLp.toLp_apply]
  rcases le_total (x k) 0 with h | h
  · rw [min_eq_left h, max_eq_right h]; ring
  · rw [min_eq_right h, max_eq_left h]; ring

/-- `x⁺` and `min(x, 0)` are orthogonal. -/
theorem inner_posPart_negPart (x : EuclideanSpace ℝ A) :
    @inner ℝ _ _ (posPart x) (negPart x) = 0 := by
  simp only [PiLp.inner_apply, posPart, negPart, RCLike.inner_apply, conj_trivial]
  refine sum_eq_zero fun k _ => ?_
  rcases le_total (x k) 0 with h | h
  · rw [max_eq_right h]; ring
  · rw [min_eq_right h]; ring

/-- **Regret matching meets Blackwell's condition with equality** (Hart and Mas-Colell 2000,
proof of Theorem B): playing `urm x` against any `b`, the expected regret vector is orthogonal to
`x⁺`. -/
theorem inner_posPart_mixedPayoff_urm [Nonempty A] (c : A → B → ℝ) (x : EuclideanSpace ℝ A)
    (b : B) : @inner ℝ _ _ (posPart x) (mixedPayoff (regretVector c) (urm x) b) = 0 := by
  simp only [PiLp.inner_apply, posPart, RCLike.inner_apply, conj_trivial,
    mixedPayoff_regretVector_apply, sum_urm, one_mul]
  set S := ∑ l, max (x l) 0
  by_cases hS : 0 < S
  · have hu : ∀ a, urm x a = max (x a) 0 / S := fun a => by simp [urm, S, hS]
    simp only [hu]
    have : ∑ a, max (x a) 0 / S * c a b = (∑ a, max (x a) 0 * c a b) / S := by
      rw [sum_div]; exact sum_congr rfl fun a _ => by ring
    rw [this]
    simp only [mul_comm _ (max _ _), mul_sub, sum_sub_distrib, ← sum_mul]
    field_simp
    ring
  · have h0 : ∀ k, max (x k) 0 = 0 := fun k => by
      have hS0 : S = 0 := le_antisymm (not_lt.1 hS) (sum_nonneg fun _ _ => le_max_right _ _)
      exact (sum_eq_zero_iff_of_nonneg fun _ _ => le_max_right _ _).1 hS0 k (mem_univ k)
    simp [h0]

/-- `min(x, 0)` is the nearest point of the nonpositive orthant to `x`: the distance is
`‖x⁺‖`. -/
theorem norm_posPart_eq_infDist (x : EuclideanSpace ℝ A) :
    ‖x - negPart x‖ = infDist x orthant := by
  have hmem : negPart x ∈ (orthant : Set (EuclideanSpace ℝ A)) := fun k => min_le_right _ _
  refine le_antisymm ?_ ?_
  · refine (le_infDist ⟨_, hmem⟩).2 fun y hy => ?_
    rw [dist_eq_norm, sub_negPart]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    refine sum_le_sum fun k _ => ?_
    simp only [posPart, PiLp.toLp_apply, PiLp.sub_apply]
    have := hy k
    rcases le_total (x k) 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg (x k - y k)]
    · rw [max_eq_left h]; nlinarith
  · rw [← dist_eq_norm]; exact infDist_le_dist_of_mem hmem

/-- `‖min(x, 0)‖ ≤ ‖x‖`. -/
theorem norm_negPart_le (x : EuclideanSpace ℝ A) : ‖negPart x‖ ≤ ‖x‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  refine sum_le_sum fun k _ => ?_
  simp only [negPart, PiLp.toLp_apply]
  rcases le_total (x k) 0 with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]; nlinarith [sq_nonneg (x k)]

/-- **Unconditional regret matching has vanishing expected regret** (expected-payoff form of
Hart and Mas-Colell 2000, Theorem B; Hart 2005, Proposition 4). Let `R` bound the norms of the
regret vectors. If the decision maker plays, at each round `t`, the mixed action `q_t` of
unconditional regret matching computed from the average expected regret vector of the previous
rounds, then against every sequence `β` of opponent actions and for every action `k`,
`(1/n) ∑_{t < n} (∑ₐ q_t(a) c(a, β_t) − c(k, β_t)) ≤ 2R / √n` for all `n ≥ 1`. -/
theorem average_regret_le_of_urm [Nonempty A] (c : A → B → ℝ) {R : ℝ}
    (hR : ∀ a b, ‖regretVector c a b‖ ≤ R) (β : ℕ → B) {n : ℕ} (hn : 0 < n) (k : A) :
    (n : ℝ)⁻¹ * ∑ t ∈ range n,
      (∑ a, urm (average (strategyPayoffs (regretVector c) urm β) t) a * c a (β t) -
        c k (β t)) ≤ 2 * R / Real.sqrt n := by
  set y := strategyPayoffs (regretVector c) urm β
  have havg : ∀ m, average y m = (m : ℝ)⁻¹ • strategySums (regretVector c) urm β m := fun m => by
    rw [average, sum_range_strategyPayoffs]
  have hy_eq : ∀ m, y m = mixedPayoff (regretVector c) (urm (average y m)) (β m) := fun m => by
    simp only [y, strategyPayoffs, havg]
  have hy : ∀ m, ‖y m‖ ≤ R := fun m => by
    rw [hy_eq]
    calc ‖mixedPayoff (regretVector c) (urm (average y m)) (β m)‖
        ≤ ∑ a, ‖urm (average y m) a • regretVector c a (β m)‖ := norm_sum_le _ _
      _ = ∑ a, urm (average y m) a * ‖regretVector c a (β m)‖ := by
          refine sum_congr rfl fun a _ => ?_
          rw [norm_smul, Real.norm_of_nonneg (urm_nonneg _ a)]
      _ ≤ ∑ a, urm (average y m) a * R :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hR a _) (urm_nonneg _ a)
      _ = R := by rw [← sum_mul, sum_urm, one_mul]
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hy 0)
  have havgR : ∀ m, ‖average y m‖ ≤ R := fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [average, hR0]
    · rw [average, norm_smul, Real.norm_of_nonneg (by positivity)]
      calc (m : ℝ)⁻¹ * ‖∑ j ∈ range m, y j‖ ≤ (m : ℝ)⁻¹ * ∑ j ∈ range m, ‖y j‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
        _ ≤ (m : ℝ)⁻¹ * ∑ _j ∈ range m, R :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => hy j) (by positivity)
        _ = R := by
            rw [sum_const, card_range, nsmul_eq_mul]
            have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
            field_simp
  have hdist : infDist (average y n) orthant ≤ (2 * R) / Real.sqrt n := by
    refine infDist_average_le (C := orthant) (c := fun m => negPart (average y m))
      (fun m j => min_le_right _ _) (fun m _ => norm_posPart_eq_infDist _) (fun m _ => ?_)
      (fun m => ?_) hn
    · rw [inner_sub_right, sub_negPart, inner_posPart_negPart, hy_eq,
        inner_posPart_mixedPayoff_urm, sub_zero]
    · calc ‖y m - negPart (average y m)‖ ≤ ‖y m‖ + ‖negPart (average y m)‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (hy m) ((norm_negPart_le _).trans (havgR m))
        _ = 2 * R := by ring
  -- the `k`-th coordinate of the average regret is at most its distance to the orthant
  have hcoord : average y n k ≤ infDist (average y n) orthant := by
    rw [← norm_posPart_eq_infDist, sub_negPart]
    calc average y n k ≤ max (average y n k) 0 := le_max_left _ _
      _ ≤ ‖max (average y n k) 0‖ := Real.le_norm_self _
      _ = ‖posPart (average y n) k‖ := rfl
      _ ≤ ‖posPart (average y n)‖ := PiLp.norm_apply_le _ _
  have hval : average y n k = (n : ℝ)⁻¹ * ∑ t ∈ range n,
      (∑ a, urm (average y t) a * c a (β t) - c k (β t)) := by
    rw [average, PiLp.smul_apply, sum_apply', smul_eq_mul]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [hy_eq, mixedPayoff_regretVector_apply, sum_urm, one_mul]
  rw [← hval]
  exact hcoord.trans hdist

end MathlibExt.GameTheory.UnconditionalRegretMatching
