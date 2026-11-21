/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lower bound for online convex optimization

One-dimensional scaled form of the `Ω(D * G * √T)` regret lower bound for
online convex optimization (Hazan, "Introduction to online convex
optimization", Section 3.2, Theorem 3.2).

Hazan phrases the result on the `n`-dimensional hypercube
`K = {x : ‖x‖∞ ≤ 1}` with linear losses `f_v(x) = v ⬝ x` over vertices
`v ∈ {±1}^n`. The one-dimensional scaled instance here already forces the
bound for every `D` and `G`: the domain is `K = [-D / 2, D / 2]` and the
losses are `x ↦ σ_t * G * x` with signs `σ_t ∈ {±1}`.

Everything is finite counting over sign sequences `σ : Fin T → Bool` with
the counting measure; no probability library is used beyond `Finset` sums
and real moments. The moment route: for `S = ∑ σ_t` (as reals),
`E[S ^ 2] = T` and `E[S ^ 4] ≤ 3 * T ^ 2`, and Cauchy-Schwarz applied
twice gives `(∑ S ^ 2) ^ 3 ≤ (∑ |S|) ^ 2 * ∑ S ^ 4`, hence
`E|S| ≥ √(T / 3)`.

A randomized online strategy is a distribution over the deterministic
adaptive strategies modeled here, and the same expectation bound applies
to its mean; this remark is not formalized.
-/

open scoped BigOperators

@[expose] public section

namespace Cslib.MachineLearning.OnlineConvexLowerBound

/-- Value of a sign bit as a real number: `true` is `+1`, `false` is `-1`. -/
def sgn : Bool → ℝ
  | true => 1
  | false => -1

/-- Round-`t` play of a deterministic online algorithm: the algorithm sees
only the first `t` signs of the length-`T` sequence. -/
def playAt (T : ℕ) (A : ∀ t : ℕ, (Fin t → Bool) → ℝ)
    (σ : Fin T → Bool) (t : Fin T) : ℝ :=
  A t.val fun i : Fin t.val => σ (Fin.castLE (le_of_lt (Fin.isLt t)) i)

/-- Regret of a deterministic online algorithm against a sign sequence at
gradient scale `G` on `[-D / 2, D / 2]`, with the comparator minimum
already evaluated (`comparator_lower_bound`, `comparator_attained`). -/
noncomputable def regret (T : ℕ) (A : ∀ t : ℕ, (Fin t → Bool) → ℝ) (D G : ℝ)
    (σ : Fin T → Bool) : ℝ :=
  (∑ t : Fin T, sgn (σ t) * G * playAt T A σ t) +
    G * (D / 2) * |∑ t : Fin T, sgn (σ t)|

/-- Every sign squares to one. -/
theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

/-- Every sign has absolute value one. -/
theorem sgn_abs (b : Bool) : |sgn b| = 1 := by
  cases b <;> simp [sgn, abs_neg]

/-- There are `2 ^ T` sign sequences of length `T`. -/
theorem card_sign_seq (T : ℕ) :
    (Finset.univ : Finset (Fin T → Bool)).card = 2 ^ T := by
  rw [Finset.card_univ, Fintype.card_pi]
  simp [Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The constant-one sum over sign sequences. -/
theorem sum_one_sign (T : ℕ) :
    ∑ _σ : Fin T → Bool, (1 : ℝ) = (2 : ℝ) ^ T := by
  simp

/-- The comparator minimum over `|x| ≤ D / 2`: no feasible `x` beats
`-(D / 2) * G * |S|`. This evaluates the comparator term in `regret`. -/
theorem comparator_lower_bound (D G S x : ℝ) (_hD : 0 ≤ D) (hG : 0 ≤ G)
    (hx : |x| ≤ D / 2) : -(D / 2) * G * |S| ≤ S * G * x := by
  have h1 : -(|S| * G * |x|) ≤ S * G * x := by
    have h := neg_abs_le (S * G * x)
    rwa [abs_mul, abs_mul, abs_of_nonneg hG] at h
  have h2 : |S| * G * |x| ≤ |S| * G * (D / 2) :=
    mul_le_mul_of_nonneg_left hx (mul_nonneg (abs_nonneg S) hG)
  have h3 : -(D / 2) * G * |S| = -(|S| * G * (D / 2)) := by ring
  rw [h3]
  exact (neg_le_neg h2).trans h1

/-- The comparator bound is attained: some feasible `x` achieves
`-(D / 2) * G * |S|`. -/
theorem comparator_attained (D G S : ℝ) (hD : 0 ≤ D) (_hG : 0 ≤ G) :
    ∃ x : ℝ, |x| ≤ D / 2 ∧ S * G * x = -(D / 2) * G * |S| := by
  by_cases hS : 0 ≤ S
  · refine ⟨-(D / 2), ?_, ?_⟩
    · rw [abs_neg, abs_of_nonneg (div_nonneg hD zero_le_two)]
    · rw [abs_of_nonneg hS]
      ring
  · refine ⟨D / 2, ?_, ?_⟩
    · rw [abs_of_nonneg (div_nonneg hD zero_le_two)]
    · rw [abs_of_neg (lt_of_not_ge hS)]
      ring

/-- Flip of a single coordinate of a sign sequence. -/
def signFlip (T : ℕ) (t : Fin T) (σ : Fin T → Bool) :
    Fin T → Bool :=
  fun t' => if t' = t then !(σ t') else σ t'

/-- The flip changes the flipped coordinate. -/
theorem signFlip_apply_same (T : ℕ) (t : Fin T) (σ : Fin T → Bool) :
    signFlip T t σ t = !(σ t) := by
  exact ite_eq_left rfl

/-- The flip fixes all other coordinates. -/
theorem signFlip_apply_ne (T : ℕ) (t t' : Fin T) (σ : Fin T → Bool)
    (h : t' ≠ t) : signFlip T t σ t' = σ t' := by
  exact ite_eq_right h

/-- Flipping twice is the identity. -/
theorem signFlip_involutive (T : ℕ) (t : Fin T) (σ : Fin T → Bool) :
    signFlip T t (signFlip T t σ) = σ := by
  funext t'
  by_cases h : t' = t
  · rw [h]
    rw [signFlip_apply_same, signFlip_apply_same]
    cases σ t <;> rfl
  · rw [signFlip_apply_ne _ _ _ _ h, signFlip_apply_ne _ _ _ _ h]

/-- The sign flips under boolean negation. -/
theorem sgn_not : ∀ (b : Bool), sgn (!b) = -sgn b
  | true => rfl
  | false => by simp [sgn]

/-- Coordinate flip as an equivalence. -/
def signFlipEquiv (T : ℕ) (t : Fin T) :
    (Fin T → Bool) ≃ (Fin T → Bool) where
  toFun σ := signFlip T t σ
  invFun σ := signFlip T t σ
  left_inv σ := signFlip_involutive T t σ
  right_inv σ := signFlip_involutive T t σ

/-- The online play is unchanged by flipping the current coordinate. -/
theorem playAt_flip (T : ℕ) (A : ∀ t : ℕ, (Fin t → Bool) → ℝ)
    (σ : Fin T → Bool) (t : Fin T) :
    playAt T A (signFlip T t σ) t = playAt T A σ t := by
  simp only [playAt]
  congr 1
  funext i
  have hne : Fin.castLE (le_of_lt (Fin.isLt t)) i ≠ t := by
    intro hcon
    have hval : (Fin.castLE (le_of_lt (Fin.isLt t)) i).val = t.val :=
      congrArg Fin.val hcon
    have h2 : (Fin.castLE (le_of_lt (Fin.isLt t)) i).val = i.val := rfl
    rw [h2] at hval
    exact absurd hval (ne_of_lt (Fin.isLt i))
  exact signFlip_apply_ne T t _ σ hne

/-- A sum that changes sign under the coordinate flip is zero. -/
theorem sum_eq_zero_of_flip (T : ℕ) (t : Fin T)
    (f : (Fin T → Bool) → ℝ)
    (hterm : ∀ σ : Fin T → Bool, f (signFlip T t σ) = -f σ) :
    ∑ σ : Fin T → Bool, f σ = 0 := by
  have hreindex : (∑ σ : Fin T → Bool, f ((signFlipEquiv T t) σ))
      = ∑ σ : Fin T → Bool, f σ :=
    Equiv.sum_comp (signFlipEquiv T t) f
  have hcoe : ∀ σ : Fin T → Bool, (signFlipEquiv T t) σ
      = signFlip T t σ := fun σ => rfl
  simp only [hcoe] at hreindex
  have hLHS : (∑ σ : Fin T → Bool, f (signFlip T t σ))
      = -∑ σ : Fin T → Bool, f σ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun σ _ => hterm σ)
  have hneg : -(∑ σ : Fin T → Bool, f σ)
      = ∑ σ : Fin T → Bool, f σ := hLHS.symm.trans hreindex
  exact eq_zero_of_neg_eq hneg

/-- Cross terms vanish for distinct rounds. -/
theorem sum_sgn_cross (T : ℕ) (t u : Fin T) (hne : t ≠ u) :
    ∑ σ : Fin T → Bool, sgn (σ t) * sgn (σ u) = 0 := by
  apply sum_eq_zero_of_flip T t
  intro σ
  show sgn ((signFlip T t σ) t) * sgn ((signFlip T t σ) u) =
    -(sgn (σ t) * sgn (σ u))
  rw [signFlip_apply_same, sgn_not,
    signFlip_apply_ne T t u σ (Ne.symm hne)]
  ring

/-- A squared sum is a double sum. -/
theorem sum_sq_expand (T : ℕ) (s : Fin T → ℝ) :
    (∑ t : Fin T, s t) ^ 2
      = ∑ t : Fin T, ∑ u : Fin T, s t * s u := by
  rw [pow_two, Finset.sum_mul_sum]

/-- Split a squared sign sum into diagonal and off-diagonal parts. -/
theorem sum_sq_split (T : ℕ) (σ : Fin T → Bool) :
    (∑ t : Fin T, sgn (σ t)) ^ 2 = (T : ℝ) +
      ∑ t : Fin T, ∑ u ∈ Finset.univ.erase t,
        sgn (σ t) * sgn (σ u) := by
  have hinner : ∀ t : Fin T, (∑ u : Fin T, sgn (σ t) * sgn (σ u))
      = sgn (σ t) * sgn (σ t) +
        ∑ u ∈ Finset.univ.erase t, sgn (σ t) * sgn (σ u) :=
    fun t => (Finset.add_sum_erase _ _ (Finset.mem_univ t)).symm
  have hdiag : (∑ t : Fin T, sgn (σ t) * sgn (σ t)) = (T : ℝ) := by
    simp only [sgn_mul_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [sum_sq_expand]
  simp only [hinner, Finset.sum_add_distrib]
  rw [hdiag]

/-- Second moment of the sign sum over all sign sequences: cross terms
vanish by the coordinate-flip symmetry, leaving `2 ^ T * T`.
Proof route: expand with `pow_two` and `Finset.sum_mul_sum`; the diagonal
contributes `T` (`sgn_mul_self`) and each off-diagonal cell sums to zero
by reindexing with `Equiv.sum_comp`. -/
theorem sum_sgn_sq_mean (T : ℕ) :
    ∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 2
      = (2 : ℝ) ^ T * (T : ℝ) := by
  have hswap : (∑ σ : Fin T → Bool, ∑ t : Fin T,
        ∑ u ∈ Finset.univ.erase t, sgn (σ t) * sgn (σ u))
        = ∑ t : Fin T, ∑ u ∈ Finset.univ.erase t,
          ∑ σ : Fin T → Bool, sgn (σ t) * sgn (σ u) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun t _ => Finset.sum_comm)
  have hoff : (∑ σ : Fin T → Bool, ∑ t : Fin T,
      ∑ u ∈ Finset.univ.erase t, sgn (σ t) * sgn (σ u)) = 0 := by
    rw [hswap]
    rw [Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun u hu =>
      sum_sgn_cross T t u (Ne.symm (Finset.ne_of_mem_erase hu))))]
    simp only [Finset.sum_const_zero]
  simp only [sum_sq_split, Finset.sum_add_distrib]
  rw [hoff, add_zero]
  have hconst : (∑ σ : Fin T → Bool, (T : ℝ))
      = (T : ℝ) * ∑ σ : Fin T → Bool, (1 : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => (mul_one _).symm)
  rw [hconst, sum_one_sign, mul_comm]

/-- Fourth-moment upper bound for the sign sum; the `≤` form suffices for
`khintchine_lower`. Proof route: induction that splits off the head
coordinate; for each tail sign sum, the two head choices contribute the sum
of the fourth powers at the tail sum plus one and at the tail sum minus
one, the odd terms cancel leaving twice the fourth power plus twelve
times the square plus two, and the induction hypothesis combines with the
exact second moment. -/
theorem sum_sgn_fourth_le (T : ℕ) :
    ∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 4
      ≤ (2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2) := by
  induction T with
  | zero =>
    show (∑ σ : Fin 0 → Bool, (∑ t : Fin 0, sgn (σ t)) ^ 4)
      ≤ (2 : ℝ) ^ (0 : ℕ) * (3 * ((0 : ℕ) : ℝ) ^ 2)
    have hL : (∑ σ : Fin 0 → Bool, (∑ t : Fin 0, sgn (σ t)) ^ 4) = 0 := by
      simp
    have hR : (2 : ℝ) ^ (0 : ℕ) * (3 * ((0 : ℕ) : ℝ) ^ 2) = 0 := by simp
    rw [hL, hR]
  | succ n ih =>
    show (∑ σ : Fin (n + 1) → Bool, (∑ t : Fin (n + 1), sgn (σ t)) ^ 4)
      ≤ (2 : ℝ) ^ (n + 1) * (3 * ((n + 1 : ℕ) : ℝ) ^ 2)
    set E : (Fin n → Bool) → Bool → ℝ := fun σ' b =>
      (∑ i : Fin n, sgn (σ' i)) ^ 4
        + 4 * (∑ i : Fin n, sgn (σ' i)) ^ 3 * sgn b
        + 6 * (∑ i : Fin n, sgn (σ' i)) ^ 2
        + 4 * (∑ i : Fin n, sgn (σ' i)) * sgn b + 1 with hEdef
    have hreindex : (∑ σ : Fin (n + 1) → Bool,
          (∑ t : Fin (n + 1), sgn (σ t)) ^ 4)
        = ∑ p : Bool × (Fin n → Bool),
          (∑ t : Fin (n + 1), sgn (((Fin.consEquiv fun _ => Bool) p) t)) ^ 4 :=
      (Equiv.sum_comp (Fin.consEquiv fun _ => Bool)
        (fun σ => (∑ t : Fin (n + 1), sgn (σ t)) ^ 4)).symm
    simp only [Fin.consEquiv_apply] at hreindex
    have hsplit : ∀ p : Bool × (Fin n → Bool),
        (∑ t : Fin (n + 1), sgn (Fin.cons (α := fun _ => Bool) p.1 p.2 t))
          = sgn p.1 + ∑ i : Fin n, sgn (p.2 i) := fun p => by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    have hexpand : ∀ p : Bool × (Fin n → Bool),
        (∑ t : Fin (n + 1), sgn (Fin.cons (α := fun _ => Bool) p.1 p.2 t)) ^ 4
          = E p.2 p.1 := fun p => by
      have hsq1 : sgn p.1 ^ 2 = 1 := by rw [pow_two]; exact sgn_mul_self _
      have hs3 : sgn p.1 ^ 3 = sgn p.1 := by
        rw [show sgn p.1 ^ 3 = sgn p.1 ^ 2 * sgn p.1 from by ring,
          hsq1, one_mul]
      have hs4 : sgn p.1 ^ 4 = 1 := by
        rw [show sgn p.1 ^ 4 = (sgn p.1 ^ 2) ^ 2 from by ring, hsq1,
          one_pow]
      rw [hsplit]
      simp only [hEdef]
      rw [show (sgn p.1 + ∑ i : Fin n, sgn (p.2 i)) ^ 4
        = sgn p.1 ^ 4 + 4 * sgn p.1 ^ 3 * (∑ i : Fin n, sgn (p.2 i))
          + 6 * sgn p.1 ^ 2 * (∑ i : Fin n, sgn (p.2 i)) ^ 2
          + 4 * sgn p.1 * (∑ i : Fin n, sgn (p.2 i)) ^ 3
          + (∑ i : Fin n, sgn (p.2 i)) ^ 4 from by ring]
      rw [hs4, hs3, hsq1]
      ring
    have hbool : ∀ σ' : Fin n → Bool, (∑ b : Bool, E σ' b)
        = 2 * (∑ i : Fin n, sgn (σ' i)) ^ 4
          + 12 * (∑ i : Fin n, sgn (σ' i)) ^ 2 + 2 := fun σ' => by
      simp only [hEdef]
      rw [Fintype.sum_bool]
      simp only [sgn]
      ring
    have hprod : (∑ p : Bool × (Fin n → Bool), E p.2 p.1)
        = ∑ b : Bool, ∑ σ' : Fin n → Bool, E σ' b :=
      Fintype.sum_prod_type _
    have hcomm : (∑ b : Bool, ∑ σ' : Fin n → Bool, E σ' b)
        = ∑ σ' : Fin n → Bool, ∑ b : Bool, E σ' b :=
      Finset.sum_comm
    have hcard2 : (∑ _σ' : Fin n → Bool, (2 : ℝ)) = (2 : ℝ) ^ n * 2 := by
      rw [Finset.sum_const, card_sign_seq, nsmul_eq_mul]
      simp [Nat.cast_pow]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
    have hN : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by linarith : (0:ℝ) ≤ 2) n
    rw [hreindex]
    simp only [hexpand]
    rw [hprod, hcomm]
    simp only [hbool]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hcard2, pow_succ, hcast]
    linarith [ih, sum_sgn_sq_mean n, hN]

/-- Moment algebra: two Cauchy-Schwarz bounds combine to `B ^ 3 ≤ A ^ 2 * C`. -/
theorem moment_algebra (A B C M : ℝ) (hAnn : 0 ≤ A) (hBnn : 0 ≤ B)
    (hCnn : 0 ≤ C) (_hMnn : 0 ≤ M) (hB2 : B ^ 2 ≤ A * M)
    (hM2 : M ^ 2 ≤ B * C) : B ^ 3 ≤ A ^ 2 * C := by
  have hBMC : (B * M) ^ 2 ≤ (A * C) * (B * M) := by
    have z1 : 0 ≤ B ^ 2 * (B * C - M ^ 2) :=
      mul_nonneg (sq_nonneg _) (by linarith [hM2])
    have z2 : 0 ≤ (B * C) * (A * M - B ^ 2) :=
      mul_nonneg (mul_nonneg hBnn hCnn) (by linarith [hB2])
    linarith [z1, z2]
  have hBM : B * M ≤ A * C := by
    nlinarith [hBMC, mul_nonneg hBnn _hMnn, mul_nonneg hAnn hCnn]
  have z1 : B * (B ^ 2 - A * M) ≤ 0 := by
    have h' : 0 ≤ B * (A * M - B ^ 2) :=
      mul_nonneg hBnn (by linarith [hB2])
    linarith [h']
  have z2 : A * (B * M - A * C) ≤ 0 := by
    have h' : 0 ≤ A * (A * C - B * M) :=
      mul_nonneg hAnn (by linarith [hBM])
    linarith [h']
  linarith [z1, z2]

/-- Khintchine-type lower bound: the mean absolute sign sum is at least
`√(T / 3)`. From `sum_sgn_sq_mean` and `sum_sgn_fourth_le` by
`Finset.sum_mul_sq_le_sq_mul_sq` applied twice, giving
`(∑ S ^ 2) ^ 3 ≤ (∑ |S|) ^ 2 * ∑ S ^ 4`. -/
theorem khintchine_lower (T : ℕ) :
    ∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)|
      ≥ (2 : ℝ) ^ T * Real.sqrt ((T : ℝ) / 3) := by
  by_cases hT0 : T = 0
  · subst hT0
    show (∑ σ : Fin 0 → Bool, |∑ t : Fin 0, sgn (σ t)|)
      ≥ (2 : ℝ) ^ (0 : ℕ) * Real.sqrt (((0 : ℕ) : ℝ) / 3)
    have hL : (∑ σ : Fin 0 → Bool, |∑ t : Fin 0, sgn (σ t)|) = 0 := by
      simp
    have hR : (2 : ℝ) ^ (0 : ℕ) * Real.sqrt (((0 : ℕ) : ℝ) / 3) = 0 := by
      simp
    rw [hL, hR]
  · have hTpos : 0 < T := by omega
    have hB : (∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 2)
        = (2 : ℝ) ^ T * (T : ℝ) := sum_sgn_sq_mean T
    have hC : (∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 4)
        ≤ (2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2) := sum_sgn_fourth_le T
    have hAnn : 0 ≤ ∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)| :=
      Finset.sum_nonneg (fun σ _ => abs_nonneg _)
    have hBnn : 0 ≤ ∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 2 :=
      Finset.sum_nonneg (fun σ _ => sq_nonneg _)
    have hCnn : 0 ≤ ∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 4 :=
      Finset.sum_nonneg (fun σ _ => by
        have h4 : (∑ t : Fin T, sgn (σ t)) ^ 4
            = ((∑ t : Fin T, sgn (σ t)) ^ 2) ^ 2 := by ring
        rw [h4]
        exact sq_nonneg _)
    have hMnn : 0 ≤ ∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)| ^ 3 :=
      Finset.sum_nonneg (fun σ _ => by
        have h3 : |∑ t : Fin T, sgn (σ t)| ^ 3
            = |∑ t : Fin T, sgn (σ t)| ^ 2 * |∑ t : Fin T, sgn (σ t)| := by
          ring
        rw [h3]
        exact mul_nonneg (sq_nonneg _) (abs_nonneg _))
    have hCS1 : ((∑ σ : Fin T → Bool,
          |∑ t : Fin T, sgn (σ t)| * |∑ t : Fin T, sgn (σ t)| ^ 2)) ^ 2
        ≤ (∑ σ : Fin T → Bool, (|∑ t : Fin T, sgn (σ t)|) ^ 2) *
          (∑ σ : Fin T → Bool, (|∑ t : Fin T, sgn (σ t)| ^ 2) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hM2 : ((∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)| ^ 3)) ^ 2
        ≤ (∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 2) *
          (∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 4) := by
      have eL : (∑ σ : Fin T → Bool,
            |∑ t : Fin T, sgn (σ t)| * |∑ t : Fin T, sgn (σ t)| ^ 2)
          = ∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)| ^ 3 :=
        Finset.sum_congr rfl (fun σ _ => by ring)
      have eR1 : (∑ σ : Fin T → Bool, (|∑ t : Fin T, sgn (σ t)|) ^ 2)
          = ∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 2 :=
        Finset.sum_congr rfl (fun σ _ => sq_abs _)
      have eR2 : (∑ σ : Fin T → Bool, (|∑ t : Fin T, sgn (σ t)| ^ 2) ^ 2)
          = ∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 4 :=
        Finset.sum_congr rfl (fun σ _ => by rw [sq_abs]; ring)
      rw [eL, eR1, eR2] at hCS1
      exact hCS1
    have hCS2 : ((∑ σ : Fin T → Bool, Real.sqrt |∑ t : Fin T, sgn (σ t)|
          * (|∑ t : Fin T, sgn (σ t)|
            * Real.sqrt |∑ t : Fin T, sgn (σ t)|))) ^ 2
        ≤ (∑ σ : Fin T → Bool,
            (Real.sqrt |∑ t : Fin T, sgn (σ t)|) ^ 2) *
          (∑ σ : Fin T → Bool,
            (|∑ t : Fin T, sgn (σ t)|
              * Real.sqrt |∑ t : Fin T, sgn (σ t)|) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hB2 : ((∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 2)) ^ 2
        ≤ (∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)|) *
          (∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)| ^ 3) := by
      have eL : (∑ σ : Fin T → Bool, Real.sqrt |∑ t : Fin T, sgn (σ t)|
            * (|∑ t : Fin T, sgn (σ t)|
              * Real.sqrt |∑ t : Fin T, sgn (σ t)|))
          = ∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 2 := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        have hsq : (Real.sqrt |∑ t : Fin T, sgn (σ t)|) ^ 2
            = |∑ t : Fin T, sgn (σ t)| :=
          Real.sq_sqrt (abs_nonneg _)
        have hss : Real.sqrt |∑ t : Fin T, sgn (σ t)|
              * (|∑ t : Fin T, sgn (σ t)|
                * Real.sqrt |∑ t : Fin T, sgn (σ t)|)
              = |∑ t : Fin T, sgn (σ t)| ^ 2 := by
          have e : Real.sqrt |∑ t : Fin T, sgn (σ t)|
                * (|∑ t : Fin T, sgn (σ t)|
                  * Real.sqrt |∑ t : Fin T, sgn (σ t)|)
                = |∑ t : Fin T, sgn (σ t)|
                  * (Real.sqrt |∑ t : Fin T, sgn (σ t)|) ^ 2 := by ring
          rw [e, hsq]
          ring
        rw [hss]
        exact sq_abs _
      have eR1 : (∑ σ : Fin T → Bool,
            (Real.sqrt |∑ t : Fin T, sgn (σ t)|) ^ 2)
          = ∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)| :=
        Finset.sum_congr rfl (fun σ _ => Real.sq_sqrt (abs_nonneg _))
      have eR2 : (∑ σ : Fin T → Bool,
            (|∑ t : Fin T, sgn (σ t)|
              * Real.sqrt |∑ t : Fin T, sgn (σ t)|) ^ 2)
          = ∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)| ^ 3 := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
        ring
      rw [eL, eR1, eR2] at hCS2
      exact hCS2
    have hB3 : (∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 2) ^ 3
        ≤ (∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)|) ^ 2
          * (∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 4) :=
      moment_algebra _ _ _ _ hAnn hBnn hCnn hMnn hB2 hM2
    have hST : (∑ t : Fin T, sgn ((fun _ => true) t)) = (T : ℝ) := by
      simp only [sgn, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
    have hCpos : 0 < ∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 4 := by
      have hterm : ∀ σ : Fin T → Bool,
          0 ≤ (∑ t : Fin T, sgn (σ t)) ^ 4 := fun σ => by
        have h4 : (∑ t : Fin T, sgn (σ t)) ^ 4
            = ((∑ t : Fin T, sgn (σ t)) ^ 2) ^ 2 := by ring
        rw [h4]
        exact sq_nonneg _
      have hle := Finset.single_le_sum (fun σ _ => hterm σ)
        (Finset.mem_univ (fun _ => true))
      rw [hST] at hle
      have hT4 : 0 < (T : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr hTpos) 4
      linarith [hle, hT4]
    have hTposR : 0 < (T : ℝ) := Nat.cast_pos.mpr hTpos
    have hA2 : ((2 : ℝ) ^ T) ^ 2 * ((T : ℝ) / 3)
        ≤ (∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)|) ^ 2 := by
      have h3 : (∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 2) ^ 3
          / (∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 4)
          ≤ (∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)|) ^ 2 := by
        rw [div_le_iff₀ hCpos]
        linarith [hB3]
      have h4 : ((2 : ℝ) ^ T) ^ 2 * ((T : ℝ) / 3)
          ≤ (∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 2) ^ 3
            / (∑ σ : Fin T → Bool, (∑ t : Fin T, sgn (σ t)) ^ 4) := by
        rw [hB, mul_pow, le_div_iff₀ hCpos]
        have ha0 : 0 ≤ ((2 : ℝ) ^ T) ^ 2 * ((T : ℝ) / 3) :=
          mul_nonneg (sq_nonneg _)
            (div_nonneg (le_of_lt hTposR) (by linarith : (0:ℝ) ≤ 3))
        have hmul := mul_le_mul_of_nonneg_left hC ha0
        have heq : ((2 : ℝ) ^ T) ^ 2 * ((T : ℝ) / 3)
            * ((2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2))
            = ((2 : ℝ) ^ T) ^ 3 * (T : ℝ) ^ 3 := by ring
        rw [heq] at hmul
        exact hmul
      exact h4.trans h3
    have hX2 : ((2 : ℝ) ^ T * Real.sqrt ((T : ℝ) / 3)) ^ 2
        = ((2 : ℝ) ^ T) ^ 2 * ((T : ℝ) / 3) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg (le_of_lt hTposR)
        (by linarith : (0:ℝ) ≤ 3))]
    rw [← hX2] at hA2
    exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) hAnn hA2

/-- The algorithm's own play has mean zero against the signs: for each
round, reindexing by the coordinate-`t` flip (`Equiv.sum_comp`) changes
the sign of `sgn (σ t)` while `playAt` is unchanged, since the
restriction reads only earlier coordinates; the sum equals its negation. -/
theorem online_play_expectation_zero (T : ℕ)
    (A : ∀ t : ℕ, (Fin t → Bool) → ℝ) (t : Fin T) :
    ∑ σ : Fin T → Bool, sgn (σ t) * playAt T A σ t = 0 := by
  apply sum_eq_zero_of_flip T t
  intro σ
  show sgn ((signFlip T t σ) t) * playAt T A (signFlip T t σ) t =
    -(sgn (σ t) * playAt T A σ t)
  rw [signFlip_apply_same, playAt_flip, sgn_not]
  ring

/-- Main lower bound: every deterministic online algorithm on
`[-D / 2, D / 2]` suffers regret at least
`(D * G / 2) * √(T / 3)` against some sign sequence. The comparator term is
already evaluated inside `regret`, with `comparator_lower_bound` and
`comparator_attained` justifying that evaluated form; by averaging,
`online_play_expectation_zero` kills the play term, so mean regret is
`(D * G / 2)` times the mean absolute sign sum, bounded below by
`khintchine_lower`; some sequence attains at least the mean
(`Finset.exists_le_of_sum_le`). -/
theorem oco_lower_bound (T : ℕ) (A : ∀ t : ℕ, (Fin t → Bool) → ℝ)
    (D G : ℝ) (_hT : 0 < T) (hD : 0 < D) (hG : 0 < G)
    (_hA : ∀ (t : ℕ) (s : Fin t → Bool), |A t s| ≤ D / 2) :
    ∃ σ : Fin T → Bool,
      (D * G / 2) * Real.sqrt ((T : ℝ) / 3)
        ≤ regret T A D G σ := by
  have hPreg : ∀ σ : Fin T → Bool, regret T A D G σ
      = (∑ t : Fin T, sgn (σ t) * G * playAt T A σ t) +
        G * (D / 2) * |∑ t : Fin T, sgn (σ t)| := fun σ => rfl
  have hsumP : (∑ σ : Fin T → Bool, ∑ t : Fin T,
      sgn (σ t) * G * playAt T A σ t) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun t _ => ?_)
    have hfactor : (∑ σ : Fin T → Bool, sgn (σ t) * G * playAt T A σ t)
        = G * (∑ σ : Fin T → Bool, sgn (σ t) * playAt T A σ t) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun σ _ => by ring)
    rw [hfactor, online_play_expectation_zero T A t, mul_zero]
  have hsumC : (∑ σ : Fin T → Bool, G * (D / 2) * |∑ t : Fin T, sgn (σ t)|)
      = G * (D / 2)
        * (∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)|) := by
    rw [← Finset.mul_sum]
  have hnonneg : 0 ≤ G * (D / 2) :=
    mul_nonneg (le_of_lt hG) (div_nonneg (le_of_lt hD) zero_le_two)
  have htot : (∑ σ : Fin T → Bool, regret T A D G σ)
      = G * (D / 2)
        * (∑ σ : Fin T → Bool, |∑ t : Fin T, sgn (σ t)|) := by
    simp only [hPreg, Finset.sum_add_distrib, hsumP, zero_add, hsumC]
  have hmean : (2 : ℝ) ^ T * ((D * G / 2) * Real.sqrt ((T : ℝ) / 3))
      ≤ ∑ σ : Fin T → Bool, regret T A D G σ := by
    rw [htot]
    have hmul := mul_le_mul_of_nonneg_left (khintchine_lower T) hnonneg
    have heq : (2 : ℝ) ^ T * ((D * G / 2) * Real.sqrt ((T : ℝ) / 3))
        = G * (D / 2) * ((2 : ℝ) ^ T * Real.sqrt ((T : ℝ) / 3)) := by
      ring
    rw [heq]
    exact hmul
  have hcard : (∑ _σ : Fin T → Bool, (D * G / 2) * Real.sqrt ((T : ℝ) / 3))
      = (2 : ℝ) ^ T * ((D * G / 2) * Real.sqrt ((T : ℝ) / 3)) := by
    have h1 : (∑ _σ : Fin T → Bool, (D * G / 2) * Real.sqrt ((T : ℝ) / 3))
        = ((D * G / 2) * Real.sqrt ((T : ℝ) / 3))
          * ∑ _σ : Fin T → Bool, (1 : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun σ _ => (mul_one _).symm)
    rw [h1, sum_one_sign, mul_comm]
  have hle : (∑ _σ : Fin T → Bool, (D * G / 2) * Real.sqrt ((T : ℝ) / 3))
      ≤ ∑ σ : Fin T → Bool, regret T A D G σ := by
    rw [hcard]
    exact hmean
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_sum_le
    ⟨fun _ => true, Finset.mem_univ _⟩ hle
  exact ⟨σ, hσ⟩

end Cslib.MachineLearning.OnlineConvexLowerBound
