/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Optimization.LineSearch
public import Mathlib.Topology.Bornology.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fletcher–Reeves convergence under strong Wolfe line searches
-/

@[expose] public section

namespace WantedExt.Analysis.Optimization.FletcherReevesWanted

open scoped RealInnerProductSpace
open MathlibExt.Analysis.Optimization.LineSearch

/-- Pair adjacent terms to compare with the harmonic series even if individual ratios get small. -/
private theorem not_summable_of_adjacent_ratios {r D : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hDpos : ∀ k, 0 < D k) (hD : ∀ k, D k ≤ C * ((k : ℝ) + 1))
    (hr : ∀ k, 1 / 4 ≤ r k ^ 2 + r (k + 1) ^ 2) :
    ¬ Summable fun k => r k ^ 2 / D k := by
  intro hz
  have hshift := (summable_nat_add_iff (f := fun k => r k ^ 2 / D k) 1).2 hz
  have hsum := (hz.add hshift).mul_left (4 * C)
  have hle (k : ℕ) : 1 / ((k : ℝ) + 2) ≤ 4 * C * (r k ^ 2 / D k + r (k + 1) ^ 2 / D (k + 1)) := by
    have hden : 0 < C * ((k : ℝ) + 2) := by positivity
    have hk : D k ≤ C * ((k : ℝ) + 2) := (hD k).trans (by gcongr; norm_num)
    have hks : D (k + 1) ≤ C * ((k : ℝ) + 2) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hD (k + 1)
    calc
      1 / ((k : ℝ) + 2) = 4 * C * ((1 / 4) / (C * ((k : ℝ) + 2))) := by
        field_simp
      _ ≤ 4 * C * ((r k ^ 2 + r (k + 1) ^ 2) / (C * ((k : ℝ) + 2))) := by gcongr; exact hr k
      _ ≤ 4 * C * (r k ^ 2 / D k + r (k + 1) ^ 2 / D (k + 1)) := by
        rw [add_div]
        gcongr <;> exact hDpos _
  have harm : Summable (fun k : ℕ => 1 / ((k : ℝ) + 2)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hle hsum
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 2).mp (by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using harm))

-- Keep the original names of the level-set boundedness, openness and differentiability hypotheses.
-- The direct proof only needs the lower bound and the Lipschitz estimate on successive iterates.
set_option linter.unusedVariables false in
/-- **Global convergence of the Fletcher–Reeves method under strong Wolfe steps.** Let `f` be a
function on a finite-dimensional real inner product space whose level set `{y | f y ≤ f (x 0)}`
is bounded. Assume `f` is bounded below on this level set and, on an open neighbourhood `U` of it,
is differentiable with `L`-Lipschitz gradient. Run `x (k + 1) = x k + α k • d k` with
`d 0 = -∇f(x 0)` and
`d (k + 1) = -∇f(x (k + 1)) + (‖∇f(x (k + 1))‖² / ‖∇f(x k)‖²) • d k`, where every step length
`α k > 0` satisfies the strong Wolfe conditions with `0 < δ < σ ≤ 1/2`. If no gradient vanishes,
then `liminf ‖∇f(x k)‖ = 0`.

This is the Fletcher–Reeves conclusion of Y. H. Dai and Y. Yuan, *A note on the nonlinear conjugate
gradient method*, J. Comput. Math. 20 (2002), Theorem 4.2, with an explicit lower-bound hypothesis
not stated in its Assumption 2.1. Armijo keeps the iterates in the starting level set, so the lower
bound on that set suffices for `MathlibExt.Analysis.Optimization.LineSearch.zoutendijk`. The earlier
Dai–Yuan paper, *A nonlinear conjugate gradient method with a strong global convergence property*,
SIAM J. Optim. 10 (1999), Assumption 3.1, instead assumes a global lower bound. -/
theorem fletcherReeves_liminf_norm_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {f : E → ℝ} {δ σ L : ℝ} (hδ : 0 < δ)
    (hδσ : δ < σ) (hσ : σ ≤ 1 / 2) {x d : ℕ → E} {α : ℕ → ℝ}
    (hlevel : Bornology.IsBounded {y | f y ≤ f (x 0)})
    (hlower : BddBelow (f '' {y | f y ≤ f (x 0)})) {U : Set E} (hU : IsOpen U)
    (hlevelU : {y | f y ≤ f (x 0)} ⊆ U) (hdiff : DifferentiableOn ℝ f U)
    (hlip : ∀ y ∈ U, ∀ z ∈ U, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖)
    (hx : ∀ k, x (k + 1) = x k + α k • d k) (hα : ∀ k, 0 < α k)
    (hd0 : d 0 = -gradient f (x 0))
    (hd : ∀ k, d (k + 1) = -gradient f (x (k + 1)) +
      (‖gradient f (x (k + 1))‖ ^ 2 / ‖gradient f (x k)‖ ^ 2) • d k)
    (hwolfe : ∀ k, StrongWolfeConditions f δ σ (x k) (d k) (α k))
    (hg : ∀ k, gradient f (x k) ≠ 0) :
    ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, ‖gradient f (x k)‖ < ε := by
  let g (k : ℕ) := gradient f (x k)
  let s (k : ℕ) := (‖g k‖ ^ 2)⁻¹
  let p (k : ℕ) := s k • d k
  let r (k : ℕ) := -⟪g k, p k⟫
  have hgpos (k : ℕ) : 0 < ‖g k‖ := norm_pos_iff.mpr (hg k)
  have hs (k : ℕ) : 0 < s k := inv_pos.mpr (pow_pos (hgpos k) 2)
  have hs_norm (k : ℕ) : s k * ‖g k‖ ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 (hgpos k).ne')
  -- Normalizing by the squared gradient norm cancels the Fletcher–Reeves coefficient.
  have hp (k : ℕ) : p (k + 1) = p k - s (k + 1) • g (k + 1) := by
    have hscale : s (k + 1) * (‖g (k + 1)‖ ^ 2 / ‖g k‖ ^ 2) = s k := by
      rw [div_eq_mul_inv, ← mul_assoc, hs_norm, one_mul]
    change s (k + 1) • d (k + 1) = _
    rw [show d (k + 1) = -g (k + 1) + (‖g (k + 1)‖ ^ 2 / ‖g k‖ ^ 2) • d k from hd k,
      smul_add, smul_neg, smul_smul, hscale, neg_add_eq_sub]
  have hr0 : r 0 = 1 := by
    change -⟪g 0, s 0 • d 0⟫ = 1
    rw [show d 0 = -g 0 from hd0, real_inner_smul_right, inner_neg_right,
      real_inner_self_eq_norm_sq, mul_neg, neg_neg, hs_norm]
  have hnext (k : ℕ) : r (k + 1) - 1 = -⟪g (k + 1), p k⟫ := by
    dsimp only [r]
    rw [hp k, inner_sub_right, real_inner_smul_right (g (k + 1)) (g (k + 1)) (s (k + 1)),
      real_inner_self_eq_norm_sq, hs_norm]
    ring
  have hcontract (k : ℕ) : |r (k + 1) - 1| ≤ σ * r k := by
    have hw := (hwolfe k).2
    rw [← hx k] at hw
    rw [hnext, abs_neg]
    dsimp only [r, p]
    rw [real_inner_smul_right, real_inner_smul_right, abs_mul, abs_of_pos (hs k)]
    calc
      _ ≤ s k * (-σ * ⟪g k, d k⟫) := mul_le_mul_of_nonneg_left hw (hs k).le
      _ = _ := by ring
  have hr (k : ℕ) : 0 < r k ∧ r k < 2 := by
    induction k with
    | zero => rw [hr0]; norm_num
    | succ k ih =>
      have hb := abs_le.mp (hcontract k)
      have hhalf := mul_le_mul_of_nonneg_right hσ ih.1.le
      constructor <;> linarith [ih.2, hb.1, hb.2]
  have hdesc (k : ℕ) : ⟪gradient f (x k), d k⟫ < 0 := by
    have h := (hr k).1
    change 0 < -⟪g k, s k • d k⟫ at h
    rw [real_inner_smul_right, neg_pos] at h
    by_contra! hn
    exact (not_lt_of_ge (mul_nonneg (hs k).le hn)) h
  have hxlevel (k : ℕ) : f (x k) ≤ f (x 0) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have harm := (hwolfe k).1
      unfold ArmijoCondition at harm
      rw [← hx k] at harm
      have hdecr := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hδ.le (hα k).le) (hdesc k).le
      linarith
  have hbdd : BddBelow (Set.range fun k => f (x k)) :=
    hlower.mono (by rintro _ ⟨k, rfl⟩; exact ⟨x k, hxlevel k, rfl⟩)
  have hlip' (k : ℕ) : ‖g (k + 1) - g k‖ ≤ max 1 L * ‖x (k + 1) - x k‖ :=
    (hlip _ (hlevelU (hxlevel (k + 1))) _ (hlevelU (hxlevel k))).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 L) (norm_nonneg _))
  have hz : Summable fun k => r k ^ 2 / ‖p k‖ ^ 2 := by
    refine (zoutendijk hδ (by linarith : σ < 1) (lt_of_lt_of_le zero_lt_one (le_max_left 1 L))
      hx hα hdesc (fun k => (hwolfe k).toWolfeConditions) hlip' hbdd).congr ?_
    intro k
    dsimp only [r, p]
    rw [real_inner_smul_right, norm_smul, Real.norm_of_nonneg (hs k).le, neg_sq, mul_pow, mul_pow,
      mul_div_mul_left _ _ (pow_ne_zero 2 (hs k).ne')]
  -- The endpoint σ = 1/2 need not give a uniform lower bound on each ratio.
  -- The curvature estimate gives a lower bound for the sum of two consecutive squares.
  have hpair (k : ℕ) : 1 / 4 ≤ r k ^ 2 + r (k + 1) ^ 2 := by
    have hsq {a b : ℝ} (ha : 1 / 2 ≤ a) : 1 / 4 ≤ a ^ 2 + b ^ 2 := by
      calc
        1 / 4 = (1 / 2 : ℝ) ^ 2 := by norm_num
        _ ≤ a ^ 2 := by gcongr
        _ ≤ a ^ 2 + b ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    by_cases hk : 1 / 2 ≤ r k
    · exact hsq hk
    · rw [add_comm]
      apply hsq
      have h := (abs_le.mp (hcontract k)).1
      have hhalf := mul_le_mul_of_nonneg_right hσ (hr k).1.le
      linarith [lt_of_not_ge hk]
  have hp_pos (k : ℕ) : 0 < ‖p k‖ ^ 2 := by
    have hp_ne : p k ≠ 0 := by
      intro h
      simpa [r, h] using (hr k).1
    positivity
  have hDstep (k : ℕ) : ‖p (k + 1)‖ ^ 2 = ‖p k‖ ^ 2 + (2 * r (k + 1) - 1) * s (k + 1) := by
    have heq : p k = s (k + 1) • g (k + 1) + p (k + 1) := by rw [hp, add_sub_cancel]
    have hnorm : ‖s (k + 1) • g (k + 1)‖ ^ 2 = s (k + 1) := by
      rw [norm_smul, Real.norm_of_nonneg (hs (k + 1)).le]
      calc
        _ = s (k + 1) * (s (k + 1) * ‖g (k + 1)‖ ^ 2) := by ring
        _ = _ := by rw [hs_norm, mul_one]
    have heq' := congrArg (fun u : E => ‖u‖ ^ 2) heq
    rw [norm_add_sq_real, hnorm, real_inner_smul_left] at heq'
    rw [heq']
    dsimp only [r]
    ring
  intro ε hε N
  by_contra! hbad
  let C := ‖p N‖ ^ 2 + 3 / ε ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hstep (k : ℕ) : ‖p (N + k + 1)‖ ^ 2 ≤ ‖p (N + k)‖ ^ 2 + 3 / ε ^ 2 := by
    have hnorm : ε ≤ ‖g (N + k + 1)‖ := hbad _ (by omega)
    have hs' : s (N + k + 1) ≤ 1 / ε ^ 2 := by
      change (‖g (N + k + 1)‖ ^ 2)⁻¹ ≤ _
      rw [inv_eq_one_div]
      apply div_le_div_of_nonneg_left zero_le_one (by positivity)
      gcongr
    rw [hDstep]
    calc
      _ ≤ ‖p (N + k)‖ ^ 2 + 3 * s (N + k + 1) := by gcongr; linarith [(hr (N + k + 1)).2]
      _ ≤ _ := by rw [div_eq_mul_one_div 3]; gcongr
  have hD (k : ℕ) : ‖p (N + k)‖ ^ 2 ≤ C * ((k : ℝ) + 1) := by
    have hinc : 3 / ε ^ 2 ≤ C := le_add_of_nonneg_left (sq_nonneg _)
    induction k with
    | zero =>
      simpa only [Nat.add_zero, Nat.cast_zero, zero_add, mul_one] using
        (le_add_of_nonneg_right (a := ‖p N‖ ^ 2) (by positivity : 0 ≤ 3 / ε ^ 2))
    | succ k ih =>
      change ‖p (N + k + 1)‖ ^ 2 ≤ C * ((↑(k + 1) : ℝ) + 1)
      rw [Nat.cast_add, Nat.cast_one]
      linarith [hstep k]
  apply not_summable_of_adjacent_ratios (r := fun k => r (N + k)) (D := fun k => ‖p (N + k)‖ ^ 2)
    hC (fun k => hp_pos (N + k)) hD (fun k => by simpa only [← Nat.add_assoc] using hpair (N + k))
  simpa only [Nat.add_comm N] using
    (summable_nat_add_iff (f := fun k => r k ^ 2 / ‖p k‖ ^ 2) N).2 hz

end WantedExt.Analysis.Optimization.FletcherReevesWanted
