/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.InnerProductSpace.Calculus
import MathlibExt.Analysis.InnerProductSpace.LpShiftOperatorSpectrum
import MathlibExt.Analysis.InnerProductSpace.ShiftFredholmIndex

/-!
# Lower complexity bound for strongly convex first-order minimisation

The strongly convex lower complexity bound of Section 2.1.4 of Yu. Nesterov, *Introductory
Lectures on Convex Programming, Volume I: Basic course* (lecture notes, July 2, 1998): no method
whose iterates stay in `x 0 + span {∇f (x 0), …, ∇f (x (j - 1))}` (Assumption 2.1.4 there) can
contract faster than `((√Q - 1) / (√Q + 1)) ^ (2 k)`. The span condition is stated for every `j`;
for `j = 0` it only says `x 0 = x₀`. The smooth convex bound, Theorem 2.1.6 there, is proved in
`MathlibExt.Analysis.Convex.FirstOrderLowerBound`.
-/

@[expose] public section

open scoped ContDiff InnerProduct

namespace WantedExt.Analysis.Convex.FirstOrderLowerBoundWanted

open ContinuousLinearMap
open MathlibExt.Analysis.InnerProductSpace
open LpShiftOperator LpShiftOperatorSpectrum ShiftFredholmIndex

local notation "H" => lp (fun _ : ℕ => ℝ) 2

-- Factoring the tridiagonal Hessian as μ T†T makes both spectral bounds explicit.
private noncomputable def factor (a b : ℝ) : H →L[ℝ] H :=
  a • ContinuousLinearMap.id ℝ H - b • shiftCLM

private lemma factor_bounds {a b : ℝ} (hb : 0 ≤ b) (hab : a - b = 1) (z : H) :
    ‖z‖ ≤ ‖factor a b z‖ ∧ ‖factor a b z‖ ≤ (a + b) * ‖z‖ := by
  have ha : 0 ≤ a := by linarith
  change ‖z‖ ≤ ‖a • z - b • shiftCLM z‖ ∧ _
  have lower := norm_sub_norm_le (a • z) (b • shiftCLM z)
  have upper := norm_sub_le (a • z) (b • shiftCLM z)
  simp only [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, norm_shiftCLM_apply]
    at lower upper
  rw [← sub_mul, hab, one_mul] at lower
  exact ⟨lower, by simpa [factor, add_mul] using upper⟩

private noncomputable def energy (μ : ℝ) (T : H →L[ℝ] H) (c x : H) : ℝ :=
  μ / 2 * ‖T (x - c)‖ ^ 2

private lemma gradient_energy (μ : ℝ) (T : H →L[ℝ] H) (c x : H) :
    gradient (energy μ T c) x = μ • (T†) (T (x - c)) := by
  have hd := T.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c)
  have he := hd.norm_sq.const_mul (μ / 2)
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  apply he.congr_fderiv
  ext w
  simp [InnerProductSpace.toDual_apply_apply, adjoint_inner_left]
  ring

private lemma strongConvexOn_energy {μ : ℝ} (hμ : 0 ≤ μ) (T : H →L[ℝ] H)
    (hT : ∀ z, ‖z‖ ≤ ‖T z‖) (c : H) : StrongConvexOn Set.univ μ (energy μ T c) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hshift : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    rw [smul_sub, smul_sub]
    have hc : a • c + b • c = c := by rw [← add_smul, hab, one_smul]
    linear_combination (norm := abel) hc
  let u := T (x - c)
  let v := T (y - c)
  have hdiff : T (x - y) = u - v := by
    dsimp [u, v]
    rw [← map_sub, sub_sub_sub_cancel_right]
  have hsq : ‖x - y‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by
    rw [← hdiff]
    gcongr
    exact hT _
  have hcombo : ‖a • u + b • v‖ ^ 2 =
      a * ‖u‖ ^ 2 + b * ‖v‖ ^ 2 - a * b * ‖u - v‖ ^ 2 := by
    rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
      real_inner_smul_left, real_inner_smul_right, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    rw [show b = 1 - a by linarith]
    ring
  simp only [energy, hshift, map_add, map_smul, smul_eq_mul]
  change μ / 2 * ‖a • u + b • v‖ ^ 2 ≤ _
  rw [hcombo]
  dsimp only [u, v] at *
  nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg (mul_nonneg ha hb) hμ)]

private lemma lipschitzWith_gradient_energy {μ Q : ℝ} (hμ : 0 ≤ μ) (hQ : 0 ≤ Q)
    (T : H →L[ℝ] H) (hT : ‖T‖ ≤ √Q) (c : H) :
    LipschitzWith ⟨μ * Q, mul_nonneg hμ hQ⟩ (gradient (energy μ T c)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, gradient_energy, gradient_energy, ← smul_sub,
    ← map_sub, ← map_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg hμ]
  change μ * ‖(T†) (T (x - y))‖ ≤ μ * Q * ‖x - y‖
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hμ
  calc
    ‖(T†) (T (x - y))‖ ≤ ‖T†‖ * ‖T (x - y)‖ := le_opNorm _ _
    _ ≤ √Q * (√Q * ‖x - y‖) := by
      rw [LinearIsometryEquiv.norm_map]
      gcongr
      exact (T.le_opNorm _).trans (by gcongr)
    _ = Q * ‖x - y‖ := by rw [← mul_assoc, Real.mul_self_sqrt hQ]

-- At coordinates n + 1 and beyond, the geometric minimiser cancels out of the gradient.
private lemma factor_succ (a b : ℝ) (z : H) (n : ℕ) :
    factor a b z (n + 1) = a * z (n + 1) - b * z n := rfl

private lemma adjoint_factor_apply (a b : ℝ) (z : H) (n : ℕ) :
    ((factor a b)†) z n = a * z n - b * z (n + 1) := by
  simp [factor, adjoint_shiftCLM, adjoint_id]
  rfl

private lemma gradient_zero_of_tail {a b q : ℝ} (hq : ‖q‖ < 1) (haq : a * q = b)
    (μ : ℝ) {x x₀ : H} {i : ℕ} (hx : ∀ n, i ≤ n → (x - x₀) n = 0) :
    ∀ n, i < n → gradient (energy μ (factor a b) (x₀ + geometricVec hq)) x n = 0 := by
  have htail (j : ℕ) (hj : i ≤ j) :
      factor a b (x - (x₀ + geometricVec hq)) (j + 1) = 0 := by
    rw [← sub_sub, map_sub]
    simp only [lp.coeFn_sub, Pi.sub_apply, factor_succ, geometricVec_apply, pow_succ',
      hx _ hj, hx _ (Nat.le_succ_of_le hj), ← mul_assoc, haq]
    ring
  rintro (_ | n) hn
  · omega
  · rw [gradient_energy]
    change μ * (((factor a b)†) _ (n + 1)) = 0
    rw [adjoint_factor_apply, htail n (by omega), htail (n + 1) (by omega)]
    ring

-- Dropping the first k coordinates is a contraction. On the geometric tail it is
-- exactly multiplication by q ^ k.
private lemma geometric_tail_bound {q : ℝ} (hq : ‖q‖ < 1) (hq₀ : 0 ≤ q) (k : ℕ) (z : H)
    (hz : ∀ n, k ≤ n → z n = 0) :
    q ^ (2 * k) * ‖geometricVec hq‖ ^ 2 ≤ ‖z - geometricVec hq‖ ^ 2 := by
  let B := backwardCLM (𝕜 := ℝ) ^ k
  have hB : ‖B‖ ≤ 1 := by
    rcases k.eq_zero_or_pos with rfl | hk
    · simpa [B] using (norm_one_le (𝕜 := ℝ))
    · exact (norm_pow_le' _ hk).trans (pow_le_one₀ (norm_nonneg _) norm_backwardCLM_le)
  have htail : B (z - geometricVec hq) = -(q ^ k) • geometricVec hq := by
    apply lp.ext
    funext j
    change (backwardCLM ^ k) (z - geometricVec hq) j = -(q ^ k) * geometricVec hq j
    simp [backwardCLM_pow_apply, hz _ (Nat.le_add_left k j), geometricVec_apply, pow_add, mul_comm]
  have hnorm := B.le_opNorm (z - geometricVec hq)
  rw [htail, norm_smul, norm_neg, Real.norm_of_nonneg (pow_nonneg hq₀ _)] at hnorm
  have hle : q ^ k * ‖geometricVec hq‖ ≤ ‖z - geometricVec hq‖ :=
    hnorm.trans (mul_le_of_le_one_left (norm_nonneg _) hB)
  rw [Nat.mul_comm 2 k, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hle 2

-- Keep the positivity proof in the Lipschitz constant inline, as in the wanted statement.
set_option backward.proofsInPublic true in
/-- **Lower complexity bound for smooth strongly convex minimisation.** Let `μ > 0` and `Q > 1`.
For every `x₀ ∈ ℓ²` there is a `μ`-strongly convex `C^∞` function `f` on `ℓ²` with
`μ Q`-Lipschitz gradient and a minimiser `x⋆ ≠ x₀` such that every sequence with `x 0 = x₀` and
`x j - x₀ ∈ span {∇f (x i) : i < j}` for all `j` satisfies, for every `k`,
`‖x k - x⋆‖ ^ 2 ≥ ((√Q - 1) / (√Q + 1)) ^ (2 k) ‖x₀ - x⋆‖ ^ 2` and
`f (x k) - f x⋆ ≥ μ / 2 ((√Q - 1) / (√Q + 1)) ^ (2 k) ‖x₀ - x⋆‖ ^ 2`. Since `‖x₀ - x⋆‖ > 0`, both
bounds are positive: they are not met trivially by taking `x⋆ = x₀` (for instance
`f z = μ ‖z - x₀‖ ^ 2 / 2`).

This is Theorem 2.1.12 of Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I:
Basic course* (lecture notes, July 2, 1998), stated there on `R^∞`, the space `ℓ²` of
square-summable sequences, for the class `S^{∞,1}_{μ, μ Q}`. -/
theorem exists_lower_bound_strongly_convex {μ Q : ℝ} (hμ : 0 < μ) (hQ : 1 < Q)
    (x₀ : lp (fun _ : ℕ => ℝ) 2) :
    ∃ f : lp (fun _ : ℕ => ℝ) 2 → ℝ, ContDiff ℝ ∞ f ∧ StrongConvexOn Set.univ μ f ∧
      LipschitzWith ⟨μ * Q, by positivity⟩ (gradient f) ∧
      ∃ xstar : lp (fun _ : ℕ => ℝ) 2, xstar ≠ x₀ ∧ (∀ z, f xstar ≤ f z) ∧
        ∀ x : ℕ → lp (fun _ : ℕ => ℝ) 2, x 0 = x₀ →
          (∀ j, x j - x₀ ∈ Submodule.span ℝ ((fun i => gradient f (x i)) '' Set.Iio j)) →
          ∀ k : ℕ,
            ((√Q - 1) / (√Q + 1)) ^ (2 * k) * ‖x₀ - xstar‖ ^ 2 ≤ ‖x k - xstar‖ ^ 2 ∧
              μ / 2 * ((√Q - 1) / (√Q + 1)) ^ (2 * k) * ‖x₀ - xstar‖ ^ 2 ≤ f (x k) - f xstar := by
  have hs : 1 < √Q := by
    have := Real.sq_sqrt (show 0 ≤ Q by linarith)
    nlinarith [Real.sqrt_nonneg Q]
  let q := (√Q - 1) / (√Q + 1)
  let a := (√Q + 1) / 2
  let b := (√Q - 1) / 2
  have hq₀ : 0 < q := div_pos (by linarith) (by linarith)
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq₀.le]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have haq : a * q = b := by
    dsimp [a, q, b]
    field_simp
  let v := geometricVec hq
  let c := x₀ + v
  let T := factor a b
  have hbounds := factor_bounds (show 0 ≤ b by dsimp [b]; linarith)
    (show a - b = 1 by dsimp [a, b]; ring)
  have hT : ‖T‖ ≤ √Q := by
    apply opNorm_le_bound _ (Real.sqrt_nonneg Q)
    intro z
    simpa only [show a + b = √Q by dsimp [a, b]; ring] using (hbounds z).2
  have hmin : energy μ T c c = 0 := by simp [energy]
  refine ⟨energy μ T c, ?_, strongConvexOn_energy hμ.le T (fun z => (hbounds z).1) c,
    lipschitzWith_gradient_energy hμ.le (by linarith) T hT c, c,
    fun h => geometricVec_ne_zero hq (add_eq_left.mp h), ?_, ?_⟩
  · exact contDiff_const.mul ((T.contDiff.comp (contDiff_id.sub contDiff_const)).norm_sq ℝ)
  · intro z
    rw [hmin, energy]
    positivity
  · intro x _ hspan k
    have hsupport (j : ℕ) : ∀ n, j ≤ n → (x j - x₀) n = 0 := by
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        intro n hn
        let K : Submodule ℝ H := LinearMap.ker (lp.evalₗ (fun _ : ℕ => ℝ) 2 n)
        change x j - x₀ ∈ K
        refine (Submodule.span_le.mpr ?_ : Submodule.span ℝ _ ≤ K) (hspan j)
        rintro _ ⟨i, hi, rfl⟩
        exact gradient_zero_of_tail hq haq μ (ih i hi) n (lt_of_lt_of_le hi hn)
    have hdist := geometric_tail_bound hq hq₀.le k (x k - x₀) (hsupport k)
    have hinitial : ‖x₀ - c‖ = ‖v‖ := by simp [c]
    have hdx : x k - x₀ - v = x k - c := sub_sub _ _ _
    change q ^ (2 * k) * ‖v‖ ^ 2 ≤ ‖x k - x₀ - v‖ ^ 2 at hdist
    rw [hdx] at hdist
    rw [hinitial, hmin, sub_zero]
    refine ⟨hdist, ?_⟩
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hdist.trans (pow_le_pow_left₀ (norm_nonneg _) (hbounds _).1 2)

end WantedExt.Analysis.Convex.FirstOrderLowerBoundWanted
