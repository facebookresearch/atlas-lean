/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The mean-field fixed-point map `m ↦ tanh (U m + h)`

For a binary (`±1`-valued) mean-field model with a symmetric coupling `U` and field `h` on a
finite index set `ι`, the stationarity equation of the quadratic mean-field free energy
`F(m) = ∑ i, -H(m i) - ⟪m, U m⟫ / 2 - ⟪h, m⟫`, with `H` the binary entropy of a `±1` variable of
mean `m i`, is `artanh m = U m + h` on the open cube `(-1, 1)^ι`. Its fixed-point form is
`m = tanh (U m + h)`, coordinatewise. The results below hold for any continuous linear `U`; for a
`U` that is not symmetric, the gradient equation of `F` involves `(U + Uᵀ) / 2` instead.

Main results:

* `dist_iterate_le_of_dist_le`, `dist_iterate_le_of_dist_le'`: **error of an approximate
  fixed-point iteration**. If `T` maps `C` into itself, `T⋆` is `q`-Lipschitz on `C` with
  fixed point `x̂ ∈ C`, and `dist (T x) (T⋆ x) ≤ ζ` on `C`, then the iterates of `T` from
  `x₀ ∈ C` satisfy `dist (T^[k] x₀) x̂ ≤ q ^ k dist x₀ x̂ + ζ (1 - q ^ k) / (1 - q)` for `q < 1`.
* `meanFieldMap`: the map `m ↦ tanh (U m + h)` on `EuclideanSpace ℝ ι`, for a continuous linear
  `U`. `abs_meanFieldMap_apply_lt_one`: its values lie in the open cube.
* `contractingWith_meanFieldMap`: **if `‖U‖ ≤ a < 1`, the mean-field map is a contraction** with
  constant `a`, since `tanh` is `1`-Lipschitz (`lipschitzWith_tanh`).
* `meanFieldMap_eq_self_iff`: `m` is a fixed point exactly when `m` lies in the open cube and
  `artanh m = U m + h`, which for symmetric `U` is the stationarity equation of `F`.
* `existsUnique_meanFieldMap_eq_self`: **for `‖U‖ ≤ a < 1` there is exactly one fixed point**,
  and it lies in the open cube.
* `dist_iterate_le_of_dist_le_meanFieldMap`: the error bound for an approximate iteration of the
  mean-field map on any set `C` that the approximation maps into itself.

The contraction argument needs neither the symmetry of `U` nor the free energy; symmetry is what
makes the fixed-point equation the gradient equation of `F`. The free energy, its gradient and
Hessian, and its minimizer are not formalized here.

Source: S. Mei and Y. Wu, *Deep networks as denoising algorithms: sample-efficient learning of
diffusion models in high-dimensional graphical models*, arXiv:2309.11420 (version 1), equation
(40), page 29 (the approximation-error recursion for the mean-field iteration). The general
metric-space form of `dist_iterate_le_of_dist_le` is a standard argument stated here
independently of the source's proof.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Variational

open Set Real Finset
open scoped NNReal

/-! ## Approximate fixed-point iteration -/

section Approximate

variable {α : Type*} [PseudoMetricSpace α]

/-- **Error of an approximate fixed-point iteration.** Let `T` map `C` into itself and let `T⋆`
be `q`-Lipschitz on `C` with a fixed point `x̂ ∈ C`. If `dist (T x) (T⋆ x) ≤ ζ` for every
`x ∈ C`, then for every `x₀ ∈ C` and `k`,
`dist (T^[k] x₀) x̂ ≤ q ^ k dist x₀ x̂ + ζ ∑_{j < k} q ^ j`.

`T⋆` need not map `C` into itself and `q` need not be below `1`. -/
theorem dist_iterate_le_of_dist_le {C : Set α} {T Tstar : α → α} {q : ℝ≥0} {ζ : ℝ}
    {x₀ xhat : α} (hT : MapsTo T C C) (hTstar : LipschitzOnWith q Tstar C)
    (hfix : Tstar xhat = xhat) (hxhat : xhat ∈ C) (hζ : ∀ x ∈ C, dist (T x) (Tstar x) ≤ ζ)
    (hx₀ : x₀ ∈ C) (k : ℕ) :
    dist (T^[k] x₀) xhat ≤ (q : ℝ) ^ k * dist x₀ xhat + ζ * ∑ j ∈ range k, (q : ℝ) ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : T^[k] x₀ ∈ C := hT.iterate k hx₀
    have step : dist (T^[k + 1] x₀) xhat ≤ ζ + q * dist (T^[k] x₀) xhat := by
      rw [Function.iterate_succ_apply']
      calc dist (T (T^[k] x₀)) xhat
          ≤ dist (T (T^[k] x₀)) (Tstar (T^[k] x₀)) + dist (Tstar (T^[k] x₀)) xhat :=
            dist_triangle _ _ _
        _ ≤ ζ + q * dist (T^[k] x₀) xhat := by
          gcongr
          · exact hζ _ hk
          · conv_lhs => rw [← hfix]
            exact hTstar.dist_le_mul _ hk _ hxhat
    calc dist (T^[k + 1] x₀) xhat ≤ ζ + q * dist (T^[k] x₀) xhat := step
      _ ≤ ζ + q * ((q : ℝ) ^ k * dist x₀ xhat + ζ * ∑ j ∈ range k, (q : ℝ) ^ j) := by
          gcongr
      _ = (q : ℝ) ^ (k + 1) * dist x₀ xhat + ζ * ∑ j ∈ range (k + 1), (q : ℝ) ^ j := by
          rw [Finset.sum_range_succ', pow_zero]
          simp_rw [pow_succ]
          rw [← Finset.sum_mul]
          ring

/-- **Error of an approximate fixed-point iteration, closed form.** Under the hypotheses of
`dist_iterate_le_of_dist_le` with `q < 1`,
`dist (T^[k] x₀) x̂ ≤ q ^ k dist x₀ x̂ + ζ (1 - q ^ k) / (1 - q)`. -/
theorem dist_iterate_le_of_dist_le' {C : Set α} {T Tstar : α → α} {q : ℝ≥0} {ζ : ℝ}
    {x₀ xhat : α} (hq : q < 1) (hT : MapsTo T C C) (hTstar : LipschitzOnWith q Tstar C)
    (hfix : Tstar xhat = xhat) (hxhat : xhat ∈ C) (hζ : ∀ x ∈ C, dist (T x) (Tstar x) ≤ ζ)
    (hx₀ : x₀ ∈ C) (k : ℕ) :
    dist (T^[k] x₀) xhat ≤ (q : ℝ) ^ k * dist x₀ xhat + ζ * (1 - (q : ℝ) ^ k) / (1 - q) := by
  have hq' : (q : ℝ) < 1 := by exact_mod_cast hq
  have h := dist_iterate_le_of_dist_le hT hTstar hfix hxhat hζ hx₀ k
  rw [geom_sum_eq hq'.ne] at h
  have e : ((q : ℝ) ^ k - 1) / ((q : ℝ) - 1) = (1 - (q : ℝ) ^ k) / (1 - q) := by
    rw [← neg_div_neg_eq]; ring_nf
  rw [e, ← mul_div_assoc] at h
  exact h

end Approximate

/-! ## The hyperbolic tangent is `1`-Lipschitz -/

private theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt tanh (1 / cosh x ^ 2) x := by
  have hc : cosh x ≠ 0 := (cosh_pos x).ne'
  have h := (hasDerivAt_sinh x).div (hasDerivAt_cosh x) hc
  have e : sinh / cosh = tanh := funext fun y => (tanh_eq_sinh_div_cosh y).symm
  rw [e] at h
  convert h using 1
  rw [div_eq_div_iff (pow_ne_zero 2 hc) (pow_ne_zero 2 hc)]
  nlinarith [cosh_sq x]

/-- **The hyperbolic tangent is 1-Lipschitz**: its derivative `1 / cosh² x` lies in `(0, 1]`. -/
theorem lipschitzWith_tanh : LipschitzWith 1 tanh := by
  refine lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_tanh x).differentiableAt)
    fun x => ?_
  rw [(hasDerivAt_tanh x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [div_le_one (by positivity)]
  nlinarith [one_le_cosh x]

/-! ## The mean-field map -/

variable {ι : Type*}

local notation "E" => EuclideanSpace ℝ ι

/-- **The mean-field fixed-point map** `m ↦ tanh (U m + h)`, coordinatewise, on `ℝ^ι` with the
Euclidean norm. Its fixed points are the solutions of `artanh m = U m + h` in the open cube
(`meanFieldMap_eq_self_iff`); for symmetric `U` this is the stationarity equation of the
quadratic binary mean-field free energy. -/
noncomputable def meanFieldMap (U : E →L[ℝ] E) (h : E) (m : E) : E :=
  WithLp.toLp 2 fun i => tanh ((U m + h) i)

@[simp]
theorem meanFieldMap_apply (U : E →L[ℝ] E) (h m : E) (i : ι) :
    meanFieldMap U h m i = tanh ((U m) i + h i) := rfl

/-- **The mean-field map takes values in the open cube** `(-1, 1)^ι`. -/
theorem abs_meanFieldMap_apply_lt_one (U : E →L[ℝ] E) (h m : E) (i : ι) :
    |meanFieldMap U h m i| < 1 :=
  abs_tanh_lt_one _

/-- **The mean-field map is a contraction for a coupling of norm below one**: if `‖U‖ ≤ a < 1`
for the operator norm of `U` on `ℝ^ι` with the Euclidean (`ℓ²`) norm, it is a contraction with
constant `a`. -/
theorem contractingWith_meanFieldMap [Fintype ι] {U : E →L[ℝ] E} (h : E) {a : ℝ≥0} (ha : a < 1)
    (hU : ‖U‖₊ ≤ a) : ContractingWith a (meanFieldMap U h) := by
  refine ⟨ha, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  calc √(∑ i, dist (meanFieldMap U h x i) (meanFieldMap U h y i) ^ 2)
      ≤ √(∑ i, dist ((U x + h) i) ((U y + h) i) ^ 2) := by
        gcongr with i
        simpa using lipschitzWith_tanh.dist_le_mul ((U x + h) i) ((U y + h) i)
    _ = dist (U x + h) (U y + h) := (EuclideanSpace.dist_eq _ _).symm
    _ = ‖U (x - y)‖ := by rw [dist_add_right, dist_eq_norm, map_sub]
    _ ≤ ‖U‖ * ‖x - y‖ := U.le_opNorm _
    _ ≤ a * ‖x - y‖ := by gcongr; exact_mod_cast hU
    _ = a * √(∑ i, dist (x i) (y i) ^ 2) := by
        rw [← dist_eq_norm, EuclideanSpace.dist_eq]

/-- **Fixed points of the mean-field map are the solutions of artanh m = U m + h**: `m` is a fixed
point exactly when it lies in the open cube and `artanh m = U m + h`. -/
theorem meanFieldMap_eq_self_iff (U : E →L[ℝ] E) (h m : E) :
    meanFieldMap U h m = m ↔
      (∀ i, m i ∈ Set.Ioo (-1) 1) ∧ ∀ i, artanh (m i) = (U m) i + h i := by
  constructor
  · intro hm
    have hi : ∀ i, meanFieldMap U h m i = m i := fun i => by rw [hm]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [← hi i]; exact abs_lt.mp (abs_meanFieldMap_apply_lt_one U h m i)
    · rw [← hi i, meanFieldMap_apply, artanh_tanh]
  · rintro ⟨hcube, heq⟩
    ext i
    rw [meanFieldMap_apply, ← heq i, tanh_artanh (hcube i)]

/-- **Existence and uniqueness of the mean-field fixed point.** If `‖U‖ ≤ a < 1`, the mean-field
map has exactly one fixed point; it lies in the open cube and solves `artanh m = U m + h`
(`meanFieldMap_eq_self_iff`). The proof is Banach's fixed-point theorem on the complete space
`ℝ^ι`, which the map sends into the open cube. -/
theorem existsUnique_meanFieldMap_eq_self [Fintype ι] {U : E →L[ℝ] E} (h : E) {a : ℝ≥0} (ha : a < 1)
    (hU : ‖U‖₊ ≤ a) : ∃! m : E, meanFieldMap U h m = m := by
  have hc := contractingWith_meanFieldMap h ha hU
  exact ⟨ContractingWith.fixedPoint _ hc, ContractingWith.fixedPoint_isFixedPt hc,
    fun m hm => ContractingWith.fixedPoint_unique hc hm⟩

/-- **Error of an approximate mean-field iteration.** Let `‖U‖ ≤ a < 1` and let `m` be the fixed
point of the mean-field map `T⋆ = meanFieldMap U h`. If `T` maps a set `C` containing `m` and
`x₀` into itself and `dist (T x) (T⋆ x) ≤ ζ` on `C`, then
`dist (T^[k] x₀) m ≤ a ^ k dist x₀ m + ζ (1 - a ^ k) / (1 - a)`. -/
theorem dist_iterate_le_of_dist_le_meanFieldMap [Fintype ι] {U : E →L[ℝ] E} {h : E} {a : ℝ≥0}
    (ha : a < 1) (hU : ‖U‖₊ ≤ a) {m : E} (hm : meanFieldMap U h m = m) {C : Set E}
    {T : E → E} {ζ : ℝ} {x₀ : E} (hT : MapsTo T C C) (hmC : m ∈ C)
    (hζ : ∀ x ∈ C, dist (T x) (meanFieldMap U h x) ≤ ζ) (hx₀ : x₀ ∈ C) (k : ℕ) :
    dist (T^[k] x₀) m ≤ (a : ℝ) ^ k * dist x₀ m + ζ * (1 - (a : ℝ) ^ k) / (1 - a) :=
  dist_iterate_le_of_dist_le' ha hT
    ((contractingWith_meanFieldMap h ha hU).toLipschitzWith.lipschitzOnWith) hm hmC hζ hx₀ k

end Cslib.MachineLearning.Variational
