/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Domains.Biology.Dynamics.PlanarStability
import MathlibExt.Analysis.PDE.SemilinearFlow.Instability
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Nicholson–Bailey host–parasitoid map

The state `(H, P)` records host and parasitoid populations. The growth factor is
`r`, the search parameter is `a`, and conversion is `c`. The map acts on the
real plane, whose product norm is the maximum of the two coordinate norms.
The positive quadrant is the biological domain.

The equations and Jacobian follow Ben Bolker, *2D nonlinear discrete-time
models* (2017), p. 1, where the model is attributed to S. P. Ellner and
J. Guckenheimer, *Dynamic Models in Biology* (2006). The model is named for
A. J. Nicholson and V. A. Bailey, *The balance of animal populations.
Part I* (1935). The nonlinear escape statement is a separate consequence.
-/

@[expose] public noncomputable section

open Function
open scoped ContDiff

namespace MathlibExt.Biology.Ecology.NicholsonBailey

/-- The positive quadrant `{x | 0 < x.1 ∧ 0 < x.2}`: host population `H = x.1` and parasitoid
population `P = x.2` both strictly above zero. -/
def positiveQuadrant : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2}

/-- One generation of Nicholson–Bailey dynamics, with host coordinate first: for a state
`x = (H, P)`, `step r a c x = (r H exp(-a P), c H (1 - exp(-a P)))`, where `r` is the host growth
factor, `a` the search parameter and `c` the conversion factor. The map is defined for all real
`r`, `a`, `c` and all states. -/
def step (r a c : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (r * x.1 * Real.exp (-(a * x.2)), c * x.1 * (1 - Real.exp (-(a * x.2))))

/-- The equilibrium formula
`positiveEquilibrium r a c = (r log r / ((r - 1) a c), log r / a)`.

It is defined for all real `r`, `a`, `c` with Lean's total conventions: `Real.log` is the natural
logarithm with `log 0 = 0` and `log x = log |x|` for `x < 0`, and division by zero returns `0`.
So when `r = 1`, `a = 0` or `c = 0` the host coordinate is `0`, and when `a = 0` the parasitoid
coordinate is `0`. In the regime `r > 1`, `a > 0`, `c > 0` it is the unique fixed point of
`step r a c` in the positive quadrant (`positiveEquilibrium_spec`,
`eq_positiveEquilibrium_of_isFixedPt`). -/
def positiveEquilibrium (r a c : ℝ) : ℝ × ℝ :=
  (r * Real.log r / ((r - 1) * a * c), Real.log r / a)

/-- The Jacobian matrix of `step r a c` at `x = (H, P)`, in the ordered host and parasitoid
coordinates: with `e = exp(-a P)`,
`jacobian r a c x = [[r e, -r a H e], [c (1 - e), a c H e]]` (rows are the host and parasitoid
components, columns the derivatives in `H` and `P`). It is defined for all real `r`, `a`, `c` and
all `x`, and is the derivative of `step r a c` at every point (`hasFDerivAt_step`). -/
def jacobian (r a c : ℝ) (x : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r * Real.exp (-(a * x.2)), -(r * a * x.1 * Real.exp (-(a * x.2)));
     c * (1 - Real.exp (-(a * x.2))), a * c * x.1 * Real.exp (-(a * x.2))]

/-- **Positivity is preserved.** For a growth factor `r > 0`, search parameter `a > 0` and
conversion `c > 0`, one generation maps the positive quadrant (both populations strictly positive)
into itself. -/
theorem mapsTo_step_positiveQuadrant {r a c : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hc : 0 < c) :
    Set.MapsTo (step r a c) positiveQuadrant positiveQuadrant := by
  intro x hx
  obtain ⟨hH, hP⟩ := hx
  have he : Real.exp (-(a * x.2)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos ha hP))
  exact ⟨mul_pos (mul_pos hr hH) (Real.exp_pos _),
    mul_pos (mul_pos hc hH) (sub_pos.mpr he)⟩

/-- **Positivity is preserved by all iterates.** For a growth factor `r > 0`, search parameter
`a > 0` and conversion `c > 0`, and every number of generations `n`, the `n`-th iterate of the map
sends the positive quadrant into itself. -/
theorem mapsTo_iterate_step_positiveQuadrant {r a c : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hc : 0 < c) (n : ℕ) :
    Set.MapsTo (step r a c)^[n] positiveQuadrant positiveQuadrant :=
  (mapsTo_step_positiveQuadrant hr ha hc).iterate n

/-- **The positive equilibrium.** For a growth factor `r > 1`, search parameter `a > 0` and
conversion `c > 0`, the point `positiveEquilibrium r a c = (r log r / ((r - 1) a c), log r / a)`
lies in the positive quadrant and is a fixed point of the map. -/
theorem positiveEquilibrium_spec {r a c : ℝ}
    (hr : 1 < r) (ha : 0 < a) (hc : 0 < c) :
    positiveEquilibrium r a c ∈ positiveQuadrant ∧
      IsFixedPt (step r a c) (positiveEquilibrium r a c) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have he : Real.exp (-(a * (positiveEquilibrium r a c).2)) = r⁻¹ := by
    simp only [positiveEquilibrium, mul_div_cancel₀ _ ha.ne']
    rw [Real.exp_neg, Real.exp_log hr0]
  refine ⟨⟨div_pos (mul_pos hr0 (Real.log_pos hr))
    (mul_pos (mul_pos (sub_pos.mpr hr) ha) hc),
    div_pos (Real.log_pos hr) ha⟩, ?_⟩
  apply Prod.ext <;> dsimp [step] <;> rw [he]
  · field_simp [hr0.ne']
  · dsimp [positiveEquilibrium]
    field_simp [hr0.ne', ha.ne', hc.ne', (sub_pos.mpr hr).ne']

/-- **Uniqueness of the positive equilibrium.** For a growth factor `r > 1`, search parameter
`a > 0` and conversion `c > 0`, every fixed point `x` of the map in the positive quadrant equals
`positiveEquilibrium r a c`. -/
theorem eq_positiveEquilibrium_of_isFixedPt {r a c : ℝ}
    (hr : 1 < r) (ha : 0 < a) (hc : 0 < c) {x : ℝ × ℝ}
    (hx : x ∈ positiveQuadrant) (hfix : IsFixedPt (step r a c) x) :
    x = positiveEquilibrium r a c := by
  obtain ⟨hH, hP⟩ := hx
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have h1 := congrArg Prod.fst hfix
  have h2 := congrArg Prod.snd hfix
  change r * x.1 * Real.exp (-(a * x.2)) = x.1 at h1
  change c * x.1 * (1 - Real.exp (-(a * x.2))) = x.2 at h2
  have he : Real.exp (-(a * x.2)) = r⁻¹ := by
    apply (mul_left_cancel₀ hr0.ne')
    have : r * Real.exp (-(a * x.2)) = 1 := by nlinarith
    simpa [hr0.ne'] using this
  have hp : x.2 = Real.log r / a := by
    have hlog := congrArg Real.log he
    rw [Real.log_exp, Real.log_inv] at hlog
    apply (eq_div_iff ha.ne').mpr
    nlinarith
  rw [he, hp] at h2
  apply Prod.ext
  · dsimp [positiveEquilibrium]
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (sub_pos.mpr hr).ne' ha.ne') hc.ne')).mpr
    have := h2
    field_simp [hr0.ne', ha.ne'] at this
    nlinarith
  · exact hp

/-- **No positive equilibrium for `r ≤ 1`.** For a growth factor `r` with `0 < r ≤ 1`, search
parameter `a > 0` and any conversion `c`, the map has no fixed point `x` in the positive quadrant.
-/
theorem not_isFixedPt_of_le_one {r a c : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (ha : 0 < a) {x : ℝ × ℝ}
    (hx : x ∈ positiveQuadrant) : ¬ IsFixedPt (step r a c) x := by
  obtain ⟨hH, hP⟩ := hx
  have he : Real.exp (-(a * x.2)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos ha hP))
  have hlt := mul_lt_mul_of_pos_left he (mul_pos hr hH)
  rw [mul_one] at hlt
  have hle : r * x.1 ≤ x.1 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 hH.le
  intro hfix
  exact (hlt.trans_le hle).ne (congrArg Prod.fst hfix)

/-- **The trivial equilibrium.** For all real parameters `r`, `a`, `c`, the origin (zero host and
parasitoid populations) is a fixed point of the map. No sign hypothesis is needed. -/
theorem isFixedPt_zero (r a c : ℝ) : IsFixedPt (step r a c) 0 := by
  simp [IsFixedPt, step]

/-- **Smoothness.** For all real parameters `r`, `a`, `c`, the map is `C^∞` on the whole real plane.
No sign hypothesis is needed. -/
theorem contDiff_step (r a c : ℝ) : ContDiff ℝ ∞ (step r a c) := by
  exact ((contDiff_const.mul contDiff_fst).mul
    ((contDiff_const.mul contDiff_snd).neg.exp)).prodMk
    ((contDiff_const.mul contDiff_fst).mul
      (contDiff_const.sub ((contDiff_const.mul contDiff_snd).neg.exp)))

/-- **The derivative.** For all real parameters `r`, `a`, `c` and every point `x` of the real plane,
the Fréchet derivative of the map at `x` is the linear map given, in the standard basis, by the
matrix `jacobian r a c x`. No sign hypothesis is needed. -/
theorem hasFDerivAt_step (r a c : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (step r a c)
      (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
        (jacobian r a c x)).toContinuousLinearMap x := by
  have he := ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).const_mul a).neg.exp
  have h := ((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).const_mul r |>.mul he).prodMk
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).const_mul c |>.mul
      ((hasFDerivAt_const (1 : ℝ) x).sub he))
  convert h using 1
  · rfl
  · unfold jacobian
    rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
    ext <;> simp <;> ring

/-- **The Jacobian at the positive equilibrium.** For a growth factor `r > 1`, search parameter
`a > 0` and conversion `c > 0`, the Jacobian at `positiveEquilibrium r a c` is
`[[1, -a H*], [c (1 - 1/r), log r / (r - 1)]]`, where `H*` is the host coordinate of the
equilibrium. -/
theorem jacobian_positiveEquilibrium {r a c : ℝ}
    (hr : 1 < r) (ha : 0 < a) (hc : 0 < c) :
    jacobian r a c (positiveEquilibrium r a c) =
      !![1, -(a * (positiveEquilibrium r a c).1);
         c * (1 - 1 / r), Real.log r / (r - 1)] := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have he : Real.exp (-(a * (positiveEquilibrium r a c).2)) = r⁻¹ := by
    simp only [positiveEquilibrium, mul_div_cancel₀ _ ha.ne']
    rw [Real.exp_neg, Real.exp_log hr0]
  simp only [jacobian, he]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [positiveEquilibrium] <;>
    field_simp [hr0.ne', ha.ne', hc.ne', (sub_pos.mpr hr).ne']

/-- **Trace at the positive equilibrium.** For a growth factor `r > 1`, search parameter `a > 0` and
conversion `c > 0`, the Jacobian at `positiveEquilibrium r a c` has trace `1 + log r / (r - 1)`. -/
theorem trace_jacobian_positiveEquilibrium {r a c : ℝ}
    (hr : 1 < r) (ha : 0 < a) (hc : 0 < c) :
    (jacobian r a c (positiveEquilibrium r a c)).trace =
      1 + Real.log r / (r - 1) := by
  rw [jacobian_positiveEquilibrium hr ha hc, Matrix.trace_fin_two]
  simp

/-- **Determinant at the positive equilibrium.** For a growth factor `r > 1`, search parameter
`a > 0` and conversion `c > 0`, the Jacobian at `positiveEquilibrium r a c` has determinant
`r log r / (r - 1)`. -/
theorem det_jacobian_positiveEquilibrium {r a c : ℝ}
    (hr : 1 < r) (ha : 0 < a) (hc : 0 < c) :
    (jacobian r a c (positiveEquilibrium r a c)).det =
      r * Real.log r / (r - 1) := by
  rw [jacobian_positiveEquilibrium hr ha hc, Matrix.det_fin_two]
  simp [positiveEquilibrium]
  field_simp [ha.ne', hc.ne', (lt_trans zero_lt_one hr).ne', (sub_pos.mpr hr).ne']
  ring

private theorem log_ratio_bounds {r : ℝ} (hr : 1 < r) :
    0 < Real.log r / (r - 1) ∧ Real.log r / (r - 1) < 1 ∧
      1 < r * Real.log r / (r - 1) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hl := Real.log_lt_sub_one_of_pos hr0 hr.ne'
  have hi := Real.log_lt_sub_one_of_pos (inv_pos.mpr hr0) (inv_ne_one.mpr hr.ne')
  rw [Real.log_inv] at hi
  have hi' := mul_lt_mul_of_pos_left hi hr0
  simp only [mul_sub, mul_neg, mul_inv_cancel₀ hr0.ne', mul_one] at hi'
  refine ⟨div_pos (Real.log_pos hr) (sub_pos.mpr hr), ?_, ?_⟩
  · exact (div_lt_one (sub_pos.mpr hr)).mpr hl
  · apply (lt_div_iff₀ (sub_pos.mpr hr)).mpr
    linarith

/-- **Spectrum at the positive equilibrium.** For a growth factor `r > 1`, search parameter `a > 0`
and conversion `c > 0`, the complex spectrum of the Jacobian at `positiveEquilibrium r a c` is a
pair `{z, z̄}` of nonreal conjugate eigenvalues (`0 < Im z`) of common modulus
`‖z‖ = ‖z̄‖ = √(r log r / (r - 1))`, and this modulus exceeds `1`. -/
theorem spectrum_jacobian_positiveEquilibrium {r a c : ℝ}
    (hr : 1 < r) (ha : 0 < a) (hc : 0 < c) :
    ∃ z : ℂ, 0 < z.im ∧
      spectrum ℂ
        ((jacobian r a c (positiveEquilibrium r a c)).map (algebraMap ℝ ℂ)) =
        {z, star z} ∧
      ‖z‖ = Real.sqrt (r * Real.log r / (r - 1)) ∧
      ‖star z‖ = ‖z‖ ∧ 1 < ‖z‖ := by
  obtain ⟨hu0, hu1, hΔ⟩ := log_ratio_bounds hr
  let τ := 1 + Real.log r / (r - 1)
  let Δ := r * Real.log r / (r - 1)
  have hd : τ ^ 2 < 4 * Δ := by
    have := mul_pos (sub_pos.mpr hu1) (show 0 < 3 + Real.log r / (r - 1) by linarith)
    dsimp [τ, Δ]
    nlinarith
  let s := Real.sqrt (4 * Δ - τ ^ 2) / 2
  let z : ℂ := ⟨τ / 2, s⟩
  have hs0 : 0 < s := div_pos (Real.sqrt_pos.mpr (by linarith)) (by norm_num)
  have hs : s ^ 2 = Δ - (τ / 2) ^ 2 := by
    have := Real.sq_sqrt (show 0 ≤ 4 * Δ - τ ^ 2 by linarith)
    dsimp [s]
    nlinarith
  have hz : MathlibExt.Biology.Dynamics.PlanarStability.IsCharRoot τ Δ z := by
    unfold MathlibExt.Biology.Dynamics.PlanarStability.IsCharRoot
    apply Complex.ext <;> simp [z, pow_two] <;> nlinarith
  have hstar : MathlibExt.Biology.Dynamics.PlanarStability.IsCharRoot τ Δ (star z) := by
    unfold MathlibExt.Biology.Dynamics.PlanarStability.IsCharRoot
    apply Complex.ext <;> simp [z, pow_two] <;> nlinarith
  have hn : ‖z‖ = Real.sqrt Δ := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    dsimp [z]
    nlinarith
  refine ⟨z, hs0, ?_, hn, norm_star z, ?_⟩
  · ext w
    rw [MathlibExt.Biology.Dynamics.PlanarStability.mem_spectrum_iff_isCharRoot,
      trace_jacobian_positiveEquilibrium hr ha hc,
      det_jacobian_positiveEquilibrium hr ha hc]
    change MathlibExt.Biology.Dynamics.PlanarStability.IsCharRoot τ Δ w ↔
      w ∈ ({z, star z} : Set ℂ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hw
      obtain ⟨h1, h2⟩ := hw.re_im
      have him := hw.im_ne_zero hd
      have hre : w.re = τ / 2 := by
        have := (mul_eq_zero.mp h2).resolve_left him
        linarith
      have hsq : (w.im - s) * (w.im + s) = 0 := by rw [hre] at h1; nlinarith
      rcases mul_eq_zero.mp hsq with h | h
      · left
        apply Complex.ext
        · exact hre
        · dsimp [z]; linarith
      · right
        apply Complex.ext
        · simpa [z] using hre
        · simp [z]; linarith
    · rintro (rfl | rfl)
      · exact hz
      · exact hstar
  · rw [hn]
    have := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) hΔ
    simpa using this

private theorem rotation_square (t s b k : ℝ) (hs : s ≠ 0)
    (h : b * k = -((1 - t) ^ 2 + s ^ 2)) :
    !![(1 - t) / s, b / s; k / s, (t - 1) / s] *
      !![(1 - t) / s, b / s; k / s, (t - 1) / s] =
      -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
    nlinarith
  · ring
  · ring
  · field_simp
    nlinarith

private theorem shifted_rotation_square (t s b k : ℝ) (hs : s ≠ 0)
    (h : b * k = -((1 - t) ^ 2 + s ^ 2)) :
    let B := s⁻¹ • (!![1, b; k, 2 * t - 1] - t • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    B * B = -1 := by
  dsimp
  have hform : s⁻¹ • (!![1, b; k, 2 * t - 1] - t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      !![(1 - t) / s, b / s; k / s, (t - 1) / s] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [div_eq_mul_inv] <;> ring
  rw [hform]
  exact rotation_square t s b k hs h

private def planeConjugacy (t s k : ℝ) (hs : s ≠ 0) (hk : k ≠ 0) :
    ℂ ≃L[ℝ] (ℝ × ℝ) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun w => (w.re + (1 - t) / s * w.im, k / s * w.im)
    invFun := fun y => ⟨y.1 - (1 - t) / k * y.2, s / k * y.2⟩
    left_inv := by
      intro w
      apply Complex.ext <;> dsimp <;> field_simp
      ring
    right_inv := by
      intro y
      apply Prod.ext <;> dsimp <;> field_simp
      ring
    map_add' := by
      intro w v
      apply Prod.ext <;> simp <;> ring
    map_smul' := by
      intro b w
      apply Prod.ext <;> simp <;> ring }

private theorem step_remainder (r a c : ℝ) (x : ℝ × ℝ) :
    ∃ ρ > 0, ∃ C ≥ 0, ∀ y : ℝ × ℝ, ‖y‖ ≤ ρ →
      ‖step r a c (x + y) - step r a c x -
        (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
          (jacobian r a c x)).toContinuousLinearMap y‖ ≤ C * ‖y‖ ^ 2 := by
  let e := Real.exp (-(a * x.2))
  let K := |x.1| * a ^ 2 + 2 * |a|
  refine ⟨1 / (|a| + 1), by positivity, (|r| + |c|) * e * K, by positivity, ?_⟩
  intro y hy
  have h1 : |y.1| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le y
  have h2 : |y.2| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le y
  let v := -(a * y.2)
  have hv : |v| ≤ 1 := by
    simp only [v, abs_neg, abs_mul]
    calc |a| * |y.2| ≤ |a| * ‖y‖ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ ≤ |a| * (1 / (|a| + 1)) := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
  have hv2 : v ^ 2 ≤ a ^ 2 * ‖y‖ ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg y.2) (norm_nonneg y)).mpr h2
    have h := mul_le_mul_of_nonneg_left this (sq_nonneg a)
    simpa [v, sq_abs, mul_pow] using h
  let d := x.1 * (Real.exp v - 1 - v) + y.1 * (Real.exp v - 1)
  have hd : |d| ≤ K * ‖y‖ ^ 2 := by
    calc |d| ≤ |x.1| * |Real.exp v - 1 - v| + |y.1| * |Real.exp v - 1| := by
          simpa only [abs_mul] using abs_add_le (x.1 * (Real.exp v - 1 - v))
            (y.1 * (Real.exp v - 1))
      _ ≤ |x.1| * (a ^ 2 * ‖y‖ ^ 2) + ‖y‖ * (2 * (|a| * ‖y‖)) := by
          gcongr
          · exact (Real.abs_exp_sub_one_sub_id_le hv).trans hv2
          · calc |Real.exp v - 1| ≤ 2 * |v| := Real.abs_exp_sub_one_le hv
              _ ≤ 2 * (|a| * ‖y‖) := by simp only [v, abs_neg, abs_mul]; gcongr
      _ = K * ‖y‖ ^ 2 := by dsimp [K]; ring
  have hform :
      step r a c (x + y) - step r a c x -
        (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
          (jacobian r a c x)).toContinuousLinearMap y = (r * e * d, -(c * e * d)) := by
    simp only [jacobian, Matrix.toLin_finTwoProd_toContinuousLinearMap]
    apply Prod.ext <;> simp [step, e, d, v, mul_add, Real.exp_add] <;> ring
  have he0 : 0 < e := Real.exp_pos _
  rw [hform, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  apply max_le
  · simp only [abs_mul, abs_of_pos he0 ]
    calc |r| * e * |d| ≤ |r| * e * (K * ‖y‖ ^ 2) := by gcongr
      _ = |r| * (e * K * ‖y‖ ^ 2) := by ring
      _ ≤ (|r| + |c|) * (e * K * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg c)) (by positivity)
      _ = _ := by ring
  · simp only [abs_neg, abs_mul, abs_of_pos he0]
    calc |c| * e * |d| ≤ |c| * e * (K * ‖y‖ ^ 2) := by gcongr
      _ = |c| * (e * K * ‖y‖ ^ 2) := by ring
      _ ≤ (|r| + |c|) * (e * K * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg r)) (by positivity)
      _ = _ := by ring

private theorem escape_conjugate (r a c : ℝ) (x : ℝ × ℝ) (hx : x ∈ positiveQuadrant)
    (hfix : IsFixedPt (step r a c) x) (z : ℂ) (hz : 1 < ‖z‖)
    (Q : ℂ ≃L[ℝ] (ℝ × ℝ))
    (hQ : ∀ w, (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      (jacobian r a c x)).toContinuousLinearMap (Q w) = Q (z * w)) :
    ∃ ε > 0, ∀ δ > 0, ∃ x₀ ∈ positiveQuadrant,
      ‖x₀ - x‖ < δ ∧ ∃ n : ℕ, ε ≤ ‖(step r a c)^[n] x₀ - x‖ := by
  let A := (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    (jacobian r a c x)).toContinuousLinearMap
  let L : ℂ →L[ℂ] ℂ := algebraMap ℂ (ℂ →L[ℂ] ℂ) z
  let G : ℂ → ℂ := fun w => Q.symm (step r a c (x + Q w) - x)
  have hL (w : ℂ) : L w = z * w := by simp [L, Algebra.algebraMap_eq_smul_one]
  obtain ⟨ρ, hρ, C, hC, hrem⟩ := step_remainder r a c x
  have hnormQ (w : ℂ) : ‖Q w‖ ≤ ‖Q.toContinuousLinearMap‖ * ‖w‖ :=
    Q.toContinuousLinearMap.le_opNorm w
  have hnormS (y : ℝ × ℝ) : ‖Q.symm y‖ ≤ ‖Q.symm.toContinuousLinearMap‖ * ‖y‖ :=
    Q.symm.toContinuousLinearMap.le_opNorm y
  have hG : ∀ w : ℂ, ‖w‖ ≤ ρ / (‖Q.toContinuousLinearMap‖ + 1) →
      ‖G (0 + w) - 0 - L w‖ ≤
        (‖Q.symm.toContinuousLinearMap‖ * C * ‖Q.toContinuousLinearMap‖ ^ 2) * ‖w‖ ^ (2 : ℝ) := by
    intro w hw
    have hball : ‖Q w‖ ≤ ρ := by
      calc ‖Q w‖ ≤ ‖Q.toContinuousLinearMap‖ * ‖w‖ := hnormQ w
        _ ≤ (‖Q.toContinuousLinearMap‖ + 1) * ‖w‖ := by gcongr; linarith
        _ ≤ ρ := (le_div_iff₀' (by positivity)).mp hw
    have hid : G w - L w = Q.symm (step r a c (x + Q w) - step r a c x - A (Q w)) := by
      rw [hfix, hQ]
      simp [G, map_sub, hL]
    simp only [zero_add, sub_zero, Real.rpow_two]
    rw [hid]
    calc _ ≤ ‖Q.symm.toContinuousLinearMap‖ *
        ‖step r a c (x + Q w) - step r a c x - A (Q w)‖ := hnormS _
      _ ≤ ‖Q.symm.toContinuousLinearMap‖ * (C * ‖Q w‖ ^ 2) := by
        gcongr
        exact hrem (Q w) hball
      _ ≤ ‖Q.symm.toContinuousLinearMap‖ * (C * (‖Q.toContinuousLinearMap‖ * ‖w‖) ^ 2) := by
        gcongr
        exact hnormQ w
      _ = _ := by ring
  have hrad : spectralRadius ℂ L = ‖z‖₊ := by
    rw [spectralRadius_eq_of_unital, spectrum.scalar_eq]
    simp
  obtain ⟨ε, hε, hescape⟩ :=
    MathlibExt.Analysis.PDE.SemilinearFlow.Instability.exists_escape_of_spectralRadius_eq
      (G := G) (x₀ := 0) (L := L) (ν := z) (v := (1 : ℂ))
      (by positivity : 0 < ρ / (‖Q.toContinuousLinearMap‖ + 1))
      (by positivity) (by norm_num : (1 : ℝ) < 2) hG
      one_ne_zero (by simp [hL]) hz hrad
  have hS0 : 0 < ‖Q.symm.toContinuousLinearMap‖ := Q.symm.norm_pos
  refine ⟨ε / ‖Q.symm.toContinuousLinearMap‖, div_pos hε hS0, ?_⟩
  intro δ hδ
  let b := min δ (min x.1 x.2)
  have hb : 0 < b := lt_min hδ (lt_min hx.1 hx.2)
  obtain ⟨w, hw, n, _, hn⟩ := hescape (b / (‖Q.toContinuousLinearMap‖ + 1)) (by positivity)
  simp only [sub_zero] at hw hn
  have hwQ : ‖Q w‖ < b := by
    calc ‖Q w‖ ≤ ‖Q.toContinuousLinearMap‖ * ‖w‖ := hnormQ w
      _ ≤ (‖Q.toContinuousLinearMap‖ + 1) * ‖w‖ := by gcongr; linarith
      _ < b := (lt_div_iff₀' (by positivity)).mp hw
  have hw1 : |(Q w).1| < x.1 :=
    (show |(Q w).1| ≤ ‖Q w‖ by simpa only [Real.norm_eq_abs] using norm_fst_le (Q w)).trans_lt
      (hwQ.trans_le ((min_le_right δ (min x.1 x.2)).trans (min_le_left x.1 x.2)))
  have hw2 : |(Q w).2| < x.2 :=
    (show |(Q w).2| ≤ ‖Q w‖ by simpa only [Real.norm_eq_abs] using norm_snd_le (Q w)).trans_lt
      (hwQ.trans_le ((min_le_right δ (min x.1 x.2)).trans (min_le_right x.1 x.2)))
  refine ⟨x + Q w, ⟨by dsimp; linarith [neg_abs_le (Q w).1],
    by dsimp; linarith [neg_abs_le (Q w).2]⟩, ?_, n, ?_⟩
  · simpa only [add_sub_cancel_left] using hwQ.trans_le (min_le_left δ (min x.1 x.2))
  · have hsem : Semiconj (fun w => x + Q w) G (step r a c) := by
      intro w
      simp [G]
    have hiter := hsem.iterate_right n w
    have hnorm : ε ≤ ‖Q.symm.toContinuousLinearMap‖ * ‖Q (G^[n] w)‖ := by
      calc ε ≤ ‖G^[n] w‖ := hn
        _ = ‖Q.symm (Q (G^[n] w))‖ := by rw [Q.symm_apply_apply]
        _ ≤ _ := hnormS _
    have hdist : (step r a c)^[n] (x + Q w) - x = Q (G^[n] w) := by
      rw [← hiter]
      simp
    rw [hdist]
    exact (div_le_iff₀ hS0).mpr (by simpa only [mul_comm] using hnorm)

/-- **Instability of the positive equilibrium.** For a growth factor `r > 1`, search parameter
`a > 0` and conversion `c > 0`, there is `ε > 0` such that for every `δ > 0` some initial state `x₀`
in the positive quadrant with `‖x₀ - positiveEquilibrium r a c‖ < δ` has a forward iterate
`(step r a c)^[n] x₀` at distance at least `ε` from the equilibrium (the norm on the plane is the
maximum of the coordinate norms). -/
theorem positiveEquilibrium_lyapunovUnstable {r a c : ℝ}
    (hr : 1 < r) (ha : 0 < a) (hc : 0 < c) :
    ∃ ε > 0, ∀ δ > 0, ∃ x₀ ∈ positiveQuadrant,
      ‖x₀ - positiveEquilibrium r a c‖ < δ ∧
      ∃ n : ℕ, ε ≤ ‖(step r a c)^[n] x₀ - positiveEquilibrium r a c‖ := by
  obtain ⟨z, him, hspec, _, _, hz⟩ := spectrum_jacobian_positiveEquilibrium hr ha hc
  have hzmem : z ∈ spectrum ℂ
      ((jacobian r a c (positiveEquilibrium r a c)).map (algebraMap ℝ ℂ)) := by
    rw [hspec]
    simp
  have hroot := (MathlibExt.Biology.Dynamics.PlanarStability.mem_spectrum_iff_isCharRoot
    _ z).mp hzmem
  rw [trace_jacobian_positiveEquilibrium hr ha hc,
    det_jacobian_positiveEquilibrium hr ha hc] at hroot
  obtain ⟨hroot1, hroot2⟩ := hroot.re_im
  have ht : 1 + Real.log r / (r - 1) = 2 * z.re := by
    have := (mul_eq_zero.mp hroot2).resolve_left him.ne'
    linarith
  let k := c * (1 - 1 / r)
  have hk : 0 < k := mul_pos hc (sub_pos.mpr ((div_lt_one (lt_trans zero_lt_one hr)).mpr hr))
  let Q := planeConjugacy z.re z.im k him.ne' hk.ne'
  obtain ⟨hx, hfix⟩ := positiveEquilibrium_spec hr ha hc
  apply escape_conjugate r a c (positiveEquilibrium r a c) hx hfix z hz Q
  intro w
  have hdet := det_jacobian_positiveEquilibrium hr ha hc
  rw [jacobian_positiveEquilibrium hr ha hc, Matrix.det_fin_two] at hdet
  dsimp at hdet
  have hentry : -(a * (positiveEquilibrium r a c).1) * k =
      -((1 - z.re) ^ 2 + z.im ^ 2) := by
    dsimp [k]
    nlinarith
  let B := z.im⁻¹ • (jacobian r a c (positiveEquilibrium r a c) -
    z.re • (1 : Matrix (Fin 2) (Fin 2) ℝ))
  have hB : B * B = -1 := by
    dsimp [B]
    rw [jacobian_positiveEquilibrium hr ha hc,
      show Real.log r / (r - 1) = 2 * z.re - 1 by linarith]
    exact shifted_rotation_square z.re z.im (-(a * (positiveEquilibrium r a c).1))
      k him.ne' hentry
  have hrel : -(a * (positiveEquilibrium r a c).1) * k =
      -((1 - z.re) ^ 2 + z.im ^ 2) := by
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hB
    simp only [jacobian_positiveEquilibrium hr ha hc, one_div, Fin.isValue,
      Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, smul_eq_mul,
      Fin.sum_univ_two, Matrix.one_apply_eq, mul_one, Matrix.cons_val_one, ne_eq,
      zero_ne_one, not_false_eq_true, Matrix.one_apply_ne, mul_zero, sub_zero, mul_neg,
      one_ne_zero, neg_mul, Matrix.neg_apply, B] at h00
    have h00' : ((1 - z.re) / z.im) ^ 2 +
        (-(a * (positiveEquilibrium r a c).1) / z.im) * (k / z.im) = -1 := by
      convert h00 using 1
      dsimp [k]
      ring
    generalize -(a * (positiveEquilibrium r a c).1) = b at *
    generalize k = q at *
    field_simp [him.ne'] at h00'
    nlinarith only [h00']
  rw [jacobian_positiveEquilibrium hr ha hc, Matrix.toLin_finTwoProd_toContinuousLinearMap]
  apply Prod.ext
  · simp [Q, planeConjugacy]
    field_simp [him.ne']
    linear_combination w.im * hrel
  · simp only [one_smul, one_div, planeConjugacy,
      LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk, ContinuousLinearMap.prod_apply, add_apply,
      ContinuousLinearMap.coe_fst', smul_apply, ContinuousLinearMap.coe_snd',
      smul_eq_mul, neg_mul, Complex.mul_re, Complex.mul_im, Q]
    rw [← one_div r]
    change k * (w.re + (1 - z.re) / z.im * w.im) +
      (Real.log r / (r - 1)) * (k / z.im * w.im) =
      k / z.im * (z.re * w.im + z.im * w.re)
    generalize hkdef : k = q at *
    generalize hudef : Real.log r / (r - 1) = u at *
    field_simp [him.ne']
    linear_combination w.im * ht

end MathlibExt.Biology.Ecology.NicholsonBailey
