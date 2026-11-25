/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Geometry/HopfUmlaufsatz.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `hopf_umlaufsatz`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest `manifests/problems/hopf_umlaufsatz.toml`,
rev 1, submitter Kim Morrison, status archived): the definitions `Plane`, `period`, `velocity`,
`det2`, `signedArea`, `IsPositiveSimpleClosedUnitSpeedCurve`, `IsTangentAngleLift`,
`signedCurvature` and `totalCurvature` and the statement of `hopf_umlaufsatz`, with the
docstrings and comments they had in the former wanted module
`WantedExt/Geometry/HopfUmlaufsatzWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.Geometry.HopfUmlaufsatzWanted` namespace. Mathematical statements are unchanged.
Later change (ATLAS, 2026): the `theorem_wanted` was proved and the declarations moved from
`WantedExt/Geometry/HopfUmlaufsatzWanted.lean` to this `MathlibExt` module with unchanged names,
statements and docstrings, and the imports of `Batteries.Util.ProofWanted` and of all of Mathlib
were replaced by narrower Mathlib imports.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`hopf_umlaufsatz`, the private lemmas it uses, the module documentation and the linter options.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.Homotopy.Lifting

/-!
# The Hopf Umlaufsatz (theorem of turning tangents)

`hopf_umlaufsatz`: a positively oriented simple closed unit-speed plane curve
has total signed curvature `2π`. Trusted helpers (`signedArea`, `signedCurvature`,
`totalCurvature`, `IsPositiveSimpleClosedUnitSpeedCurve`, `IsTangentAngleLift`,
…) are non-holes. Mathlib has no turning-tangents theorem.
Category-(b) candidate from §170 of the Knill survey.

## Main results

* `hopf_umlaufsatz`: let `r : ℝ → ℝ²` be continuously differentiable, `2π`-periodic, injective on
  `[0, 2π)`, of unit speed and of positive signed area, and let `α` be a continuously
  differentiable tangent angle of `r`, so that `r' = (cos α, sin α)`. Then
  `∫₀^{2π} α' = 2π`.

## Proof outline

Write the curve as `z : ℝ → ℂ`, so that `z' = exp (i α)`, and let `L = 2π`. Since `z'` is
`L`-periodic, `α (b + L) - α b` does not depend on `b`; call it `2πk`.

* **Hopf's secant map.** For a base point `b`, the direction of `z t - z s` on the triangle
  `b ≤ s ≤ t ≤ b + L`, extended by `z' s` on the diagonal and by `-z' b` at the corner
  `(b, b + L)`, is continuous; it is parametrized by the unit square and lifted to an angle by the
  homotopy lifting property of `Circle.exp`. Along the diagonal the lift is `α`. The two other
  edges carry antipodal directions, so they turn by the same amount, and that amount is `πk`:
  seen from any point of the curve, the rest of the curve turns by `πk`.
* **Winding numbers off the curve.** For `p` off the curve, let `z t₁` be a point of the curve
  closest to `p`. No point of the curve lies strictly between `p` and `z t₁`, so the directions of
  `z t - p` and `z t - z t₁` are never opposite, and the tangent `z' t₁` is orthogonal to
  `z t₁ - p`. Comparing the two angle functions shows that the angle of `z t - p` turns by
  `πk ± π` over a period. Far from the curve it does not turn at all, so `k = ±1`.
* **Area.** By Fubini's theorem and the identity `∫_{|p| < R} (x - p)⁻¹ dp = π x̄` for `|x| < R`
  (computed in polar coordinates with circle integrals), the integral over a disc containing the
  curve of the turning of the angle of `z t - p` is `π ∫₀^L Im (z̄ z') = 2π · signedArea`. The
  curve has measure zero, so if `k = -1` the turning `-π ± π` is nonpositive almost everywhere
  and the signed area is nonpositive. Hence `k = 1`, and `∫₀^L α' = α L - α 0 = 2π`.

The orientation argument avoids the Jordan curve theorem: simplicity enters only through the
secant map and the closest-point comparison.

## Implementation notes

The definitions and the statement keep the full names they had in the former wanted module, so
the namespace still reads `HopfUmlaufsatzWanted` and repeats `Geometry`; the `dupNamespace`
linter is turned off for these declarations only.

## References

* H. Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Math. 2 (1935).
  Listed as §170 in O. Knill, *Some Fundamental Theorems in Mathematics*. This is the source cited
  by problem `hopf_umlaufsatz` of the lean-eval benchmark (leanprover/lean-eval), from which the
  definitions and the statement are taken.
-/

@[expose] public section

namespace MathlibExt.Geometry.HopfUmlaufsatzWanted
namespace Geometry.HopfUmlaufsatz

set_option linter.dupNamespace false in
/-- **Euclidean plane for the Umlaufsatz.** The Euclidean plane is the space $\mathbb{R}^2$ of
pairs of real numbers with the Euclidean inner product and norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

set_option linter.dupNamespace false in
/-- **Parameter period for the Umlaufsatz.** The parameter period of the closed curves in the
Hopf Umlaufsatz is the real number $2\pi$. -/
noncomputable def period : ℝ := 2 * Real.pi

set_option linter.dupNamespace false in
/-- **Velocity of a plane curve.** For a curve $r : \mathbb{R} \to \mathbb{R}^2$ in the Euclidean
plane and $t \in \mathbb{R}$, the velocity of $r$ at $t$ is its derivative $r'(t) \in \mathbb{R}^2$,
taken to be $0$ where $r$ is not differentiable. -/
noncomputable def velocity (r : ℝ → Plane) (t : ℝ) : Plane := deriv r t

set_option linter.dupNamespace false in
/-- **Planar determinant for the Umlaufsatz.** For vectors $u = (u_0, u_1)$ and
$v = (v_0, v_1)$ in the Euclidean plane $\mathbb{R}^2$, $\det(u, v) = u_0 v_1 - u_1 v_0$, the
signed area of the parallelogram spanned by $u$ and $v$. -/
def det2 (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

set_option linter.dupNamespace false in
/-- **Signed area of a closed plane curve.** For a curve $r : \mathbb{R} \to \mathbb{R}^2$, the
signed area is $\frac{1}{2}\int_0^{2\pi} \det(r(t), r'(t))\,dt$, where $r'$ is the velocity of
$r$ and $\det(u, v) = u_0 v_1 - u_1 v_0$ (Green's normalization). Its sign fixes the orientation
convention. -/
noncomputable def signedArea (r : ℝ → Plane) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..period, det2 (r t) (velocity r t)

set_option linter.dupNamespace false in
/-- **Positively oriented simple closed unit-speed curve.** A curve
$r : \mathbb{R} \to \mathbb{R}^2$ in the Euclidean plane is a positively oriented simple closed
unit-speed curve when it is continuously differentiable, periodic with period $2\pi$, injective on
$[0, 2\pi)$, has velocity of norm $\lVert r'(t) \rVert = 1$ for every $t \in \mathbb{R}$, and has
positive signed area $\frac{1}{2}\int_0^{2\pi} \det(r(t), r'(t))\,dt > 0$, where
$\det(u, v) = u_0 v_1 - u_1 v_0$. -/
structure IsPositiveSimpleClosedUnitSpeedCurve (r : ℝ → Plane) : Prop where
  smooth : ContDiff ℝ 1 r
  periodic : Function.Periodic r period
  injective_on_period : Set.InjOn r (Set.Ico (0 : ℝ) period)
  unit_speed : ∀ t : ℝ, ‖velocity r t‖ = 1
  positive_orientation : 0 < signedArea r

set_option linter.dupNamespace false in
/-- **Tangent-angle lift.** For a curve $r : \mathbb{R} \to \mathbb{R}^2$ in the Euclidean plane,
a function $\alpha : \mathbb{R} \to \mathbb{R}$ is a tangent-angle lift of $r$ when $\alpha$ is
continuously differentiable and the velocity of $r$ satisfies
$r'(t) = (\cos \alpha(t), \sin \alpha(t))$ for every $t \in \mathbb{R}$. -/
structure IsTangentAngleLift (r : ℝ → Plane) (α : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ 1 α
  velocity_eq : ∀ t : ℝ,
    velocity r t = !₂[Real.cos (α t), Real.sin (α t)]

set_option linter.dupNamespace false in
/-- **Signed curvature.** For a function $\alpha : \mathbb{R} \to \mathbb{R}$ and
$t \in \mathbb{R}$, the signed curvature of $\alpha$ at $t$ is the derivative $\alpha'(t)$, taken
to be $0$ where $\alpha$ is not differentiable at $t$.

When $\alpha$ is a tangent-angle lift of a unit-speed plane curve, this is the signed curvature
of the curve at $t$. -/
noncomputable def signedCurvature (α : ℝ → ℝ) (t : ℝ) : ℝ := deriv α t

set_option linter.dupNamespace false in
/-- **Total signed curvature of a tangent-angle lift.** For a function
$\alpha : \mathbb{R} \to \mathbb{R}$, the total signed curvature is $\int_0^{2\pi} \alpha'(t)\,dt$,
the integral of the signed curvature $\alpha'$ over one parameter period $[0, 2\pi]$. -/
noncomputable def totalCurvature (α : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..period, signedCurvature α t

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real ComplexConjugate

section Proof

variable {z : ℝ → ℂ} {L : ℝ} {α : ℝ → ℝ}

/-! ### Angles -/

/-- A continuous function on `[a, b]` that never takes a value in `π + 2πℤ` stays in one band
`((2m - 1)π, (2m + 1)π)`. -/
private theorem band {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hne : ∀ x ∈ Icc a b, ∀ m : ℤ, f x ≠ (2 * m + 1) * π) :
    ∃ m : ℤ, ∀ x ∈ Icc a b, (2 * m - 1) * π < f x ∧ f x < (2 * m + 1) * π := by
  set m : ℤ := ⌊(f a + π) / (2 * π)⌋
  refine ⟨m, ?_⟩
  have hπ := Real.pi_pos
  have h1 : (m : ℝ) ≤ (f a + π) / (2 * π) := Int.floor_le _
  have h2 : (f a + π) / (2 * π) < m + 1 := Int.lt_floor_add_one _
  have hlo : (2 * m - 1) * π ≤ f a := by
    rw [le_div_iff₀ (by positivity)] at h1; nlinarith
  have hhi : f a < (2 * m + 1) * π := by
    rw [div_lt_iff₀ (by positivity)] at h2; nlinarith
  have hlo' : (2 * m - 1) * π < f a := by
    refine lt_of_le_of_ne hlo fun h => hne a ⟨le_rfl, hab⟩ (m - 1) ?_
    rw [← h]; push_cast; ring
  intro x hx
  have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
  constructor
  · by_contra h
    push Not at h
    obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc' hx.1 (hf.mono hsub) ⟨h, hlo'.le⟩
    exact hne y (hsub hy) (m - 1) (by rw [hfy]; push_cast; ring)
  · by_contra h
    push Not at h
    obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc hx.1 (hf.mono hsub) ⟨hhi.le, h⟩
    exact hne y (hsub hy) m hfy

private theorem circleExp_pi : Circle.exp π = -1 := by
  ext; simp [Circle.coe_exp, Complex.exp_pi_mul_I]

/-- `Circle.exp x = -1` exactly when `x ∈ π + 2πℤ`. -/
private theorem circleExp_eq_neg_one_iff {x : ℝ} :
    Circle.exp x = -1 ↔ ∃ m : ℤ, x = (2 * m + 1) * π := by
  rw [← circleExp_pi, Circle.exp_eq_exp]
  constructor <;> rintro ⟨m, hm⟩ <;> exact ⟨m, by rw [hm]; ring⟩

/-- If a continuous function on `[a, b]` never has `Circle.exp` equal to `-1`, its total change
is less than `2π` in absolute value. -/
private theorem abs_sub_lt_two_pi {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hne : ∀ x ∈ Icc a b, Circle.exp (f x) ≠ -1) : |f b - f a| < 2 * π := by
  obtain ⟨m, hm⟩ := band hab hf fun x hx m h => hne x hx (circleExp_eq_neg_one_iff.2 ⟨m, h⟩)
  have ha := hm a ⟨le_rfl, hab⟩
  have hb := hm b ⟨hab, le_rfl⟩
  rw [abs_lt]; constructor <;> nlinarith

/-- A continuous function starting at `0` whose `Circle.exp` never equals `-1` stays in
`(-π, π)`. -/
private theorem abs_lt_pi_of_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hne : ∀ x ∈ Icc a b, Circle.exp (f x) ≠ -1) (h0 : f a = 0) : |f b| < π := by
  obtain ⟨m, hm⟩ := band hab hf fun x hx m h => hne x hx (circleExp_eq_neg_one_iff.2 ⟨m, h⟩)
  have ha := hm a ⟨le_rfl, hab⟩
  have hb := hm b ⟨hab, le_rfl⟩
  rw [h0] at ha
  have hπ := Real.pi_pos
  have hm0 : m = 0 := by
    have h1 : (m : ℝ) < 1 / 2 := by nlinarith
    have h2 : (-1 / 2 : ℝ) < m := by nlinarith
    have : m < 1 := by exact_mod_cast (show (m : ℝ) < 1 by linarith)
    have : -1 < m := by exact_mod_cast (show (-1 : ℝ) < m by linarith)
    omega
  subst hm0
  rw [abs_lt]; constructor <;> push_cast at hb <;> linarith [hb.1, hb.2]

/-- An element of `2πℤ` of absolute value less than `2π` vanishes. -/
private theorem eq_zero_of_circleExp_eq_one {x : ℝ} (h : Circle.exp x = 1) (hx : |x| < 2 * π) :
    x = 0 := by
  rw [← Circle.exp_zero, Circle.exp_eq_exp] at h
  obtain ⟨m, hm⟩ := h
  rw [zero_add] at hm
  subst hm
  have hπ := Real.pi_pos
  rw [abs_lt] at hx
  have h1 : (m : ℝ) < 1 := by nlinarith
  have h2 : (-1 : ℝ) < m := by nlinarith
  have : m = 0 := by
    have : m < 1 := by exact_mod_cast h1
    have : -1 < m := by exact_mod_cast h2
    omega
  simp [this]

/-- An element of `π + 2πℤ` of absolute value less than `2π` is `π` or `-π`. -/
private theorem eq_pi_or_of_circleExp_eq_neg_one {x : ℝ} (h : Circle.exp x = -1)
    (hx : |x| < 2 * π) :
    x = π ∨ x = -π := by
  obtain ⟨m, hm⟩ := circleExp_eq_neg_one_iff.1 h
  subst hm
  have hπ := Real.pi_pos
  rw [abs_lt] at hx
  have h1 : (m : ℝ) < 1 / 2 := by nlinarith
  have h2 : (-3 / 2 : ℝ) < m := by nlinarith
  have : m = 0 ∨ m = -1 := by
    have : m < 1 := by exact_mod_cast (show (m : ℝ) < 1 by linarith)
    have : -2 < m := by exact_mod_cast (show (-2 : ℝ) < m by linarith)
    omega
  rcases this with rfl | rfl
  · left; simp
  · right; push_cast; ring

/-! ### Normalization to the circle -/

/-- The unit vector `w / ‖w‖` as an element of the circle (junk `1` at `0`). -/
private noncomputable def toCircle (w : ℂ) : Circle :=
  if hw : w = 0 then 1 else
    ⟨w / (‖w‖ : ℂ), by
      rw [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk, mem_sphere_zero_iff_norm,
        norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hw)]⟩

private theorem coe_toCircle {w : ℂ} (hw : w ≠ 0) : (toCircle w : ℂ) = w / (‖w‖ : ℂ) := by
  simp [toCircle, hw]

private theorem toCircle_smul {w : ℂ} {κ : ℝ} (hκ : 0 < κ) : toCircle (κ • w) = toCircle w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hκw : κ • w ≠ 0 := smul_ne_zero hκ.ne' hw
  ext
  have h1 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have h2 : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw)
  rw [coe_toCircle hκw, coe_toCircle hw, norm_smul, Real.norm_of_nonneg hκ.le, Complex.real_smul]
  push_cast
  field_simp

private theorem toCircle_neg {w : ℂ} (hw : w ≠ 0) : toCircle (-w) = -toCircle w := by
  ext
  rw [Circle.coe_neg, coe_toCircle (neg_ne_zero.2 hw), coe_toCircle hw, norm_neg, neg_div]

private theorem toCircle_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) : (toCircle w : ℂ) = w := by
  have : w ≠ 0 := by rintro rfl; simp at hw
  rw [coe_toCircle this, hw]; simp

private theorem continuousAt_toCircle {w : ℂ} (hw : w ≠ 0) : ContinuousAt toCircle w := by
  refine (Topology.IsInducing.subtypeVal.continuousAt_iff).2 ?_
  have h : ∀ᶠ v in 𝓝 w, v ≠ 0 := isOpen_ne.mem_nhds hw
  have hc : ContinuousAt (fun v : ℂ => v / (‖v‖ : ℂ)) w :=
    continuousAt_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt
      (by exact_mod_cast norm_ne_zero_iff.2 hw)
  refine hc.congr ?_
  filter_upwards [h] with v hv
  exact (coe_toCircle hv).symm

/-! ### Hopf's secant lift -/

private theorem periodic_deriv (hper : Function.Periodic z L) : Function.Periodic (deriv z) L := by
  intro t
  have : (fun s => z (s + L)) = z := funext hper
  rw [← deriv_comp_add_const, this]

private theorem ne_of_lt_period (hL : 0 < L) (hper : Function.Periodic z L)
    (hinj : InjOn z (Ico 0 L))
    {s t : ℝ} (h1 : 0 < t - s) (h2 : t - s < L) : z t ≠ z s := by
  intro h
  have hs := toIcoMod_mem_Ico hL 0 s
  have ht := toIcoMod_mem_Ico hL 0 t
  rw [zero_add] at hs ht
  have es : toIcoMod hL 0 s = s - toIcoDiv hL 0 s • L := by
    rw [← self_sub_toIcoMod]; ring
  have et : toIcoMod hL 0 t = t - toIcoDiv hL 0 t • L := by
    rw [← self_sub_toIcoMod]; ring
  have hzs : z (toIcoMod hL 0 s) = z s := by rw [es, hper.sub_zsmul_eq]
  have hzt : z (toIcoMod hL 0 t) = z t := by rw [et, hper.sub_zsmul_eq]
  have heq : toIcoMod hL 0 t = toIcoMod hL 0 s := hinj ht hs (by rw [hzs, hzt, h])
  have hdiff : t - s = ((toIcoDiv hL 0 t - toIcoDiv hL 0 s : ℤ) : ℝ) * L := by
    rw [es, et] at heq
    push_cast
    simp only [zsmul_eq_mul] at heq
    linarith
  set n : ℤ := toIcoDiv hL 0 t - toIcoDiv hL 0 s
  rw [hdiff] at h1 h2
  have hn1 : (0 : ℝ) < n := pos_of_mul_pos_left h1 hL.le
  have hn2 : (n : ℝ) < 1 := by nlinarith
  have : 0 < n := by exact_mod_cast hn1
  have : n < 1 := by exact_mod_cast hn2
  omega

/-- The slope `(z t - z s) / (t - s)` written as an average of the derivative, so that it is
jointly continuous and equals `z' s` on the diagonal. -/
private noncomputable def slopeFn (z : ℝ → ℂ) (s t : ℝ) : ℂ :=
  ∫ τ in (0 : ℝ)..1, deriv z (s + τ * (t - s))

private theorem continuous_slopeFn (hz' : Continuous (deriv z)) :
    Continuous fun p : ℝ × ℝ => slopeFn z p.1 p.2 := by
  unfold slopeFn
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : ℝ × ℝ) (τ : ℝ) => deriv z (p.1 + τ * (p.2 - p.1)))
    (hz'.comp (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.1 + q.2 * (q.1.2 - q.1.1)))
    0 1

private theorem slopeFn_self (s : ℝ) : slopeFn z s s = deriv z s := by simp [slopeFn]

private theorem sub_eq_smul_slopeFn (hz : Differentiable ℝ z) (hz' : Continuous (deriv z))
    (s t : ℝ) :
    z t - z s = (t - s) • slopeFn z s t := by
  rcases eq_or_ne t s with rfl | hts
  · simp
  have hc : t - s ≠ 0 := sub_ne_zero.mpr hts
  have h1 := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) (fun u => deriv z u) hc s
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at h1
  have h2 : ∫ u in s..t, deriv z u = z t - z s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (hz x).hasDerivAt)
      (hz'.intervalIntegrable _ _)
  unfold slopeFn
  have h3 : (fun τ => deriv z (s + τ * (t - s))) = fun τ => deriv z ((t - s) * τ + s) := by
    ext τ; ring_nf
  rw [h3, h1, h2, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- Hopf's secant vector on the square `[0,1]²`, a parametrization of the triangle
`b ≤ s ≤ t ≤ b + L` by `s = b + L a c`, `t = b + L a`: a positive multiple of `z t - z s` off the
diagonal and the corner, `z' s` on the diagonal and `-z' b` at the corner. -/
private noncomputable def secantVec (z : ℝ → ℂ) (L b a c : ℝ) : ℂ :=
  (1 - a * (1 - c)) • slopeFn z (b + L * a * c) (b + L * a) +
    (a * (1 - c)) • -slopeFn z (b + L * a) (b + L * a * c + L)

private theorem continuous_secantVec (hz' : Continuous (deriv z)) (L b : ℝ) :
    Continuous fun p : ℝ × ℝ => secantVec z L b p.1 p.2 := by
  have h := continuous_slopeFn hz'
  unfold secantVec
  have c1 : Continuous fun p : ℝ × ℝ => slopeFn z (b + L * p.1 * p.2) (b + L * p.1) :=
    h.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (b + L * p.1 * p.2, b + L * p.1))
  have c2 : Continuous fun p : ℝ × ℝ => slopeFn z (b + L * p.1) (b + L * p.1 * p.2 + L) :=
    h.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (b + L * p.1, b + L * p.1 * p.2 + L))
  exact ((continuous_const.sub (continuous_fst.mul (continuous_const.sub continuous_snd))).smul
    c1).add ((continuous_fst.mul (continuous_const.sub continuous_snd)).smul c2.neg)

private theorem secantVec_of_eq_zero {b a c : ℝ} (h : a * (1 - c) = 0) :
    secantVec z L b a c = deriv z (b + L * a * c) := by
  have ht : b + L * a = b + L * a * c := by linear_combination L * h
  simp only [secantVec, h, sub_zero, one_smul, zero_smul, add_zero]
  rw [ht, slopeFn_self]

private theorem secantVec_one_zero (b : ℝ) : secantVec z L b 1 0 = -deriv z (b + L) := by
  simp [secantVec, slopeFn_self]

private theorem secantVec_eq_smul (hz : Differentiable ℝ z) (hz' : Continuous (deriv z))
    (hper : Function.Periodic z L) (hL : 0 < L) {b a c : ℝ} (h0 : 0 < a * (1 - c))
    (h1 : a * (1 - c) < 1) :
    ∃ κ : ℝ, 0 < κ ∧ secantVec z L b a c = κ • (z (b + L * a) - z (b + L * a * c)) := by
  set θ := a * (1 - c) with hθ
  set s := b + L * a * c
  set t := b + L * a
  have hts : t - s = L * θ := by simp only [t, s, θ]; ring
  have hst : s + L - t = L * (1 - θ) := by simp only [t, s, θ]; ring
  have hpos1 : 0 < L * θ := mul_pos hL h0
  have hpos2 : 0 < L * (1 - θ) := mul_pos hL (by linarith)
  have e1 := sub_eq_smul_slopeFn hz hz' s t
  have e2 := sub_eq_smul_slopeFn hz hz' t (s + L)
  rw [hts] at e1
  rw [hst, hper s] at e2
  have f1 : slopeFn z s t = (L * θ)⁻¹ • (z t - z s) := by
    rw [e1, smul_smul, inv_mul_cancel₀ hpos1.ne', one_smul]
  have f2 : slopeFn z t (s + L) = (L * (1 - θ))⁻¹ • (z s - z t) := by
    rw [e2, smul_smul, inv_mul_cancel₀ hpos2.ne', one_smul]
  refine ⟨(1 - θ) * (L * θ)⁻¹ + θ * (L * (1 - θ))⁻¹, by positivity, ?_⟩
  simp only [secantVec]
  rw [f1, f2, ← hθ, ← neg_sub (z t) (z s)]
  simp only [smul_neg, neg_neg, smul_smul, add_smul]

/-- Hypotheses on the curve used throughout. -/
private structure CurveHyp (z : ℝ → ℂ) (L : ℝ) (α : ℝ → ℝ) : Prop where
  pos : 0 < L
  diff : Differentiable ℝ z
  cont_deriv : Continuous (deriv z)
  periodic : Function.Periodic z L
  inj : InjOn z (Ico 0 L)
  cont : Continuous α
  deriv_eq : ∀ t, deriv z t = (Circle.exp (α t) : ℂ)

private theorem CurveHyp.norm_deriv (h : CurveHyp z L α) (t : ℝ) : ‖deriv z t‖ = 1 := by
  rw [h.deriv_eq]; exact Circle.norm_coe _

private theorem CurveHyp.deriv_ne_zero (h : CurveHyp z L α) (t : ℝ) : deriv z t ≠ 0 := by
  intro h'; have := h.norm_deriv t; rw [h'] at this; simp at this

private theorem CurveHyp.toCircle_deriv (h : CurveHyp z L α) (t : ℝ) :
    toCircle (deriv z t) = Circle.exp (α t) := by
  ext; rw [toCircle_of_norm_eq_one (h.norm_deriv _), h.deriv_eq]

private theorem CurveHyp.secantVec_ne_zero (h : CurveHyp z L α) (b : ℝ) {a c : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) : secantVec z L b a c ≠ 0 := by
  have hθ0 : 0 ≤ a * (1 - c) := mul_nonneg ha.1 (by linarith [hc.2])
  have hθ1 : a * (1 - c) ≤ 1 := by nlinarith [ha.1, ha.2, hc.1, hc.2]
  rcases hθ0.eq_or_lt with h0 | h0
  · rw [secantVec_of_eq_zero h0.symm]
    exact h.deriv_ne_zero _
  rcases hθ1.eq_or_lt with h1 | h1
  · have ha1 : a = 1 := by nlinarith [ha.1, ha.2, hc.1, hc.2]
    subst ha1
    have hc0 : c = 0 := by linarith
    subst hc0
    rw [secantVec_one_zero]
    exact neg_ne_zero.2 (h.deriv_ne_zero _)
  obtain ⟨κ, hκ, he⟩ := secantVec_eq_smul h.diff h.cont_deriv h.periodic h.pos (b := b) h0 h1
  rw [he]
  refine smul_ne_zero hκ.ne' (sub_ne_zero.2 ?_)
  have := mul_pos h.pos h0
  exact ne_of_lt_period h.pos h.periodic h.inj (by nlinarith) (by nlinarith)

/-- **Hopf's secant lift.** Along the edge `s = b` of the triangle `b ≤ s ≤ t ≤ b + L`, the
secant direction from `z b` (from `z' b` to `-z' b`) has a continuous lift whose total change
is half the total change `α (b + L) - α b` of the tangent angle. -/
private theorem CurveHyp.exists_secant_lift (h : CurveHyp z L α) (b : ℝ) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧
      (∀ a ∈ Icc (0 : ℝ) 1, Circle.exp (φ a) = toCircle (secantVec z L b a 0)) ∧
      φ 1 - φ 0 = (α (b + L) - α b) / 2 := by
  let H : C(unitInterval × unitInterval, Circle) :=
    ⟨fun p => toCircle (secantVec z L b p.1 p.2), by
      have hc : Continuous fun p : unitInterval × unitInterval => secantVec z L b p.1 p.2 :=
        (continuous_secantVec h.cont_deriv L b).comp
          (continuous_subtype_val.prodMap continuous_subtype_val)
      refine continuous_iff_continuousAt.2 fun p => ?_
      exact (continuousAt_toCircle (h.secantVec_ne_zero b p.1.2 p.2.2)).comp
        (f := fun p : unitInterval × unitInterval => secantVec z L b p.1 p.2) hc.continuousAt⟩
  have hH : ∀ p, H p = toCircle (secantVec z L b p.1 p.2) := fun _ => rfl
  have H0 : ∀ c, H (0, c) = Circle.exp (ContinuousMap.const unitInterval (α b) c) := by
    intro c
    rw [hH]
    simp only [ContinuousMap.const_apply, Set.Icc.coe_zero]
    rw [secantVec_of_eq_zero (by simp), h.toCircle_deriv]
    simp
  set Θ := Circle.isCoveringMap_exp.liftHomotopy H (ContinuousMap.const _ (α b)) H0
  have hΘ : ∀ p, Circle.exp (Θ p) = H p := fun p =>
    congr_fun (Circle.isCoveringMap_exp.liftHomotopy_lifts H _ H0) p
  have hΘ0 : ∀ c, Θ (0, c) = α b := fun c =>
    Circle.isCoveringMap_exp.liftHomotopy_zero H _ H0 c
  have hdiag : ∀ a : unitInterval, Θ (a, 1) = α (b + L * a) := by
    have := Circle.isCoveringMap_exp.eq_of_comp_eq (A := unitInterval)
      (g₁ := fun a => Θ (a, 1)) (g₂ := fun a => α (b + L * a))
      (Θ.continuous.comp (continuous_id.prodMk continuous_const))
      (h.cont.comp (by fun_prop)) ?_ 0 ?_
    · exact fun a => congr_fun this a
    · ext1 a
      simp only [Function.comp_apply]
      rw [hΘ, hH]
      simp only [Set.Icc.coe_one]
      rw [secantVec_of_eq_zero (by simp), mul_one, h.toCircle_deriv]
    · simp [hΘ0]
  have hanti : ∀ c : unitInterval, H (1, c) = -H (c, 0) := by
    rintro ⟨c, hc0, hc1⟩
    rw [hH, hH]
    simp only [Set.Icc.coe_one, Set.Icc.coe_zero]
    rcases hc0.eq_or_lt with rfl | hc0'
    · rw [secantVec_one_zero, secantVec_of_eq_zero (by simp), toCircle_neg (h.deriv_ne_zero _),
        periodic_deriv h.periodic b]
      simp
    rcases hc1.eq_or_lt with rfl | hc1'
    · rw [secantVec_of_eq_zero (by simp), secantVec_one_zero, toCircle_neg (h.deriv_ne_zero _),
        neg_neg]
      simp
    have hθ1 : 0 < (1 : ℝ) * (1 - c) := by linarith
    have hθ1' : (1 : ℝ) * (1 - c) < 1 := by linarith
    have hθ2 : 0 < c * (1 - 0) := by linarith
    have hθ2' : c * (1 - 0) < 1 := by linarith
    obtain ⟨κ₁, hκ₁, e₁⟩ := secantVec_eq_smul h.diff h.cont_deriv h.periodic h.pos (b := b) hθ1 hθ1'
    obtain ⟨κ₂, hκ₂, e₂⟩ := secantVec_eq_smul h.diff h.cont_deriv h.periodic h.pos (b := b) hθ2 hθ2'
    have hv : z (b + L * c) - z b ≠ 0 := by
      refine sub_ne_zero.2 (ne_of_lt_period h.pos h.periodic h.inj ?_ ?_)
      · have := mul_pos h.pos hc0'; linarith
      · have := mul_lt_mul_of_pos_left hc1' h.pos; linarith
    rw [e₁, e₂]
    rw [show z (b + L * 1) - z (b + L * 1 * c) = -(z (b + L * c) - z b) by
      simp only [mul_one]; rw [h.periodic b]; ring]
    rw [show b + L * c * 0 = b by ring, smul_neg, toCircle_neg (smul_ne_zero hκ₁.ne' hv),
      toCircle_smul hκ₁, toCircle_smul hκ₂]
  set κ := Θ (1, 0) - Θ (0, 0) with hκ
  have hκexp : Circle.exp κ = -1 := by
    rw [hκ, Circle.exp_sub, hΘ, hΘ, hanti 0, neg_div, div_self']
  have hedge : ∀ c : unitInterval, Θ (1, c) = Θ (c, 0) + κ := by
    have := Circle.isCoveringMap_exp.eq_of_comp_eq (A := unitInterval)
      (g₁ := fun c => Θ (1, c)) (g₂ := fun c => Θ (c, 0) + κ)
      (Θ.continuous.comp (continuous_const.prodMk continuous_id))
      ((Θ.continuous.comp (continuous_id.prodMk continuous_const)).add continuous_const) ?_ 0 ?_
    · exact fun c => congr_fun this c
    · ext1 c
      simp only [Function.comp_apply]
      rw [Circle.exp_add, hΘ, hΘ, hκexp, hanti c, mul_neg_one]
    · simp [κ]
  have h11 := hedge 1
  rw [hdiag 1] at h11
  refine ⟨fun a => Θ (Set.projIcc 0 1 zero_le_one a, 0), ?_, ?_, ?_⟩
  · exact Θ.continuous.comp (continuous_projIcc.prodMk continuous_const)
  · intro a ha
    simp only
    rw [Set.projIcc_of_mem _ ha, hΘ, hH]
    rfl
  · have e0 : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) := by
      rw [Set.projIcc_left]; rfl
    have e1 : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) := by
      rw [Set.projIcc_right]; rfl
    simp only [e0, e1]
    have := hΘ0 0
    simp only [Set.Icc.coe_one, mul_one] at h11
    rw [← hκ]
    linarith

/-! ### Winding numbers off the curve -/

private theorem toCircle_eq_exp_arg {w : ℂ} (hw : w ≠ 0) : toCircle w = Circle.exp (arg w) := by
  ext
  rw [coe_toCircle hw, Circle.coe_exp]
  have h := Complex.norm_mul_exp_arg_mul_I w
  have hn : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw
  rw [div_eq_iff hn, mul_comm, h]

private theorem toCircle_mul {w : ℂ} (hw : w ≠ 0) (u : Circle) :
    toCircle (w * u) = toCircle w * u := by
  have hwu : w * (u : ℂ) ≠ 0 := mul_ne_zero hw (by
    intro h; have := Circle.norm_coe u; rw [h] at this; simp at this)
  ext
  rw [Circle.coe_mul, coe_toCircle hwu, coe_toCircle hw, norm_mul, Circle.norm_coe, mul_one]
  ring

private theorem exp_logInt {p : ℂ} (hz : Differentiable ℝ z) (hz' : Continuous (deriv z))
    (hp : ∀ t, z t ≠ p) (b t : ℝ) :
    z t - p = (z b - p) * Complex.exp (∫ τ in b..t, deriv z τ / (z τ - p)) := by
  set F := fun t => ∫ τ in b..t, deriv z τ / (z τ - p) with hFdef
  have hcont : Continuous fun τ => deriv z τ / (z τ - p) :=
    hz'.div (hz.continuous.sub continuous_const) (fun τ => sub_ne_zero.2 (hp τ))
  have hF : ∀ t, HasDerivAt F (deriv z t / (z t - p)) t := fun t =>
    (hcont.integral_hasStrictDerivAt b t).hasDerivAt
  set g := fun t => (z t - p) * Complex.exp (-F t) with hgdef
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h1 : HasDerivAt (fun t => z t - p) (deriv z t) t := ((hz t).hasDerivAt).sub_const p
    have h2 := ((hF t).neg).cexp
    convert h1.mul h2 using 1
    have : z t - p ≠ 0 := sub_ne_zero.2 (hp t)
    field_simp
    ring
  have hconst : g t = g b :=
    is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t b
  have hgb : g b = z b - p := by simp [g, F]
  rw [hgb] at hconst
  calc z t - p = (z t - p) * Complex.exp (-F t) * Complex.exp (F t) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = (z b - p) * Complex.exp (F t) := by rw [show (z t - p) * Complex.exp (-F t) = g t from rfl,
        hconst]

/-- A continuous angle function of `z t - p`, based at `b`. -/
private noncomputable def angleFn (z : ℝ → ℂ) (p : ℂ) (b t : ℝ) : ℝ :=
  arg (z b - p) + (∫ τ in b..t, deriv z τ / (z τ - p)).im

private theorem continuous_angleFn {p : ℂ} (hz : Differentiable ℝ z) (hz' : Continuous (deriv z))
    (hp : ∀ t, z t ≠ p) (b : ℝ) : Continuous (angleFn z p b) := by
  have hcont : Continuous fun τ => deriv z τ / (z τ - p) :=
    hz'.div (hz.continuous.sub continuous_const) (fun τ => sub_ne_zero.2 (hp τ))
  unfold angleFn
  exact continuous_const.add (Complex.continuous_im.comp
    (continuous_iff_continuousAt.2 fun t =>
      (hcont.integral_hasStrictDerivAt b t).hasDerivAt.continuousAt))

private theorem circleExp_angleFn {p : ℂ} (hz : Differentiable ℝ z) (hz' : Continuous (deriv z))
    (hp : ∀ t, z t ≠ p) (b t : ℝ) : Circle.exp (angleFn z p b t) = toCircle (z t - p) := by
  set F := ∫ τ in b..t, deriv z τ / (z τ - p)
  have e := exp_logInt hz hz' hp b t
  have hb : z b - p ≠ 0 := sub_ne_zero.2 (hp b)
  have hF : Complex.exp F = (Real.exp F.re : ℝ) • (Circle.exp F.im : ℂ) := by
    rw [Circle.coe_exp, Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    exact (Complex.re_add_im F).symm
  rw [e, hF, mul_smul_comm, toCircle_smul (Real.exp_pos _), toCircle_mul hb, toCircle_eq_exp_arg hb,
    ← Circle.exp_add]
  rfl

private theorem CurveHyp.exists_closest (h : CurveHyp z L α) (p : ℂ) :
    ∃ t₁, ∀ t, ‖z t₁ - p‖ ≤ ‖z t - p‖ := by
  obtain ⟨t₁, -, ht₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_isMinOn
    (nonempty_Icc.2 h.pos.le) (f := fun t => ‖z t - p‖)
    ((h.diff.continuous.sub continuous_const).norm.continuousOn)
  refine ⟨t₁, fun t => ?_⟩
  have hm := toIcoMod_mem_Ico h.pos 0 t
  rw [zero_add] at hm
  have e : toIcoMod h.pos 0 t = t - toIcoDiv h.pos 0 t • L := by rw [← self_sub_toIcoMod]; ring
  have := ht₁ (Ico_subset_Icc_self hm)
  simp only [mem_ofPred_eq] at this
  rw [e, h.periodic.sub_zsmul_eq] at this
  exact this

private theorem CurveHyp.re_eq_zero_of_closest (h : CurveHyp z L α) {p : ℂ} {t₁ : ℝ}
    (ht₁ : ∀ t, ‖z t₁ - p‖ ≤ ‖z t - p‖) : (deriv z t₁ * conj (z t₁ - p)).re = 0 := by
  have hd : HasDerivAt (fun t => ‖z t - p‖ ^ 2) (2 * inner ℝ (z t₁ - p) (deriv z t₁)) t₁ :=
    (((h.diff t₁).hasDerivAt).sub_const p).norm_sq
  have hmin : IsLocalMin (fun t => ‖z t - p‖ ^ 2) t₁ :=
    Filter.Eventually.of_forall fun t => pow_le_pow_left₀ (norm_nonneg _) (ht₁ t) 2
  have := hmin.hasDerivAt_eq_zero hd
  rw [Complex.inner] at this
  linarith

private theorem CurveHyp.alpha_add_period (h : CurveHyp z L α) (t : ℝ) :
    α (t + L) - α t = α L - α 0 := by
  have e : ∀ s, Circle.exp (α (s + L)) = Circle.exp (α s) := fun s => by
    ext; rw [← h.deriv_eq, ← h.deriv_eq, periodic_deriv h.periodic s]
  have := Circle.isCoveringMap_exp.eq_of_comp_eq (A := ℝ) (g₁ := fun t => α (t + L) - α t)
    (g₂ := fun _ => α L - α 0) ((h.cont.comp (continuous_id.add continuous_const)).sub h.cont)
    continuous_const ?_ 0 (by simp)
  · exact congr_fun this t
  · ext1 t
    simp only [Function.comp_apply, Circle.exp_sub]
    rw [e t, show L = 0 + L by ring, e 0, div_self', div_self']

private theorem CurveHyp.periodic_integrand (h : CurveHyp z L α) (p : ℂ) :
    Function.Periodic (fun t => deriv z t / (z t - p)) L := fun t => by
  simp only [periodic_deriv h.periodic t, h.periodic t]

/-- **The winding sweep off the curve.** For a point `p` off the curve, the total change of the
angle of `z t - p` over a period is `(α L - α 0) / 2 ± π`: compare with the secant directions
from the point of the curve closest to `p`. -/
private theorem CurveHyp.sweep_eq (h : CurveHyp z L α) {p : ℂ} (hp : ∀ t, z t ≠ p) :
    ∃ σ : ℝ, (σ = π ∨ σ = -π) ∧
      (∫ t in (0 : ℝ)..L, deriv z t / (z t - p)).im = (α L - α 0) / 2 + σ := by
  obtain ⟨t₁, ht₁⟩ := h.exists_closest p
  set q := z t₁ with hq
  have hqp : q - p ≠ 0 := sub_ne_zero.2 (hp t₁)
  have hδ : 0 < ‖q - p‖ := norm_pos_iff.2 hqp
  have horth := h.re_eq_zero_of_closest ht₁
  rw [← hq] at horth
  obtain ⟨φv, hφv_cont, hφv, hφv_diff⟩ := h.exists_secant_lift t₁
  set φu : ℝ → ℝ := fun a => angleFn z p t₁ (t₁ + L * a) with hφu
  have hφu_cont : Continuous φu :=
    (continuous_angleFn h.diff h.cont_deriv hp t₁).comp (by fun_prop)
  set d : ℝ → ℝ := fun a => φu a - φv a with hd
  have hd_cont : Continuous d := hφu_cont.sub hφv_cont
  have hd_exp : ∀ a ∈ Icc (0 : ℝ) 1, Circle.exp (d a) =
      toCircle (z (t₁ + L * a) - p) / toCircle (secantVec z L t₁ a 0) := by
    intro a ha
    simp only [d, φu, Circle.exp_sub, hφv a ha, circleExp_angleFn h.diff h.cont_deriv hp]
  have hv0 : toCircle (secantVec z L t₁ 0 0) = toCircle (deriv z t₁) := by
    rw [secantVec_of_eq_zero (by simp)]; simp
  have hv1 : toCircle (secantVec z L t₁ 1 0) = -toCircle (deriv z t₁) := by
    rw [secantVec_one_zero, periodic_deriv h.periodic t₁, toCircle_neg (h.deriv_ne_zero _)]
  have hu1 : z (t₁ + L * 1) = q := by rw [mul_one, h.periodic t₁]
  have hu0 : z (t₁ + L * 0) = q := by rw [mul_zero, add_zero]
  have hd' : (deriv z t₁ : ℂ) = (toCircle (deriv z t₁) : ℂ) :=
    (toCircle_of_norm_eq_one (h.norm_deriv t₁)).symm
  have hne : ∀ a ∈ Icc (0 : ℝ) 1, Circle.exp (d a) ≠ -1 := by
    intro a ha he
    rw [hd_exp a ha, div_eq_iff_eq_mul, neg_one_mul] at he
    rcases ha.1.eq_or_lt with rfl | ha0
    · -- a = 0: the tangent at the closest point is orthogonal to `q - p`
      rw [hu0, hv0] at he
      have hc := congrArg (fun u : Circle => (u : ℂ)) he
      simp only [Circle.coe_neg, coe_toCircle hqp] at hc
      rw [← hd'] at hc
      have hn : ((‖q - p‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
      have hz1 : deriv z t₁ = -((q - p) / ((‖q - p‖ : ℝ) : ℂ)) := by rw [hc, neg_neg]
      have : deriv z t₁ * conj (q - p) = -((‖q - p‖ : ℝ) : ℂ) := by
        rw [hz1, neg_mul, div_mul_eq_mul_div, Complex.mul_conj', pow_two, mul_div_assoc,
          div_self hn, mul_one]
      rw [this, Complex.neg_re, Complex.ofReal_re] at horth
      linarith
    rcases ha.2.eq_or_lt with rfl | ha1
    · -- a = 1
      rw [hu1, hv1, neg_neg] at he
      have hc := congrArg (fun u : Circle => (u : ℂ)) he
      simp only [coe_toCircle hqp] at hc
      rw [← hd'] at hc
      have hn : ((‖q - p‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
      have : deriv z t₁ * conj (q - p) = ((‖q - p‖ : ℝ) : ℂ) := by
        rw [← hc, div_mul_eq_mul_div, Complex.mul_conj', pow_two, mul_div_assoc, div_self hn,
          mul_one]
      rw [this, Complex.ofReal_re] at horth
      linarith
    · -- 0 < a < 1: the point `y` would lie strictly between `p` and `q`
      have hθ0 : 0 < a * (1 - 0) := by linarith
      have hθ1 : a * (1 - 0) < 1 := by linarith
      obtain ⟨κ, hκ, eκ⟩ :=
        secantVec_eq_smul h.diff h.cont_deriv h.periodic h.pos (b := t₁) hθ0 hθ1
      set y := z (t₁ + L * a) with hy
      rw [eκ, show t₁ + L * a * 0 = t₁ by ring, ← hq] at he
      have hyq : y - q ≠ 0 := by
        refine sub_ne_zero.2 (ne_of_lt_period h.pos h.periodic h.inj ?_ ?_)
        · have := mul_pos h.pos ha0; linarith
        · have := mul_lt_mul_of_pos_left ha1 h.pos; linarith
      have hyp : y - p ≠ 0 := sub_ne_zero.2 (hp _)
      rw [toCircle_smul hκ] at he
      have hc := congrArg (fun u : Circle => (u : ℂ)) he
      simp only [Circle.coe_neg, coe_toCircle hyq, coe_toCircle hyp] at hc
      set A := ‖y - p‖ with hA
      set B := ‖y - q‖ with hB
      have hApos : 0 < A := norm_pos_iff.2 hyp
      have hBpos : 0 < B := norm_pos_iff.2 hyq
      have hAc : ((A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hApos.ne'
      have hBc : ((B : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hBpos.ne'
      have key : (y - p) * ((A + B : ℝ) : ℂ) = (q - p) * (A : ℂ) := by
        field_simp at hc
        push_cast
        linear_combination hc
      have hnorm := congrArg norm key
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg
        (by positivity), Real.norm_of_nonneg hApos.le, ← hA] at hnorm
      have hAB : A + B = ‖q - p‖ := by
        have := mul_left_cancel₀ hApos.ne' (hnorm.trans (mul_comm _ _))
        linarith
      have hmin := ht₁ (t₁ + L * a)
      rw [← hy, ← hA] at hmin
      linarith
  have hlt := abs_sub_lt_two_pi zero_le_one hd_cont.continuousOn hne
  have hexp : Circle.exp (d 1 - d 0) = -1 := by
    rw [Circle.exp_sub, hd_exp 1 ⟨zero_le_one, le_rfl⟩, hd_exp 0 ⟨le_rfl, zero_le_one⟩, hu1, hu0,
      hv1, hv0, div_neg, neg_div, div_self']
  obtain hσ := eq_pi_or_of_circleExp_eq_neg_one hexp hlt
  refine ⟨d 1 - d 0, hσ, ?_⟩
  have hsweep : (∫ t in (0 : ℝ)..L, deriv z t / (z t - p)).im = φu 1 - φu 0 := by
    simp only [φu, angleFn, mul_one, mul_zero, add_zero, intervalIntegral.integral_same,
      Complex.zero_im, add_sub_cancel_left]
    rw [(h.periodic_integrand p).intervalIntegral_add_eq t₁ 0, zero_add]
  have hα := h.alpha_add_period t₁
  rw [hsweep]
  simp only [d] at hφv_diff ⊢
  linarith

/-- Far from the curve, the angle of `z t - p` stays in a half-plane, so its total change over a
period vanishes. -/
private theorem CurveHyp.sweep_eq_zero_of_far (h : CurveHyp z L α) {p : ℂ} (hp : ∀ t, ‖z t‖ < ‖p‖) :
    (∫ t in (0 : ℝ)..L, deriv z t / (z t - p)).im = 0 := by
  have hp' : ∀ t, z t ≠ p := fun t he => by
    have := hp t; rw [he] at this; exact lt_irrefl _ this
  set f : ℝ → ℝ := fun t => angleFn z p 0 t - angleFn z p 0 0 with hf
  have hf0 : f 0 = 0 := sub_self _
  have hfc : Continuous f :=
    (continuous_angleFn h.diff h.cont_deriv hp' 0).sub continuous_const
  have hpos : ∀ t, 0 < ((z t - p) * conj (-p)).re := by
    intro t
    have h1 : ((z t - p) * conj (-p)).re = ‖p‖ ^ 2 - (z t * conj p).re := by
      rw [map_neg, mul_neg, sub_mul, Complex.mul_conj']
      simp [← Complex.ofReal_pow]
    have h2 : (z t * conj p).re ≤ ‖z t‖ * ‖p‖ := by
      have := Complex.re_le_norm (z t * conj p)
      rwa [norm_mul, Complex.norm_conj] at this
    have h3 : ‖z t‖ * ‖p‖ < ‖p‖ ^ 2 := by
      have := hp t
      have hp0 : 0 < ‖p‖ := lt_of_le_of_lt (norm_nonneg _) this
      nlinarith
    linarith
  have hne : ∀ t ∈ Icc 0 L, Circle.exp (f t) ≠ -1 := by
    intro t _ he
    rw [hf, Circle.exp_sub, circleExp_angleFn h.diff h.cont_deriv hp',
      circleExp_angleFn h.diff h.cont_deriv hp', div_eq_iff_eq_mul, neg_one_mul] at he
    have hc := congrArg (fun u : Circle => (u : ℂ)) he
    have ht : z t - p ≠ 0 := sub_ne_zero.2 (hp' t)
    have h0 : z 0 - p ≠ 0 := sub_ne_zero.2 (hp' 0)
    simp only [Circle.coe_neg, coe_toCircle ht, coe_toCircle h0] at hc
    have hn0 : (0 : ℝ) < ‖z 0 - p‖ := norm_pos_iff.2 h0
    have hnt : (0 : ℝ) < ‖z t - p‖ := norm_pos_iff.2 ht
    have key : z t - p = (-(‖z t - p‖ / ‖z 0 - p‖) : ℝ) • (z 0 - p) := by
      have hn0' : ((‖z 0 - p‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
      have hnt' : ((‖z t - p‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnt.ne'
      rw [Complex.real_smul]
      push_cast
      field_simp at hc ⊢
      linear_combination hc
    have := hpos t
    rw [key, smul_mul_assoc, Complex.smul_re] at this
    have h0' := hpos 0
    rw [smul_eq_mul] at this
    have : 0 < ‖z t - p‖ / ‖z 0 - p‖ := div_pos hnt hn0
    nlinarith
  have hlt := abs_lt_pi_of_zero h.pos.le hfc.continuousOn hne hf0
  have hone : Circle.exp (f L) = 1 := by
    rw [hf, Circle.exp_sub, circleExp_angleFn h.diff h.cont_deriv hp',
      circleExp_angleFn h.diff h.cont_deriv hp', show L = 0 + L by ring, h.periodic 0, div_self']
  have := eq_zero_of_circleExp_eq_one hone (by rw [abs_lt] at hlt ⊢; constructor <;> linarith)
  simpa [hf, angleFn] using this

/-! ### The area formula -/

/-- The integral of `(x - w)⁻¹` over the circle `|w| = ρ` with respect to the angle. -/
private theorem ring_integral {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρx : ρ ≠ ‖x‖) :
    ∫ φ in (0 : ℝ)..(2 * π), (x - circleMap 0 ρ φ)⁻¹ = if ρ < ‖x‖ then 2 * π / x else 0 := by
  have hne : ∀ φ, circleMap 0 ρ φ ≠ 0 := fun φ => circleMap_ne_center hρ.ne'
  have h1 : ∫ φ in (0 : ℝ)..(2 * π), (x - circleMap 0 ρ φ)⁻¹ =
      ∮ w in C(0, ρ), (I * w)⁻¹ * (x - w)⁻¹ := by
    rw [circleIntegral]
    congr 1; ext φ
    rw [deriv_circleMap, smul_eq_mul, ← mul_assoc,
      show circleMap 0 ρ φ * I * (I * circleMap 0 ρ φ)⁻¹ = 1 by
        rw [mul_comm (circleMap 0 ρ φ) I]; exact mul_inv_cancel₀ (mul_ne_zero I_ne_zero (hne φ)),
      one_mul]
  rw [h1]
  have hsph : ∀ w ∈ sphere (0 : ℂ) ρ, w ≠ 0 ∧ w ≠ x := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    refine ⟨fun h => by rw [h, norm_zero] at hw; exact hρ.ne' hw.symm, fun h => ?_⟩
    rw [h] at hw; exact hρx hw.symm
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [norm_zero, ite_eq_right_iff.2 (fun h => absurd h (not_lt.2 hρ.le))]
    have : EqOn (fun w : ℂ => (I * w)⁻¹ * (0 - w)⁻¹) (fun w => I • (w - 0) ^ (-2 : ℤ))
        (sphere (0 : ℂ) ρ) := by
      intro w hw
      have hw0 := (hsph w hw).1
      simp only [zero_sub, sub_zero, smul_eq_mul, zpow_neg, zpow_two]
      field_simp
      simp [sq]
    rw [circleIntegral.integral_congr hρ.le this, circleIntegral.integral_smul,
      circleIntegral.integral_sub_zpow_of_ne (by norm_num), smul_zero]
  have : EqOn (fun w : ℂ => (I * w)⁻¹ * (x - w)⁻¹)
      (fun w => (I * x)⁻¹ • ((w - 0)⁻¹ - (w - x)⁻¹)) (sphere (0 : ℂ) ρ) := by
    intro w hw
    obtain ⟨hw0, hwx⟩ := hsph w hw
    have h1 : x - w ≠ 0 := sub_ne_zero.2 (Ne.symm hwx)
    have h2 : w - x ≠ 0 := sub_ne_zero.2 hwx
    simp only [sub_zero, smul_eq_mul]
    field_simp
    ring
  have hint0 : CircleIntegrable (fun w : ℂ => (w - 0)⁻¹) 0 ρ :=
    ContinuousOn.circleIntegrable hρ.le (continuousOn_id.sub continuousOn_const |>.inv₀
      fun w hw => by simpa using (hsph w hw).1)
  have hintx : CircleIntegrable (fun w : ℂ => (w - x)⁻¹) 0 ρ :=
    ContinuousOn.circleIntegrable hρ.le (continuousOn_id.sub continuousOn_const |>.inv₀
      fun w hw => sub_ne_zero.2 (hsph w hw).2)
  rw [circleIntegral.integral_congr hρ.le this, circleIntegral.integral_smul,
    circleIntegral.integral_sub hint0 hintx,
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hρ)]
  split_ifs with hlt
  · have : ∮ w in C(0, ρ), (w - x)⁻¹ = 0 := by
      refine circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le countable_empty ?_ ?_
      · refine (continuousOn_id.sub continuousOn_const).inv₀ fun w hw => sub_ne_zero.2 ?_
        intro hwx
        simp only [id, mem_closedBall_zero_iff] at hwx hw
        rw [hwx] at hw
        linarith
      · intro w hw
        refine ((differentiableAt_id.sub (differentiableAt_const _)).inv (sub_ne_zero.2 ?_))
        intro hwx
        rw [sdiff_empty, mem_ball_zero_iff, hwx] at hw
        linarith
    rw [this, sub_zero, smul_eq_mul]
    field_simp
  · have hxb : x ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hρx)
    rw [circleIntegral.integral_sub_inv_of_mem_ball hxb, sub_self, smul_zero]

/-- `‖q‖⁻¹`, cut off outside the ball of radius `r`, is integrable on `ℂ`. -/
private theorem integrable_inv_norm_indicator (r : ℝ) :
    Integrable (fun q : ℂ => (ball (0 : ℂ) r).indicator (fun q => ‖q‖⁻¹) q) := by
  have e : (fun q : ℂ => (ball (0 : ℂ) r).indicator (fun q => ‖q‖⁻¹) q) =
      fun q => (Iio r).indicator (fun y : ℝ => y⁻¹) ‖q‖ := by
    ext q
    by_cases hq : ‖q‖ < r
    · rw [indicator_of_mem (mem_ball_zero_iff.2 hq), indicator_of_mem (show ‖q‖ ∈ Iio r from hq)]
    · rw [indicator_of_notMem (by rwa [mem_ball_zero_iff]),
        indicator_of_notMem (show ‖q‖ ∉ Iio r from hq)]
  rw [e, integrable_fun_norm_addHaar volume, Complex.finrank_real_complex]
  have : EqOn (fun y : ℝ => y ^ (2 - 1) • (Iio r).indicator (fun y : ℝ => y⁻¹) y)
      ((Iio r).indicator (fun _ => (1 : ℝ))) (Ioi 0) := by
    intro y hy
    simp only [smul_eq_mul]
    by_cases hyr : y < r
    · rw [indicator_of_mem hyr, indicator_of_mem hyr]
      simp [(mem_Ioi.1 hy).ne']
    · rw [indicator_of_notMem hyr, indicator_of_notMem hyr, mul_zero]
  refine IntegrableOn.congr_fun ?_ this.symm measurableSet_Ioi
  rw [IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio]
  have hsub : Iio r ∩ Ioi 0 ⊆ Ioc 0 r := fun y hy => ⟨hy.2, le_of_lt hy.1⟩
  exact integrableOn_const ((measure_mono hsub).trans_lt measure_Ioc_lt_top).ne (by simp)

private theorem integrableOn_inv_norm_sub {x : ℂ} {R : ℝ} (hx : ‖x‖ < R) :
    IntegrableOn (fun p : ℂ => ‖x - p‖⁻¹) (ball (0 : ℂ) R) := by
  have hG := (integrable_inv_norm_indicator (2 * R)).comp_sub_right x
  refine hG.integrableOn.congr_fun (fun p hp => ?_) measurableSet_ball
  simp only
  rw [indicator_of_mem, norm_sub_rev]
  rw [mem_ball_zero_iff] at hp ⊢
  calc ‖p - x‖ ≤ ‖p‖ + ‖x‖ := norm_sub_le _ _
    _ < 2 * R := by linarith

private theorem setIntegral_inv_norm_sub_le {x : ℂ} {R : ℝ} (hx : ‖x‖ < R) :
    ∫ p in ball (0 : ℂ) R, ‖x - p‖⁻¹ ≤
      ∫ q : ℂ, (ball (0 : ℂ) (2 * R)).indicator (fun q => ‖q‖⁻¹) q := by
  have hG := (integrable_inv_norm_indicator (2 * R)).comp_sub_right x
  calc ∫ p in ball (0 : ℂ) R, ‖x - p‖⁻¹
        = ∫ p in ball (0 : ℂ) R, (ball (0 : ℂ) (2 * R)).indicator (fun q => ‖q‖⁻¹) (p - x) := by
          refine setIntegral_congr_fun measurableSet_ball fun p hp => ?_
          rw [indicator_of_mem, norm_sub_rev]
          rw [mem_ball_zero_iff] at hp ⊢
          calc ‖p - x‖ ≤ ‖p‖ + ‖x‖ := norm_sub_le _ _
            _ < 2 * R := by linarith
    _ ≤ ∫ p, (ball (0 : ℂ) (2 * R)).indicator (fun q => ‖q‖⁻¹) (p - x) :=
          setIntegral_le_integral hG (Eventually.of_forall fun p =>
            indicator_nonneg (fun q _ => inv_nonneg.2 (norm_nonneg q)) _)
    _ = _ := integral_sub_right_eq_self (fun q => (ball (0 : ℂ) (2 * R)).indicator
          (fun q => ‖q‖⁻¹) q) x

private theorem integrableOn_inv_sub {x : ℂ} {R : ℝ} (hx : ‖x‖ < R) :
    IntegrableOn (fun p : ℂ => (x - p)⁻¹) (ball (0 : ℂ) R) :=
  Integrable.mono' (integrableOn_inv_norm_sub hx)
    (measurable_const.sub measurable_id).inv.aestronglyMeasurable
    (Eventually.of_forall fun p => by simp [norm_inv])

/-- **The integral of `(x - p)⁻¹` over a disc.** For `‖x‖ < R`,
`∫_{|p| < R} (x - p)⁻¹ dp = π x̄`: in polar coordinates, the circles of radius `ρ < ‖x‖`
contribute `2πρ / x` each and the larger ones nothing. -/
private theorem integral_ball_inv_sub {x : ℂ} {R : ℝ} (hx : ‖x‖ < R) :
    ∫ p in ball (0 : ℂ) R, (x - p)⁻¹ = π * conj x := by
  set f : ℂ → ℂ := (ball (0 : ℂ) R).indicator (fun p => (x - p)⁻¹) with hf
  have hfi : Integrable f := by
    rw [hf, integrable_indicator_iff measurableSet_ball]
    exact integrableOn_inv_sub hx
  have hfm : Measurable f :=
    (measurable_const.sub measurable_id).inv.indicator measurableSet_ball
  have hsymm : ∀ q : ℝ × ℝ, Complex.polarCoord.symm q = circleMap 0 q.1 q.2 := by
    intro q
    rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I]
    push_cast; ring
  rw [← integral_indicator measurableSet_ball, ← Complex.integral_comp_polarCoord_symm,
    polarCoord_target]
  set g : ℝ × ℝ → ℂ := fun q => q.1 • f (Complex.polarCoord.symm q) with hg
  have hsymm_cont : Continuous (fun q : ℝ × ℝ => Complex.polarCoord.symm q) := by
    have : (fun q : ℝ × ℝ => Complex.polarCoord.symm q) =
        fun q => (q.1 : ℂ) * (Real.cos q.2 + Real.sin q.2 * I) := by
      funext q; exact Complex.polarCoord_symm_apply q
    rw [this]; fun_prop
  have hgm : Measurable g := measurable_fst.smul (hfm.comp hsymm_cont.measurable)
  have hgi : IntegrableOn g (Ioi 0 ×ˢ Ioo (-π) π) (volume.prod volume) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    have : ∫⁻ q in Ioi 0 ×ˢ Ioo (-π) π, ‖g q‖ₑ ∂(volume.prod volume) = ∫⁻ p, ‖f p‖ₑ := by
      rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target, ← Measure.volume_eq_prod]
      refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun q hq => ?_
      simp only [g, eNorm_smul, smul_eq_mul]
      rw [Real.eNorm_of_nonneg (le_of_lt hq.1)]
    rw [HasFiniteIntegral, this]
    exact hfi.2
  have hinner : ∀ ρ ∈ Ioi (0 : ℝ), ρ ≠ ‖x‖ →
      ∫ φ in Ioo (-π) π, g (ρ, φ) = (Iio ‖x‖).indicator (fun ρ => ρ • (2 * π / x)) ρ := by
    intro ρ hρ hρx
    have hρ' : 0 < ρ := hρ
    have hcm : ∀ φ, ‖circleMap 0 ρ φ‖ = ρ := fun φ => by
      rw [norm_circleMap_zero, abs_of_pos hρ']
    simp only [g, hsymm]
    by_cases hρR : ρ < R
    · have hfe : ∀ φ, f (circleMap 0 ρ φ) = (x - circleMap 0 ρ φ)⁻¹ := fun φ =>
        indicator_of_mem (mem_ball_zero_iff.2 (by rw [hcm]; exact hρR)) _
      simp only [hfe]
      rw [integral_smul]
      have hring : ∫ φ in Ioo (-π) π, (x - circleMap 0 ρ φ)⁻¹ =
          if ρ < ‖x‖ then 2 * π / x else 0 := by
        rw [← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
        have hper : Function.Periodic (fun φ => (x - circleMap 0 ρ φ)⁻¹) (2 * π) := fun φ => by
          simp only [periodic_circleMap 0 ρ φ]
        have := hper.intervalIntegral_add_eq (-π) 0
        rw [show -π + 2 * π = π by ring, zero_add] at this
        rw [this]
        exact ring_integral hρ' hρx
      rw [hring]
      by_cases h : ρ < ‖x‖
      · rw [ite_eq_left_iff.2 (fun h' => absurd h h'), indicator_of_mem (show ρ ∈ Iio ‖x‖ from h)]
      · rw [ite_eq_right_iff.2 (fun h' => absurd h' h),
          indicator_of_notMem (show ρ ∉ Iio ‖x‖ from h), smul_zero]
    · have hfe : ∀ φ, f (circleMap 0 ρ φ) = 0 := fun φ =>
        indicator_of_notMem (by rw [mem_ball_zero_iff, hcm]; exact hρR) _
      simp only [hfe, smul_zero, integral_zero]
      rw [indicator_of_notMem]
      simp only [mem_Iio, not_lt]
      linarith [not_lt.1 hρR]
  have hnull : ∀ᵐ ρ ∂(volume : Measure ℝ), ρ ≠ ‖x‖ := by
    rw [ae_iff]; simp
  rw [Measure.volume_eq_prod, setIntegral_prod g hgi,
    setIntegral_congr_ae measurableSet_Ioi (g := (Iio ‖x‖).indicator (fun ρ => ρ • (2 * π / x)))
      (by filter_upwards [hnull] with ρ hρx hρ using hinner ρ hρ hρx),
    setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, integral_smul_const,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (norm_nonneg x), integral_id]
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have h1 : (x : ℂ) * conj x = ((‖x‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' x
    rw [Complex.real_smul]
    push_cast
    field_simp
    linear_combination -h1

/-- **Area formula for the winding sweep.** For a unit-speed `C¹` curve inside the disc of
radius `R`, the integral over the disc of the total angle change of `z t - p` is `π` times the
integral of `Im (z̄ z')`. -/
private theorem integral_ball_sweep {z : ℝ → ℂ} {L R : ℝ} (hL : 0 ≤ L) (hz : Continuous z)
    (hz' : Continuous (deriv z)) (hnorm : ∀ t, ‖deriv z t‖ = 1) (hR : ∀ t, ‖z t‖ < R) :
    ∫ p in ball (0 : ℂ) R, (∫ t in (0 : ℝ)..L, deriv z t / (z t - p)).im =
      π * ∫ t in (0 : ℝ)..L, (conj (z t) * deriv z t).im := by
  set μ : Measure ℂ := volume.restrict (ball (0 : ℂ) R) with hμ
  set ν : Measure ℝ := volume.restrict (Ioc 0 L) with hν
  set F : ℂ × ℝ → ℂ := fun q => deriv z q.2 / (z q.2 - q.1) with hF
  have hFm : Measurable F :=
    (hz'.measurable.comp measurable_snd).div
      ((hz.measurable.comp measurable_snd).sub measurable_fst)
  set C := ∫ q : ℂ, (ball (0 : ℂ) (2 * R)).indicator (fun q => ‖q‖⁻¹) q
  have hFi : Integrable F (μ.prod ν) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    constructor
    · refine Eventually.of_forall fun t => ?_
      simp only [F, div_eq_mul_inv]
      exact (integrableOn_inv_sub (hR t)).const_mul (deriv z t)
    · refine Integrable.mono' (integrable_const C) ?_ (Eventually.of_forall fun t => ?_)
      · exact (hFm.norm.aestronglyMeasurable.prod_swap (μ := ν) (ν := μ)).integral_prod_right'
      · rw [Real.norm_of_nonneg (integral_nonneg fun p => norm_nonneg _)]
        have : ∫ p, ‖F (p, t)‖ ∂μ = ∫ p in ball (0 : ℂ) R, ‖z t - p‖⁻¹ := by
          refine integral_congr_ae (Eventually.of_forall fun p => ?_)
          simp [F, hnorm]
        rw [this]
        exact setIntegral_inv_norm_sub_le (hR t)
  have hswap := integral_integral_swap (f := fun p t => F (p, t)) hFi
  have hint_p : Integrable (fun p => ∫ t, F (p, t) ∂ν) μ := hFi.integral_prod_left
  have hL1 : ∫ p in ball (0 : ℂ) R, (∫ t in (0 : ℝ)..L, deriv z t / (z t - p)).im =
      (∫ p, ∫ t, F (p, t) ∂ν ∂μ).im := by
    rw [← RCLike.im_to_complex, ← integral_im hint_p]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [intervalIntegral.integral_of_le hL, F, RCLike.im_to_complex, hν]
  have hR1 : ∫ t, ∫ p, F (p, t) ∂μ ∂ν = ∫ t, (π : ℂ) * (conj (z t) * deriv z t) ∂ν := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [F, div_eq_mul_inv]
    rw [integral_const_mul, integral_ball_inv_sub (hR t)]
    ring
  have hcont : Continuous fun t => conj (z t) * deriv z t :=
    (Complex.continuous_conj.comp hz).mul hz'
  rw [hL1, hswap, hR1, integral_const_mul, Complex.im_ofReal_mul,
    intervalIntegral.integral_of_le hL, ← RCLike.im_to_complex, ← integral_im
      (hcont.integrableOn_Ioc (μ := volume))]
  simp only [RCLike.im_to_complex]

/-- The image of a differentiable curve has measure zero in `ℂ`. -/
private theorem volume_range_eq_zero {z : ℝ → ℂ} (hz : Differentiable ℝ z) :
    volume (range z) = 0 := by
  set F : ℂ → ℂ := fun w => z w.re
  have hF : DifferentiableOn ℝ F (LinearMap.ker Complex.imLm : Set ℂ) :=
    (hz.comp Complex.reCLM.differentiable).differentiableOn
  have hs : volume (LinearMap.ker Complex.imLm : Set ℂ) = 0 := by
    refine Measure.addHaar_submodule volume _ fun h => ?_
    have : I ∈ LinearMap.ker Complex.imLm := h ▸ Submodule.mem_top
    simp at this
  refine measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    volume hF hs)
  rintro _ ⟨t, rfl⟩
  exact ⟨(t : ℂ), by simp, by simp [F]⟩

end Proof

/- **Hopf Umlaufsatz.** A positively oriented simple closed unit-speed plane
curve has total signed curvature `2π`. -/
set_option linter.dupNamespace false in
/-- **Hopf's Umlaufsatz.** Let $r : \mathbb{R} \to \mathbb{R}^2$ be a positively oriented simple
closed unit-speed plane curve: $r$ is continuously differentiable and $2\pi$-periodic, injective
on $[0, 2\pi)$, satisfies $\lVert r'(t) \rVert = 1$ for all $t$, and has positive signed area
$\frac{1}{2}\int_0^{2\pi} \det(r(t), r'(t))\,dt > 0$, where $\det(u, v) = u_0 v_1 - u_1 v_0$.
Let $\alpha : \mathbb{R} \to \mathbb{R}$ be a continuously differentiable tangent-angle lift of
$r$, that is, $r'(t) = (\cos \alpha(t), \sin \alpha(t))$ for all $t$. Then the total signed
curvature over one period is $2\pi$: $\int_0^{2\pi} \alpha'(t)\,dt = 2\pi$.

Source: H. Hopf, *Über die Drehung der Tangenten...*, Compositio Math. 2 (1935). Knill, §170.
Via leanprover/lean-eval@38361be, problem `hopf_umlaufsatz`. -/
theorem hopf_umlaufsatz
    {r : ℝ → Plane} {α : ℝ → ℝ}
    (_hr : IsPositiveSimpleClosedUnitSpeedCurve r)
    (_hα : IsTangentAngleLift r α) :
    totalCurvature α = 2 * Real.pi := by
  set e : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm with he
  have he_apply : ∀ v : Plane, e v = (v 0 : ℂ) + (v 1 : ℂ) * I := fun v =>
    Complex.orthonormalBasisOneI_repr_symm_apply v
  set z : ℝ → ℂ := fun t => e (r t) with hz
  set L : ℝ := period with hLdef
  have hL : 0 < L := by simp only [L, period]; positivity
  have hr_diff : Differentiable ℝ r := _hr.smooth.differentiable one_ne_zero
  have hz_deriv : ∀ t, HasDerivAt z (e (deriv r t)) t := fun t =>
    (e.hasFDerivAt (x := r t)).comp_hasDerivAt t (hr_diff t).hasDerivAt
  have hz_deriv_eq : ∀ t, deriv z t = e (deriv r t) := fun t => (hz_deriv t).deriv
  have hz_diff : Differentiable ℝ z := fun t => (hz_deriv t).differentiableAt
  have hz'_cont : Continuous (deriv z) := by
    rw [show deriv z = fun t => e (deriv r t) from funext hz_deriv_eq]
    exact e.continuous.comp (_hr.smooth.continuous_deriv le_rfl)
  have hz_exp : ∀ t, deriv z t = (Circle.exp (α t) : ℂ) := by
    intro t
    rw [hz_deriv_eq, ← velocity, _hα.velocity_eq, he_apply, Circle.coe_exp, Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin]
  have hC : CurveHyp z L α :=
    { pos := hL
      diff := hz_diff
      cont_deriv := hz'_cont
      periodic := fun t => by
        change e (r (t + period)) = e (r t)
        rw [_hr.periodic t]
      inj := fun s hs t ht hst => _hr.injective_on_period hs ht (e.injective hst)
      cont := _hα.smooth.continuous
      deriv_eq := hz_exp }
  -- the signed area in complex form
  have harea : signedArea r = (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..L, (conj (z t) * deriv z t).im := by
    simp only [signedArea, L]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hz_deriv_eq t]
    simp only [hz, he_apply, det2, velocity]
    simp
    ring
  -- a radius containing the curve
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn
    hz_diff.continuous.continuousOn
  have hbound : ∀ t, ‖z t‖ ≤ M := by
    intro t
    have hm := toIcoMod_mem_Ico hL 0 t
    rw [zero_add] at hm
    have e' : toIcoMod hL 0 t = t - toIcoDiv hL 0 t • L := by rw [← self_sub_toIcoMod]; ring
    have := hM _ (Ico_subset_Icc_self hm)
    rwa [e', hC.periodic.sub_zsmul_eq] at this
  set R := |M| + 1 with hR
  have hzR : ∀ t, ‖z t‖ < R := fun t => by
    have := hbound t; have := le_abs_self M; linarith
  have hR0 : 0 < R := by positivity
  -- the far point fixes the rotation index up to sign
  have hfar : ∀ t, ‖z t‖ < ‖(R : ℂ)‖ := fun t => by
    rw [Complex.norm_real, Real.norm_of_nonneg hR0.le]; exact hzR t
  have hzero := hC.sweep_eq_zero_of_far hfar
  have hp₀ : ∀ t, z t ≠ (R : ℂ) := fun t h => by
    have := hfar t; rw [h] at this; exact lt_irrefl _ this
  obtain ⟨σ₀, hσ₀, hsw₀⟩ := hC.sweep_eq hp₀
  rw [hzero] at hsw₀
  have hrot : α L - α 0 = 2 * π := by
    rcases hσ₀ with rfl | rfl
    · -- rotation index `-1`: the signed area would be nonpositive
      exfalso
      have hle : ∀ p : ℂ, p ∉ range z →
          (∫ t in (0 : ℝ)..L, deriv z t / (z t - p)).im ≤ 0 := by
        intro p hp
        have hp' : ∀ t, z t ≠ p := fun t h => hp ⟨t, h⟩
        obtain ⟨σ, hσ, hsw⟩ := hC.sweep_eq hp'
        rcases hσ with rfl | rfl <;> linarith [Real.pi_pos]
      have hae : ∀ᵐ p ∂(volume : Measure ℂ),
          (∫ t in (0 : ℝ)..L, deriv z t / (z t - p)).im ≤ 0 := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_range_eq_zero hz_diff)] with p hp
        exact hle p hp
      have hint := integral_ball_sweep hL.le hz_diff.continuous hz'_cont hC.norm_deriv hzR
      have hnp : ∫ p in ball (0 : ℂ) R, (∫ t in (0 : ℝ)..L, deriv z t / (z t - p)).im ≤ 0 :=
        setIntegral_nonpos_of_ae hae
      rw [hint] at hnp
      have hpos := _hr.positive_orientation
      rw [harea] at hpos
      have : ∫ t in (0 : ℝ)..L, (conj (z t) * deriv z t).im ≤ 0 := by
        by_contra h
        push Not at h
        have := mul_pos Real.pi_pos h
        linarith
      linarith
    · linarith
  -- conclude with the fundamental theorem of calculus
  have hα_diff : Differentiable ℝ α := _hα.smooth.differentiable one_ne_zero
  have hα'_cont : Continuous (deriv α) := _hα.smooth.continuous_deriv le_rfl
  simp only [totalCurvature, signedCurvature]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => (hα_diff t).hasDerivAt)
    (hα'_cont.intervalIntegrable _ _)]
  exact hrot

end Geometry.HopfUmlaufsatz

end MathlibExt.Geometry.HopfUmlaufsatzWanted
