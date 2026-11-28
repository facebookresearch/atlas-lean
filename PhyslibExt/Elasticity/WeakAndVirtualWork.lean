/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Elasticity.StressStrain
public import PhyslibExt.ContinuumMechanics.ControlVolumes
public import PhyslibExt.EarthScience.WeakDiffusion
public import PhyslibExt.Elasticity.PrismaticMembers

/-!
# The weak bar problem and virtual work on a box

## i. Overview

**The weak bar problem.** A bar of length `L > 0`, fixed at both ends, has a measurable axial
rigidity `EA` with `0 < EAmin ≤ EA ≤ EAmax` almost everywhere on `[0, L]` and carries an axial
load `q ∈ L²(0, L)`. Its weak problem asks for `u ∈ H¹₀(0, L)` with `∫₀ᴸ EA u' v' = ∫₀ᴸ q v` for
every `v ∈ H¹₀(0, L)` (`IsWeakBarSolution`). `H¹₀(0, L)` is encoded by `WeakH10On L` exactly as
`EarthScience.WeakH10` encodes `H¹₀(0, 1)`: a representative that is the primitive, from `0`, of
an `L²(0, L)` weak derivative with zero integral, so that it vanishes at both ends. Values outside
`[0, L]` are irrelevant.

The change of variables `x = L ξ` maps the bar problem to the unit problem of
`EarthScience.weak_diffusion_exists_unique` with diffusivity `κ ξ = EA (L ξ) / L`
(`scaledRigidity`) and source `f̂ ξ = L q (L ξ)` (`scaledLoad`). It transports the
representation in both directions: `v ↦ v̂` with `v̂ ξ = v (L ξ)` and `v̂' ξ = L v' (L ξ)`
(`WeakH10On.toUnit`), and `ŵ ↦ w` with `w x = ŵ (x / L)` and `w' x = ŵ' (x / L) / L`
(`WeakH10On.ofUnit`); the two maps are mutually inverse on the stored fields. It also transports
the two weak integrals, `∫₀ᴸ EA u' v' = ∫₀¹ κ û' v̂'` and `∫₀ᴸ q v = ∫₀¹ f̂ v̂`, and the hypotheses:
`κ` is a.e. strongly measurable with `EAmin / L ≤ κ ≤ EAmax / L` a.e. on `[0, 1]`, and
`f̂ ∈ L²(0, 1)`. So the unit solution `û` gives the bar solution `u x = û (x / L)`, and a bar
solution pulled back to `[0, 1]` is a unit solution; uniqueness is uniqueness of the displacement
values on `[0, L]`.

Validation: with constant `EA` the weak solution is the classical fixed-fixed displacement
`q x (L - x) / (2 EA)` of `PhyslibExt.Elasticity.PrismaticMembers`; a positive piecewise
constant rigidity is admissible; zero rigidity has no weak solution under a unit load, a
nonpositive rigidity has no positive a.e. lower bound, and the fixed-free displacement (a traction
end) is not an element of `H¹₀(0, L)`.

Model inputs: small-strain linear elastic bar with scalar axial displacement, zero displacement
at both ends. Non-goals: traction ends, a global Hilbert-space equivalence, multidimensional
`H¹`, traces or Korn inequalities, and any empirical adequacy or system safety claim.

**Virtual work on a box.** On a nondegenerate box `[a, b]` in `ℝ³ = Fin 3 → ℝ`, let `σ` be a
tension-positive Cauchy stress field, symmetric on the box and `C¹` on an open neighbourhood `U`
of it, `v` a `C¹` virtual displacement on `U`, and `body` a body force with the equilibrium
equations `div σ + body = 0` on the box (`stressDivergence`, the divergence of each row `σ i ·`).
Applying the existing box divergence theorem `ControlVolumes.integral_divergence_box` to the
vector field `σᵀ v` gives the virtual work identity

`∫_[a, b] σ : ε(v) = ∫_[a, b] body · v + ∑_faces ∫_face (σ n) · v`,

where `ε(v) = Elasticity.smallStrain (Elasticity.displacementGradient v x)` is the canonical small
strain and the face sum (`boxTractionWork`) has the outward normal `+eᵢ` on the face `x i = b i`
(`upperFaceWork`) and `-eᵢ` on the face `x i = a i` (`lowerFaceWork`), with the Cauchy traction
`Elasticity.traction (σ x) n = σ n`. The proof is the product rule
`div (σᵀ v) = (div σ) · v + σ : ∇v` and, for symmetric `σ`, `σ : ∇v = σ : ε(v)`. A face on which
`v` vanishes contributes nothing and is removed from the identity; no other face is. A rigid
virtual displacement `v x = W x`, `Wᵀ = -W`, has zero small strain, so its external virtual work
vanishes. That it stores no elastic energy is `EarthScience.elastic_energy_of_skew` once
`Elasticity.mulVec_eq_affine` and `Elasticity.displacementGradient_affine` rewrite its strain to
`smallStrain W`.

Validation: for simple shear, `σ : ε = τ γ`, while contracting `σ` with the engineering shear
`γ = 2 ε₀₁` in both off-diagonal slots gives `2 τ γ`. The test file checks the constant uniaxial
stress `σ = diag (3, 0, 0)` on `[1, 3] × [0, 1] × [0, 1]` with `v x = (x₀, 0, 0)`: the opposing
faces `x₀ = 3` and `x₀ = 1` carry the tractions `(3, 0, 0)` and `(-3, 0, 0)` and do the works `9`
and `-3`, and the internal virtual work is `3 · 2 = 6`; with the inward normal on the face
`x₀ = 1` the face sum would be `12`.

Model inputs: small-strain kinematics, tension-positive symmetric Cauchy stress, equilibrium
`div σ + body = 0` on the box, outward normals. This is the smooth virtual work identity, not a
weak-space existence result; no Korn or coercivity statement is claimed, and no empirical
adequacy or system safety claim is made.

## ii. Key results

- `WeakH10On`, `WeakH10On.toUnit`, `WeakH10On.ofUnit`, `WeakH10On.ofUnit_toUnit`,
  `WeakH10On.toUnit_ofUnit`: the bar space and the two transport maps.
- `integral_rigidity_toUnit`, `integral_load_toUnit`, `integral_rigidity_ofUnit`,
  `integral_load_ofUnit`: the transported weak integrals.
- `isWeakBarSolution_ofUnit`, `IsWeakBarSolution.toUnit`, `weakBar_exists_unique`: existence
  and uniqueness through `EarthScience.weak_diffusion_exists_unique`.
- `IsWeakBarSolution.eqOn_axialDisplacement`, `stepRigidity_admissible`,
  `not_isWeakBarSolution_zero_rigidity`, `not_ae_lowerBound_of_nonpos`,
  `not_exists_weakH10On_eqOn_fixedFree`: validation of the weak bar problem.
- `stressDivergence`, `upperFaceWork`, `lowerFaceWork`, `boxTractionWork`.
- `boxTractionWork_eq_boxOutwardFlux`, `divergence_transpose_mulVec`,
  `doubleDot_eq_doubleDot_smallStrain`: the three ingredients of the virtual work identity.
- `virtualWork_box`: the virtual work identity.
- `upperFaceWork_eq_zero`, `lowerFaceWork_eq_zero`, `virtualWork_box_of_lowerFace_eq_zero`:
  removing a face where `v = 0`.
- `virtualWork_box_rigid`: a rigid virtual displacement does no external virtual work.
- `simpleShear_engineering_double_count`: the engineering shear factor.

The numeric fixtures are in `PhyslibExtTest.Elasticity.WeakAndVirtualWorkTest`.

## iii. Table of contents

- A. The bar space and the two transport maps
- B. Transport of the weak integrals and of the hypotheses
- C. Existence and uniqueness
- D. Validation examples
- E. Stress divergence and face works
- F. The virtual work identity
- G. Clamped faces and rigid virtual displacements
- H. Validation of the virtual work identity

## iv. References

- H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Springer, 2011, chapter 8 (one-dimensional `H¹₀` and Dirichlet problems).
- T. J. R. Hughes, *The Finite Element Method: Linear Static and Dynamic Finite Element
  Analysis*, Dover, 2000, chapter 1 (the weak form of the bar problem).
- M. E. Gurtin, *An Introduction to Continuum Mechanics*, Academic Press, 1981 (the theorem of
  virtual work).
- P. G. Ciarlet, *Mathematical Elasticity, Volume I: Three-Dimensional Elasticity*,
  North-Holland, 1988, chapter 2 (the principle of virtual work).
- `EarthScience.WeakH10` and `EarthScience.weak_diffusion_exists_unique` in
  `PhyslibExt.EarthScience.WeakDiffusion`; `ControlVolumes.integral_divergence_box` and
  Mathlib's `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`.
-/

@[expose] public section

namespace Elasticity.WeakAndVirtualWork

open MeasureTheory EarthScience Elasticity.PrismaticMembers

/-! ## A. The bar space and the two transport maps -/

/-- An element of `H¹₀(0, L)`, in the encoding of `EarthScience.WeakH10`: a representative
`toFun`, meaningful on `[0, L]`, which on `[0, L]` is the primitive from `0` of a weak derivative
`weakDeriv ∈ L²(0, L)`, and whose weak derivative has integral zero over `[0, L]` (the end
condition `toFun L = 0`). Values outside `[0, L]` are unconstrained. -/
structure WeakH10On (L : ℝ) where
  /-- The representative, meaningful on `[0, L]`. -/
  toFun : ℝ → ℝ
  /-- The weak derivative, an `L²` function on `[0, L]`. -/
  weakDeriv : ℝ → ℝ
  /-- The weak derivative is square integrable on `[0, L]`. -/
  weakDeriv_memLp : MemLp weakDeriv 2 (volume.restrict (Set.Icc 0 L))
  /-- On `[0, L]`, `toFun` is the primitive of `weakDeriv` starting from `0`. -/
  toFun_eq_integral : ∀ x ∈ Set.Icc (0 : ℝ) L, toFun x = ∫ t in (0 : ℝ)..x, weakDeriv t
  /-- The weak derivative has integral zero over `[0, L]`, the condition `toFun L = 0`. -/
  integral_weakDeriv_eq_zero : ∫ t in (0 : ℝ)..L, weakDeriv t = 0

/-- Zero displacement at both ends: for `0 ≤ L`, every `v : WeakH10On L` has `v.toFun 0 = 0`
and `v.toFun L = 0`. -/
lemma WeakH10On.toFun_zero_and_length {L : ℝ} (hL : 0 ≤ L) (v : WeakH10On L) :
    v.toFun 0 = 0 ∧ v.toFun L = 0 := by
  exact ⟨by rw [v.toFun_eq_integral 0 ⟨le_rfl, hL⟩]; simp,
    by rw [v.toFun_eq_integral L ⟨hL, le_rfl⟩]; exact v.integral_weakDeriv_eq_zero⟩

/-- For `L > 0`, the preimage of `[0, L]` under `ξ ↦ L * ξ` is `[0, 1]`. -/
private lemma preimage_mul_Icc {L : ℝ} (hL : 0 < L) :
    (fun ξ : ℝ => L * ξ) ⁻¹' Set.Icc 0 L = Set.Icc 0 1 := by
  ext ξ
  simp only [Set.mem_preimage, Set.mem_Icc]
  rw [mul_nonneg_iff_of_pos_left hL, mul_le_iff_le_one_right hL]

/-- For `L > 0`, the preimage of `[0, 1]` under `x ↦ L⁻¹ * x` is `[0, L]`. -/
private lemma preimage_inv_mul_Icc {L : ℝ} (hL : 0 < L) :
    (fun x : ℝ => L⁻¹ * x) ⁻¹' Set.Icc 0 1 = Set.Icc 0 L := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Icc]
  rw [mul_nonneg_iff_of_pos_left (inv_pos.2 hL), inv_mul_le_iff₀ hL, mul_one]

/-- The image of Lebesgue measure on `[0, 1]` under `ξ ↦ L * ξ` is `L⁻¹` times Lebesgue measure
on `[0, L]`. -/
private lemma map_mul_restrict_Icc {L : ℝ} (hL : 0 < L) :
    Measure.map (fun ξ : ℝ => L * ξ) (volume.restrict (Set.Icc (0 : ℝ) 1)) =
      ENNReal.ofReal L⁻¹ • volume.restrict (Set.Icc 0 L) := by
  have he := measurableEmbedding_mulLeft₀ (G₀ := ℝ) hL.ne'
  rw [← preimage_mul_Icc hL, ← he.restrict_map, Real.map_volume_mul_left hL.ne',
    Measure.restrict_smul, abs_of_pos (inv_pos.2 hL)]

/-- The image of Lebesgue measure on `[0, L]` under `x ↦ L⁻¹ * x` is `L` times Lebesgue measure
on `[0, 1]`. -/
private lemma map_inv_mul_restrict_Icc {L : ℝ} (hL : 0 < L) :
    Measure.map (fun x : ℝ => L⁻¹ * x) (volume.restrict (Set.Icc (0 : ℝ) L)) =
      ENNReal.ofReal L • volume.restrict (Set.Icc 0 1) := by
  have he := measurableEmbedding_mulLeft₀ (G₀ := ℝ) (inv_ne_zero hL.ne')
  rw [← preimage_inv_mul_Icc hL, ← he.restrict_map,
    Real.map_volume_mul_left (inv_ne_zero hL.ne'), Measure.restrict_smul, inv_inv,
    abs_of_pos hL]

/-- For `0 < L`, the scaled weak derivative `ξ ↦ L * g (L * ξ)` is in `L²(0, 1)` when
`g ∈ L²(0, L)`. -/
lemma memLp_scale_toUnit {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Icc 0 L))) :
    MemLp (fun ξ => L * g (L * ξ)) 2 (volume.restrict (Set.Icc 0 1)) := by
  have h1 : MemLp g 2 (Measure.map (fun ξ : ℝ => L * ξ) (volume.restrict (Set.Icc 0 1))) := by
    rw [map_mul_restrict_Icc hL]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  have h2 := (memLp_map_measure_iff h1.aestronglyMeasurable
    (measurable_const_mul L).aemeasurable).1 h1
  exact h2.const_mul L

/-- For `0 < L`, the scaled weak derivative `x ↦ g (x / L) / L` is in `L²(0, L)` when
`g ∈ L²(0, 1)`. -/
lemma memLp_scale_ofUnit {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Icc 0 1))) :
    MemLp (fun x => g (x / L) / L) 2 (volume.restrict (Set.Icc 0 L)) := by
  have h1 : MemLp g 2 (Measure.map (fun x : ℝ => L⁻¹ * x) (volume.restrict (Set.Icc 0 L))) := by
    rw [map_inv_mul_restrict_Icc hL]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  have h2 := (memLp_map_measure_iff h1.aestronglyMeasurable
    (measurable_const_mul L⁻¹).aemeasurable).1 h1
  have h3 := h2.const_mul L⁻¹
  have he : (fun x => g (x / L) / L) = fun x => L⁻¹ * (g ∘ fun x => L⁻¹ * x) x := by
    funext x
    simp only [Function.comp, div_eq_inv_mul]
  rw [he]
  exact h3

/-- For `0 < L`, `x = L ξ` transports the primitive representation to `[0, 1]`: for every
`v : WeakH10On L` and `ξ ∈ [0, 1]`, `v (L ξ) = ∫₀^ξ L * v' (L t) dt`. -/
lemma toUnit_primitive {L : ℝ} (hL : 0 < L) (v : WeakH10On L) :
    ∀ ξ ∈ Set.Icc (0 : ℝ) 1, v.toFun (L * ξ) = ∫ t in (0 : ℝ)..ξ, L * v.weakDeriv (L * t) := by
  intro ξ hξ
  have hLξ : L * ξ ∈ Set.Icc (0 : ℝ) L :=
    ⟨mul_nonneg hL.le hξ.1, mul_le_of_le_one_right hL.le hξ.2⟩
  rw [v.toFun_eq_integral _ hLξ, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun t => v.weakDeriv t) hL.ne', mul_zero,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]

/-- For `0 < L`, `x = L ξ` transports the end condition to `[0, 1]`: every `v : WeakH10On L`
has `∫₀¹ L * v' (L t) dt = 0`. -/
lemma toUnit_integral_eq_zero {L : ℝ} (hL : 0 < L) (v : WeakH10On L) :
    ∫ t in (0 : ℝ)..1, L * v.weakDeriv (L * t) = 0 := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun t => v.weakDeriv t) hL.ne', mul_zero, mul_one,
    smul_eq_mul, v.integral_weakDeriv_eq_zero, mul_zero, mul_zero]

/-- For `0 < L`, `ξ = x / L` transports the primitive representation to `[0, L]`: for every
`ŵ : WeakH10` and `x ∈ [0, L]`, `ŵ (x / L) = ∫₀ˣ ŵ' (t / L) / L dt`. -/
lemma ofUnit_primitive {L : ℝ} (hL : 0 < L) (w : WeakH10) :
    ∀ x ∈ Set.Icc (0 : ℝ) L, w.toFun (x / L) = ∫ t in (0 : ℝ)..x, w.weakDeriv (t / L) / L := by
  intro x hx
  have hxL : x / L ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg hx.1 hL.le, (div_le_one hL).2 hx.2⟩
  rw [w.toFun_eq_integral _ hxL, intervalIntegral.integral_div,
    intervalIntegral.integral_comp_div (fun t => w.weakDeriv t) hL.ne', zero_div, smul_eq_mul]
  field_simp

/-- For `0 < L`, `ξ = x / L` transports the end condition to `[0, L]`: every `ŵ : WeakH10` has
`∫₀ᴸ ŵ' (t / L) / L dt = 0`. -/
lemma ofUnit_integral_eq_zero {L : ℝ} (hL : 0 < L) (w : WeakH10) :
    ∫ t in (0 : ℝ)..L, w.weakDeriv (t / L) / L = 0 := by
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_comp_div (fun t => w.weakDeriv t) hL.ne', zero_div, div_self hL.ne',
    smul_eq_mul, w.integral_weakDeriv_eq_zero, mul_zero, zero_div]

/-- For `0 < L`, pull a bar field back to `[0, 1]`: `v̂ ξ = v (L ξ)` and
`v̂' ξ = L * v' (L ξ)`. -/
noncomputable def WeakH10On.toUnit {L : ℝ} (hL : 0 < L) (v : WeakH10On L) : WeakH10 where
  toFun ξ := v.toFun (L * ξ)
  weakDeriv ξ := L * v.weakDeriv (L * ξ)
  weakDeriv_memLp := memLp_scale_toUnit hL v.weakDeriv_memLp
  toFun_eq_integral := toUnit_primitive hL v
  integral_weakDeriv_eq_zero := toUnit_integral_eq_zero hL v

/-- For `0 < L`, push a unit field forward to `[0, L]`: `w x = ŵ (x / L)` and
`w' x = ŵ' (x / L) / L`. -/
noncomputable def WeakH10On.ofUnit {L : ℝ} (hL : 0 < L) (w : WeakH10) : WeakH10On L where
  toFun x := w.toFun (x / L)
  weakDeriv x := w.weakDeriv (x / L) / L
  weakDeriv_memLp := memLp_scale_ofUnit hL w.weakDeriv_memLp
  toFun_eq_integral := ofUnit_primitive hL w
  integral_weakDeriv_eq_zero := ofUnit_integral_eq_zero hL w

/-- Round trip from the bar: for `0 < L`, `ofUnit (toUnit v)` has the fields of `v`, the same
`toFun` and the same `weakDeriv`. -/
lemma WeakH10On.ofUnit_toUnit {L : ℝ} (hL : 0 < L) (v : WeakH10On L) :
    (WeakH10On.ofUnit hL (v.toUnit hL)).toFun = v.toFun ∧
      (WeakH10On.ofUnit hL (v.toUnit hL)).weakDeriv = v.weakDeriv := by
  constructor
  · funext x
    change v.toFun (L * (x / L)) = v.toFun x
    rw [mul_div_cancel₀ x hL.ne']
  · funext x
    change L * v.weakDeriv (L * (x / L)) / L = v.weakDeriv x
    rw [mul_div_cancel₀ x hL.ne']
    field_simp

/-- Round trip from the unit interval: for `0 < L`, `toUnit (ofUnit ŵ)` has the fields of `ŵ`,
the same `toFun` and the same `weakDeriv`. -/
lemma WeakH10On.toUnit_ofUnit {L : ℝ} (hL : 0 < L) (w : WeakH10) :
    ((WeakH10On.ofUnit hL w).toUnit hL).toFun = w.toFun ∧
      ((WeakH10On.ofUnit hL w).toUnit hL).weakDeriv = w.weakDeriv := by
  constructor
  · funext ξ
    change w.toFun (L * ξ / L) = w.toFun ξ
    rw [mul_div_cancel_left₀ ξ hL.ne']
  · funext ξ
    change L * (w.weakDeriv (L * ξ / L) / L) = w.weakDeriv ξ
    rw [mul_div_cancel_left₀ ξ hL.ne']
    field_simp

/-! ## B. Transport of the weak integrals and of the hypotheses -/

/-- The unit diffusivity `κ ξ = EA (L ξ) / L`. -/
noncomputable def scaledRigidity (EA : ℝ → ℝ) (L ξ : ℝ) : ℝ :=
  EA (L * ξ) / L

/-- The unit source `f̂ ξ = L q (L ξ)`. -/
noncomputable def scaledLoad (q : ℝ → ℝ) (L ξ : ℝ) : ℝ :=
  L * q (L * ξ)

/-- Energy integral, bar to unit: for `0 < L`, `∫₀¹ κ û' v̂' = ∫₀ᴸ EA u' v'`. -/
lemma integral_rigidity_toUnit {L : ℝ} (hL : 0 < L) (EA : ℝ → ℝ) (u v : WeakH10On L) :
    ∫ ξ in (0 : ℝ)..1, scaledRigidity EA L ξ * (u.toUnit hL).weakDeriv ξ *
        (v.toUnit hL).weakDeriv ξ =
      ∫ x in (0 : ℝ)..L, EA x * u.weakDeriv x * v.weakDeriv x := by
  have h : ∀ ξ, scaledRigidity EA L ξ * (u.toUnit hL).weakDeriv ξ * (v.toUnit hL).weakDeriv ξ =
      L * (EA (L * ξ) * u.weakDeriv (L * ξ) * v.weakDeriv (L * ξ)) := by
    intro ξ
    change EA (L * ξ) / L * (L * u.weakDeriv (L * ξ)) * (L * v.weakDeriv (L * ξ)) = _
    field_simp
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => EA x * u.weakDeriv x * v.weakDeriv x)
      hL.ne', mul_zero, mul_one, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]

/-- Load integral, bar to unit: for `0 < L`, `∫₀¹ f̂ v̂ = ∫₀ᴸ q v`. -/
lemma integral_load_toUnit {L : ℝ} (hL : 0 < L) (q : ℝ → ℝ) (v : WeakH10On L) :
    ∫ ξ in (0 : ℝ)..1, scaledLoad q L ξ * (v.toUnit hL).toFun ξ =
      ∫ x in (0 : ℝ)..L, q x * v.toFun x := by
  have h : ∀ ξ, scaledLoad q L ξ * (v.toUnit hL).toFun ξ = L * (q (L * ξ) * v.toFun (L * ξ)) := by
    intro ξ
    change L * q (L * ξ) * v.toFun (L * ξ) = _
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => q x * v.toFun x) hL.ne', mul_zero, mul_one,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]

/-- Energy integral, unit to bar: for `0 < L`, `∫₀ᴸ EA w₁' w₂' = ∫₀¹ κ ŵ₁' ŵ₂'`. -/
lemma integral_rigidity_ofUnit {L : ℝ} (hL : 0 < L) (EA : ℝ → ℝ) (w₁ w₂ : WeakH10) :
    ∫ x in (0 : ℝ)..L, EA x * (WeakH10On.ofUnit hL w₁).weakDeriv x *
        (WeakH10On.ofUnit hL w₂).weakDeriv x =
      ∫ ξ in (0 : ℝ)..1, scaledRigidity EA L ξ * w₁.weakDeriv ξ * w₂.weakDeriv ξ := by
  have h : ∀ x, EA x * (WeakH10On.ofUnit hL w₁).weakDeriv x * (WeakH10On.ofUnit hL w₂).weakDeriv x =
      (scaledRigidity EA L (x / L) * w₁.weakDeriv (x / L) * w₂.weakDeriv (x / L)) / L := by
    intro x
    change EA x * (w₁.weakDeriv (x / L) / L) * (w₂.weakDeriv (x / L) / L) =
      EA (L * (x / L)) / L * w₁.weakDeriv (x / L) * w₂.weakDeriv (x / L) / L
    rw [mul_div_cancel₀ x hL.ne']
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_comp_div
      (fun ξ => scaledRigidity EA L ξ * w₁.weakDeriv ξ * w₂.weakDeriv ξ) hL.ne',
    zero_div, div_self hL.ne', smul_eq_mul]
  field_simp

/-- Load integral, unit to bar: for `0 < L`, `∫₀ᴸ q w = ∫₀¹ f̂ ŵ`. -/
lemma integral_load_ofUnit {L : ℝ} (hL : 0 < L) (q : ℝ → ℝ) (w : WeakH10) :
    ∫ x in (0 : ℝ)..L, q x * (WeakH10On.ofUnit hL w).toFun x =
      ∫ ξ in (0 : ℝ)..1, scaledLoad q L ξ * w.toFun ξ := by
  have h : ∀ x, q x * (WeakH10On.ofUnit hL w).toFun x =
      (scaledLoad q L (x / L) * w.toFun (x / L)) / L := by
    intro x
    change q x * w.toFun (x / L) = L * q (L * (x / L)) * w.toFun (x / L) / L
    rw [mul_div_cancel₀ x hL.ne']
    field_simp
  simp_rw [h]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_comp_div (fun ξ => scaledLoad q L ξ * w.toFun ξ) hL.ne',
    zero_div, div_self hL.ne', smul_eq_mul]
  field_simp

/-- For `0 < L`, if the rigidity `EA` is a.e. strongly measurable on `[0, L]`, the unit
diffusivity `κ ξ = EA (L ξ) / L` is a.e. strongly measurable on `[0, 1]`. -/
lemma aestronglyMeasurable_scaledRigidity {L : ℝ} (hL : 0 < L) {EA : ℝ → ℝ}
    (hEA : AEStronglyMeasurable EA (volume.restrict (Set.Icc 0 L))) :
    AEStronglyMeasurable (scaledRigidity EA L) (volume.restrict (Set.Icc 0 1)) := by
  have h1 : AEStronglyMeasurable EA (Measure.map (fun ξ : ℝ => L * ξ)
      (volume.restrict (Set.Icc 0 1))) := by
    rw [map_mul_restrict_Icc hL]
    exact hEA.smul_measure _
  exact (h1.comp_aemeasurable (measurable_const_mul L).aemeasurable).mul_const L⁻¹

/-- For `0 < L`, the rigidity bounds `EAmin ≤ EA ≤ EAmax` a.e. on `[0, L]` transport to
`EAmin / L ≤ κ ≤ EAmax / L` a.e. on `[0, 1]`. -/
lemma ae_bounds_scaledRigidity {L : ℝ} (hL : 0 < L) {EA : ℝ → ℝ} {EAmin EAmax : ℝ}
    (hEA : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 L)), EAmin ≤ EA x ∧ EA x ≤ EAmax) :
    ∀ᵐ ξ ∂(volume.restrict (Set.Icc 0 1)),
      EAmin / L ≤ scaledRigidity EA L ξ ∧ scaledRigidity EA L ξ ≤ EAmax / L := by
  have h1 : ∀ᵐ x ∂(Measure.map (fun ξ : ℝ => L * ξ) (volume.restrict (Set.Icc 0 1))),
      EAmin ≤ EA x ∧ EA x ≤ EAmax := by
    rw [map_mul_restrict_Icc hL]
    exact Measure.ae_smul_measure hEA _
  filter_upwards [ae_of_ae_map (measurable_const_mul L).aemeasurable h1] with ξ hξ
  exact ⟨div_le_div_of_nonneg_right hξ.1 hL.le, div_le_div_of_nonneg_right hξ.2 hL.le⟩

/-! ## C. Existence and uniqueness -/

/-- `u` is a weak solution of the fixed-fixed bar problem `-(EA u')' = q` on `[0, L]`:
`∫₀ᴸ EA u' v' = ∫₀ᴸ q v` for every `v ∈ H¹₀(0, L)`. -/
def IsWeakBarSolution {L : ℝ} (EA q : ℝ → ℝ) (u : WeakH10On L) : Prop :=
  ∀ v : WeakH10On L,
    ∫ x in (0 : ℝ)..L, EA x * u.weakDeriv x * v.weakDeriv x = ∫ x in (0 : ℝ)..L, q x * v.toFun x

/-- For `0 < L`, a weak solution `û` of the unit problem with `κ` and `f̂` gives the bar
solution `u x = û (x / L)`. -/
lemma isWeakBarSolution_ofUnit {L : ℝ} (hL : 0 < L) {EA q : ℝ → ℝ} {w : WeakH10}
    (hw : ∀ v : WeakH10,
      ∫ ξ in (0 : ℝ)..1, scaledRigidity EA L ξ * w.weakDeriv ξ * v.weakDeriv ξ =
        ∫ ξ in (0 : ℝ)..1, scaledLoad q L ξ * v.toFun ξ) :
    IsWeakBarSolution EA q (WeakH10On.ofUnit hL w) := by
  intro v
  obtain ⟨-, h2⟩ := WeakH10On.ofUnit_toUnit hL v
  calc ∫ x in (0 : ℝ)..L, EA x * (WeakH10On.ofUnit hL w).weakDeriv x * v.weakDeriv x
      = ∫ x in (0 : ℝ)..L, EA x * (WeakH10On.ofUnit hL w).weakDeriv x *
          (WeakH10On.ofUnit hL (v.toUnit hL)).weakDeriv x := by rw [h2]
    _ = ∫ ξ in (0 : ℝ)..1, scaledRigidity EA L ξ * w.weakDeriv ξ * (v.toUnit hL).weakDeriv ξ :=
        integral_rigidity_ofUnit hL EA w (v.toUnit hL)
    _ = ∫ ξ in (0 : ℝ)..1, scaledLoad q L ξ * (v.toUnit hL).toFun ξ := hw (v.toUnit hL)
    _ = ∫ x in (0 : ℝ)..L, q x * v.toFun x := integral_load_toUnit hL q v

/-- For `0 < L`, a bar solution pulled back to `[0, 1]` is a weak solution of the unit problem:
for every `v ∈ H¹₀(0, 1)`, `∫₀¹ κ(ξ) û'(ξ) v'(ξ) dξ = ∫₀¹ f̂(ξ) v(ξ) dξ`, with
`û'(ξ) = L u'(L ξ)`, `κ(ξ) = EA(L ξ) / L` and `f̂(ξ) = L q(L ξ)`. -/
lemma IsWeakBarSolution.toUnit {L : ℝ} (hL : 0 < L) {EA q : ℝ → ℝ} {u : WeakH10On L}
    (hu : IsWeakBarSolution EA q u) :
    ∀ v : WeakH10,
      ∫ ξ in (0 : ℝ)..1, scaledRigidity EA L ξ * (u.toUnit hL).weakDeriv ξ * v.weakDeriv ξ =
        ∫ ξ in (0 : ℝ)..1, scaledLoad q L ξ * v.toFun ξ := by
  intro v
  obtain ⟨-, h2⟩ := WeakH10On.toUnit_ofUnit hL v
  calc ∫ ξ in (0 : ℝ)..1, scaledRigidity EA L ξ * (u.toUnit hL).weakDeriv ξ * v.weakDeriv ξ
      = ∫ ξ in (0 : ℝ)..1, scaledRigidity EA L ξ * (u.toUnit hL).weakDeriv ξ *
          ((WeakH10On.ofUnit hL v).toUnit hL).weakDeriv ξ := by rw [h2]
    _ = ∫ x in (0 : ℝ)..L, EA x * u.weakDeriv x * (WeakH10On.ofUnit hL v).weakDeriv x :=
        integral_rigidity_toUnit hL EA u (WeakH10On.ofUnit hL v)
    _ = ∫ x in (0 : ℝ)..L, q x * (WeakH10On.ofUnit hL v).toFun x := hu (WeakH10On.ofUnit hL v)
    _ = ∫ ξ in (0 : ℝ)..1, scaledLoad q L ξ * v.toFun ξ := integral_load_ofUnit hL q v

/-- **Variable-rigidity weak Dirichlet bar.** For `L > 0`, `EA` a.e. strongly measurable with
`0 < EAmin ≤ EA ≤ EAmax` a.e. on `[0, L]` and `q ∈ L²(0, L)`, a weak solution exists, and every
weak solution has the same displacement values on `[0, L]`. -/
lemma weakBar_exists_unique {L : ℝ} (hL : 0 < L) {EA q : ℝ → ℝ} {EAmin EAmax : ℝ}
    (hEAmin : 0 < EAmin) (hEA_meas : AEStronglyMeasurable EA (volume.restrict (Set.Icc 0 L)))
    (hEA : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 L)), EAmin ≤ EA x ∧ EA x ≤ EAmax)
    (hq : MemLp q 2 (volume.restrict (Set.Icc 0 L))) :
    ∃ u : WeakH10On L, IsWeakBarSolution EA q u ∧
      ∀ u' : WeakH10On L, IsWeakBarSolution EA q u' → Set.EqOn u'.toFun u.toFun (Set.Icc 0 L) := by
  obtain ⟨w, hw, huniq⟩ := weak_diffusion_exists_unique (κ := scaledRigidity EA L)
    (f := scaledLoad q L) (kmin := EAmin / L) (kmax := EAmax / L) (div_pos hEAmin hL)
    (aestronglyMeasurable_scaledRigidity hL hEA_meas) (ae_bounds_scaledRigidity hL hEA)
    (memLp_scale_toUnit hL hq)
  refine ⟨WeakH10On.ofUnit hL w, isWeakBarSolution_ofUnit hL hw, fun u' hu' x hx => ?_⟩
  have hxL : x / L ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg hx.1 hL.le, (div_le_one hL).2 hx.2⟩
  have h := huniq (u'.toUnit hL) (hu'.toUnit hL) hxL
  change u'.toFun (L * (x / L)) = w.toFun (x / L) at h
  rw [mul_div_cancel₀ x hL.ne'] at h
  exact h

/-! ## D. Validation examples -/

/-- The derivative of `t ↦ c * (t - t ^ 2)` is `c * (1 - 2 * t)`. -/
private lemma hasDerivAt_const_mul_sub_sq (c t : ℝ) :
    HasDerivAt (fun t : ℝ => c * (t - t ^ 2)) (c * (1 - 2 * t)) t :=
  (((hasDerivAt_id' t).sub (hasDerivAt_pow 2 t)).const_mul c).congr_deriv (by norm_num)

/-- The quadratic `c ξ (1 - ξ)` as a `WeakH10` element, with weak derivative `c (1 - 2 ξ)`. -/
private noncomputable def quadUnit (c : ℝ) : WeakH10 where
  toFun ξ := c * (ξ * (1 - ξ))
  weakDeriv ξ := c * (1 - 2 * ξ)
  weakDeriv_memLp := by
    refine MemLp.of_bound
      (by fun_prop : Continuous fun ξ : ℝ => c * (1 - 2 * ξ)).aestronglyMeasurable (|c| * 3) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with ξ hξ
    rw [Real.norm_eq_abs, abs_mul]
    gcongr
    rw [abs_le]
    constructor <;> linarith [hξ.1, hξ.2]
  toFun_eq_integral := by
    intro x _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_const_mul_sub_sq c t)
      ((by fun_prop : Continuous fun t : ℝ => c * (1 - 2 * t)).intervalIntegrable _ _)]
    ring
  integral_weakDeriv_eq_zero := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_const_mul_sub_sq c t)
      ((by fun_prop : Continuous fun t : ℝ => c * (1 - 2 * t)).intervalIntegrable _ _)]
    ring

/-- `∫₀¹ ξ (1 - ξ) = 1 / 6`. -/
private lemma integral_mul_one_sub : ∫ ξ in (0 : ℝ)..1, ξ * (1 - ξ) = 1 / 6 := by
  have h : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => t ^ 2 / 2 - t ^ 3 / 3)
      (t * (1 - t)) t := by
    intro t _
    exact (((hasDerivAt_pow 2 t).div_const 2).sub ((hasDerivAt_pow 3 t).div_const 3)).congr_deriv
      (by norm_num; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((by fun_prop : Continuous fun t : ℝ => t * (1 - t)).intervalIntegrable _ _)]
  norm_num

/-- Constant rigidity recovers the classical bar: for `0 < L`, every weak solution with
constant `EA > 0` and uniform load `q` equals `q x (L - x) / (2 EA)` on `[0, L]`. -/
lemma IsWeakBarSolution.eqOn_axialDisplacement {L EA q : ℝ} (hL : 0 < L) (hEA : 0 < EA)
    {u : WeakH10On L} (hu : IsWeakBarSolution (fun _ => EA) (fun _ => q) u) :
    Set.EqOn u.toFun (axialDisplacement EA L q) (Set.Icc 0 L) := by
  have hL0 := hL.ne'
  have hEA0 := hEA.ne'
  have hv1 : ∀ v : WeakH10, IntervalIntegrable v.weakDeriv volume 0 1 := fun v =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2
      (v.weakDeriv_memLp.integrable one_le_two)
  have hw : ∀ v : WeakH10,
      ∫ ξ in (0 : ℝ)..1, scaledRigidity (fun _ => EA) L ξ *
          (quadUnit (q * L ^ 2 / (2 * EA))).weakDeriv ξ * v.weakDeriv ξ =
        ∫ ξ in (0 : ℝ)..1, scaledLoad (fun _ => q) L ξ * v.toFun ξ := by
    intro v
    have hibp := weak_diffusion_ibp (f := fun _ => (-2 : ℝ)) (memLp_const _) v
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hibp
    have hcont : ContinuousOn (fun x : ℝ => x * -2) (Set.uIcc 0 1) := by fun_prop
    have hint2 : IntervalIntegrable (fun x => x * -2 * v.weakDeriv x) volume 0 1 :=
      (hv1 v).continuousOn_mul hcont
    have e : ∀ ξ, scaledRigidity (fun _ => EA) L ξ * (quadUnit (q * L ^ 2 / (2 * EA))).weakDeriv ξ *
        v.weakDeriv ξ = (q * L / 2) * v.weakDeriv ξ + (q * L / 2) * (ξ * -2 * v.weakDeriv ξ) := by
      intro ξ
      change EA / L * (q * L ^ 2 / (2 * EA) * (1 - 2 * ξ)) * v.weakDeriv ξ = _
      field_simp
      ring
    have e2 : ∀ ξ, scaledLoad (fun _ => q) L ξ * v.toFun ξ = (-(q * L / 2)) * (-2 * v.toFun ξ) := by
      intro ξ
      change L * q * v.toFun ξ = _
      ring
    simp_rw [e, e2]
    rw [intervalIntegral.integral_add ((hv1 v).const_mul _) (hint2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, v.integral_weakDeriv_eq_zero, hibp]
    ring
  have hcl := isWeakBarSolution_ofUnit hL hw
  obtain ⟨u₀, -, huniq⟩ := weakBar_exists_unique hL (EA := fun _ => EA) (q := fun _ => q)
    (EAmin := EA) (EAmax := EA) hEA aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩) (memLp_const q)
  intro x hx
  rw [huniq u hu hx, ← huniq _ hcl hx]
  change q * L ^ 2 / (2 * EA) * (x / L * (1 - x / L)) = axialDisplacement EA L q x
  unfold axialDisplacement
  field_simp

/-- A two-valued rigidity: `EA₁` on `x < a` and `EA₂` on `x ≥ a`, for any real `EA₁` and `EA₂`;
it is positive when both values are positive. -/
noncomputable def stepRigidity (EA₁ EA₂ a x : ℝ) : ℝ :=
  if x < a then EA₁ else EA₂

/-- A positive piecewise constant rigidity is admissible on `[0, L]`: for `EA₁ > 0`, `EA₂ > 0`
and every `a` and `L`, `stepRigidity EA₁ EA₂ a` is a.e. strongly measurable on `[0, L]` and lies
a.e. on `[0, L]` between `min EA₁ EA₂ > 0` and `max EA₁ EA₂`. -/
lemma stepRigidity_admissible {EA₁ EA₂ : ℝ} (hEA₁ : 0 < EA₁) (hEA₂ : 0 < EA₂) (a L : ℝ) :
    0 < min EA₁ EA₂ ∧
      AEStronglyMeasurable (stepRigidity EA₁ EA₂ a) (volume.restrict (Set.Icc 0 L)) ∧
      ∀ᵐ x ∂(volume.restrict (Set.Icc 0 L)),
        min EA₁ EA₂ ≤ stepRigidity EA₁ EA₂ a x ∧ stepRigidity EA₁ EA₂ a x ≤ max EA₁ EA₂ := by
  refine ⟨lt_min hEA₁ hEA₂, ?_, Filter.Eventually.of_forall fun x => ?_⟩
  · exact (Measurable.ite measurableSet_Iio measurable_const measurable_const).aestronglyMeasurable
  · unfold stepRigidity
    split_ifs
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
    · exact ⟨min_le_right _ _, le_max_right _ _⟩

/-- Zero rigidity is not admissible: for `0 < L`, under the unit load the weak bar problem on
`[0, L]` has no solution. -/
lemma not_isWeakBarSolution_zero_rigidity {L : ℝ} (hL : 0 < L) (u : WeakH10On L) :
    ¬ IsWeakBarSolution (fun _ => 0) (fun _ => 1) u := by
  intro h
  have h1 := h (WeakH10On.ofUnit hL (quadUnit 1))
  rw [integral_load_ofUnit hL (fun _ => 1) (quadUnit 1)] at h1
  simp only [zero_mul, intervalIntegral.integral_zero] at h1
  have h2 :
      ∫ ξ in (0 : ℝ)..1, scaledLoad (fun _ => (1 : ℝ)) L ξ * (quadUnit 1).toFun ξ = L / 6 := by
    have e : ∀ ξ, scaledLoad (fun _ => (1 : ℝ)) L ξ * (quadUnit 1).toFun ξ = L * (ξ * (1 - ξ)) := by
      intro ξ
      change L * 1 * (1 * (ξ * (1 - ξ))) = _
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_mul_one_sub]
    ring
  rw [h2] at h1
  linarith

/-- For `0 < L`, a rigidity that is nonpositive on `[0, L]` has no positive a.e. lower bound
there. -/
lemma not_ae_lowerBound_of_nonpos {L : ℝ} (hL : 0 < L) {EA : ℝ → ℝ}
    (hEA : ∀ x ∈ Set.Icc (0 : ℝ) L, EA x ≤ 0) {EAmin EAmax : ℝ} (hEAmin : 0 < EAmin) :
    ¬ ∀ᵐ x ∂(volume.restrict (Set.Icc 0 L)), EAmin ≤ EA x ∧ EA x ≤ EAmax := by
  intro h
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) L)), False := by
    filter_upwards [h, ae_restrict_mem measurableSet_Icc] with x hx hmem
    linarith [hEA x hmem, hx.1]
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero, Real.volume_Icc,
    ENNReal.ofReal_eq_zero] at hae
  linarith

/-- A traction end is not covered: for `0 < L` and `0 < EA`, the fixed-free displacement
`q x (2 L - x) / (2 EA)` with `q ≠ 0` does not vanish at `x = L`, so no element of `H¹₀(0, L)`
represents it. -/
lemma not_exists_weakH10On_eqOn_fixedFree {L EA q : ℝ} (hL : 0 < L) (hEA : 0 < EA) (hq : q ≠ 0) :
    ¬ ∃ v : WeakH10On L, Set.EqOn v.toFun (fixedFreeDisplacement EA L q) (Set.Icc 0 L) := by
  rintro ⟨v, hv⟩
  have h1 := (v.toFun_zero_and_length hL.le).2
  rw [hv ⟨hL.le, le_rfl⟩] at h1
  unfold fixedFreeDisplacement at h1
  have : q * L ^ 2 = 0 := by
    field_simp at h1
    nlinarith
  rcases mul_eq_zero.mp this with h | h
  · exact hq h
  · exact hL.ne' (pow_eq_zero_iff two_ne_zero |>.mp h)

section VirtualWork

open scoped Matrix
open ControlVolumes
open MathlibExt.Probability.FokkerPlanck (divergence)

/-! ## E. Stress divergence and face works -/

/-- The divergence of a stress field, row by row: `(div σ)ᵢ = ∑ⱼ ∂ⱼ σᵢⱼ`. -/
noncomputable def stressDivergence (σ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => divergence (fun y => σ y i) x

/-- Virtual work of the traction on the upper face `x i = b i` of the box, outward normal
`+eᵢ`. -/
noncomputable def upperFaceWork (a b : Fin 3 → ℝ) (σ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (v : (Fin 3 → ℝ) → Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
    traction (σ (i.insertNth (b i) y)) (Pi.single i 1) ⬝ᵥ v (i.insertNth (b i) y)

/-- Virtual work of the traction on the lower face `x i = a i` of the box, outward normal
`-eᵢ`. -/
noncomputable def lowerFaceWork (a b : Fin 3 → ℝ) (σ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (v : (Fin 3 → ℝ) → Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
    traction (σ (i.insertNth (a i) y)) (-Pi.single i 1) ⬝ᵥ v (i.insertNth (a i) y)

/-- The virtual work of the boundary tractions, summed over the six faces. -/
noncomputable def boxTractionWork (a b : Fin 3 → ℝ) (σ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (v : (Fin 3 → ℝ) → Fin 3 → ℝ) : ℝ :=
  ∑ i, (upperFaceWork a b σ v i + lowerFaceWork a b σ v i)

/-- The traction on the face normal `eⱼ`, dotted with `w`: `(σ eⱼ) · w = (σᵀ w)ⱼ`. -/
private lemma traction_single_dotProduct (M : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ)
    (j : Fin 3) : traction M (Pi.single j 1) ⬝ᵥ w = (Mᵀ *ᵥ w) j := by
  simp [traction, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The traction on the face normal `-eⱼ`, dotted with `w`: `(σ (-eⱼ)) · w = -(σᵀ w)ⱼ`. -/
private lemma traction_neg_single_dotProduct (M : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ)
    (j : Fin 3) : traction M (-Pi.single j 1) ⬝ᵥ w = -(Mᵀ *ᵥ w) j := by
  rw [← traction_single_dotProduct]
  simp [traction, Matrix.mulVec_neg]

/-- The `j`-th component of `σᵀ v` as a sum: `(σᵀ v)ⱼ = ∑ᵢ σᵢⱼ vᵢ`. -/
private lemma fun_transpose_mulVec_apply (σ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (v : (Fin 3 → ℝ) → Fin 3 → ℝ) (j : Fin 3) :
    (fun y => ((σ y)ᵀ *ᵥ v y) j) = fun y => ∑ i, σ y i j * v y i := by
  funext y
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

/-- At a point of an open set where `v` is `C¹`, the displacement gradient is the Fréchet
derivative: `(∇v)ᵢⱼ = (Dv(x) eⱼ)ᵢ`. -/
private lemma displacementGradient_eq_fderiv {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    {v : (Fin 3 → ℝ) → Fin 3 → ℝ} (hv : ContDiffOn ℝ 1 v U) {x : Fin 3 → ℝ} (hx : x ∈ U)
    (i j : Fin 3) : displacementGradient v x i j = fderiv ℝ v x (Pi.single j 1) i := by
  have hvd : HasFDerivAt v (fderiv ℝ v x) x :=
    (((hv.differentiableOn (by norm_num)) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => x + t • Pi.single j (1 : ℝ)) (Pi.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j (1 : ℝ))).const_add x
  have hx0 : x + (0 : ℝ) • Pi.single j (1 : ℝ) = x := by simp
  have hvi : HasFDerivAt (fun y => v y i) (ContinuousLinearMap.proj i ∘L fderiv ℝ v x)
      (x + (0 : ℝ) • Pi.single j (1 : ℝ)) := by
    rw [hx0]
    exact hasFDerivAt_pi'.1 hvd i
  exact (hvi.comp_hasDerivAt (0 : ℝ) hline).deriv

/-- The face sum is the outward flux of `σᵀ v` through the box. -/
lemma boxTractionWork_eq_boxOutwardFlux (a b : Fin 3 → ℝ)
    (σ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (v : (Fin 3 → ℝ) → Fin 3 → ℝ) :
    boxTractionWork a b σ v = boxOutwardFlux a b (fun y => (σ y)ᵀ *ᵥ v y) := by
  unfold boxTractionWork boxOutwardFlux upperFaceWork lowerFaceWork
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [traction_single_dotProduct, traction_neg_single_dotProduct, integral_neg]
  ring

/-- Product rule: `div (σᵀ v) = (div σ) · v + σ : ∇v` at every point of an open set where the
components of `σ` and `v` are `C¹`. -/
lemma divergence_transpose_mulVec {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    {σ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {v : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hσ : ∀ i j, ContDiffOn ℝ 1 (fun x => σ x i j) U) (hv : ContDiffOn ℝ 1 v U)
    {x : Fin 3 → ℝ} (hx : x ∈ U) :
    divergence (fun y => (σ y)ᵀ *ᵥ v y) x =
      stressDivergence σ x ⬝ᵥ v x + ∑ i, ∑ j, σ x i j * displacementGradient v x i j := by
  have hσd : ∀ i j, HasFDerivAt (fun y => σ y i j) (fderiv ℝ (fun y => σ y i j) x) x :=
    fun i j =>
      ((((hσ i j).differentiableOn (by norm_num)) x hx).differentiableAt
        (hU.mem_nhds hx)).hasFDerivAt
  have hvd : HasFDerivAt v (fderiv ℝ v x) x :=
    (((hv.differentiableOn (by norm_num)) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hvi : ∀ i, HasFDerivAt (fun y => v y i) (ContinuousLinearMap.proj i ∘L fderiv ℝ v x) x :=
    fun i => hasFDerivAt_pi'.1 hvd i
  have hFj : ∀ j, fderiv ℝ (fun y => ((σ y)ᵀ *ᵥ v y) j) x (Pi.single j 1) =
      ∑ i, (σ x i j * fderiv ℝ v x (Pi.single j 1) i +
        v x i * fderiv ℝ (fun y => σ y i j) x (Pi.single j 1)) := by
    intro j
    have h := HasFDerivAt.fun_sum (u := Finset.univ) (A := fun i y => σ y i j * v y i)
      (fun i _ => (hσd i j).fun_mul (hvi i))
    rw [fun_transpose_mulVec_apply σ v j, h.fderiv]
    simp
  simp only [divergence, MathlibExt.Probability.FokkerPlanck.pderiv, stressDivergence, hFj,
    displacementGradient_eq_fderiv hU hv hx, dotProduct, Fin.sum_univ_three]
  ring

/-- A symmetric stress does no work on the skew part of a gradient: `σ : H = σ : ε(H)`. -/
lemma doubleDot_eq_doubleDot_smallStrain {σ : Matrix (Fin 3) (Fin 3) ℝ}
    (hσ : IsSymmetricStress σ) (H : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ i, ∑ j, σ i j * H i j = ∑ i, ∑ j, σ i j * smallStrain H i j := by
  have h : ∀ i j, σ j i = σ i j := fun i j => congrFun (congrFun hσ i) j
  simp only [smallStrain_apply, Fin.sum_univ_three]
  rw [h 1 0, h 2 0, h 2 1]
  ring

/-! ## F. The virtual work identity -/

/-- **Virtual work on a box.** For a nondegenerate box, a stress `C¹` on an open neighbourhood
`U` of the box and symmetric on it, a `C¹` virtual displacement `v` on `U` and the equilibrium
equations `div σ + body = 0` on the box,
`∫ σ : ε(v) = ∫ body · v + ∑_faces ∫ (σ n) · v`. -/
lemma virtualWork_box {a b : Fin 3 → ℝ} (hab : ∀ i, a i < b i) {U : Set (Fin 3 → ℝ)}
    (hU : IsOpen U) (hbox : Set.Icc a b ⊆ U) {σ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    {v body : (Fin 3 → ℝ) → Fin 3 → ℝ} (hσ : ∀ i j, ContDiffOn ℝ 1 (fun x => σ x i j) U)
    (hsymm : ∀ x ∈ Set.Icc a b, IsSymmetricStress (σ x)) (hv : ContDiffOn ℝ 1 v U)
    (heq : ∀ x ∈ Set.Icc a b, stressDivergence σ x + body x = 0) :
    ∫ x in Set.Icc a b, ∑ i, ∑ j, σ x i j * smallStrain (displacementGradient v x) i j =
      (∫ x in Set.Icc a b, body x ⬝ᵥ v x) + boxTractionWork a b σ v := by
  have hF : ContDiffOn ℝ 1 (fun y => (σ y)ᵀ *ᵥ v y) U := by
    refine contDiffOn_pi.2 fun j => ?_
    rw [fun_transpose_mulVec_apply σ v j]
    exact ContDiffOn.sum fun i _ => (hσ i j).mul (contDiffOn_pi.1 hv i)
  have hdiv := integral_divergence_box hab hU hbox hF
  rw [← boxTractionWork_eq_boxOutwardFlux] at hdiv
  have hpt : ∀ x ∈ Set.Icc a b, divergence (fun y => (σ y)ᵀ *ᵥ v y) x =
      ∑ i, ∑ j, σ x i j * smallStrain (displacementGradient v x) i j - body x ⬝ᵥ v x := by
    intro x hx
    rw [divergence_transpose_mulVec hU hσ hv (hbox hx),
      doubleDot_eq_doubleDot_smallStrain (hsymm x hx), eq_neg_of_add_eq_zero_left (heq x hx)]
    simp only [neg_dotProduct]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc hpt] at hdiv
  have hcv : ContinuousOn (fderiv ℝ v) U := hv.continuousOn_fderiv_of_isOpen hU le_rfl
  have hcσ : ∀ i j, ContinuousOn (fderiv ℝ (fun y => σ y i j)) U :=
    fun i j => (hσ i j).continuousOn_fderiv_of_isOpen hU le_rfl
  have hgradc : ∀ i j, ContinuousOn (fun x => fderiv ℝ v x (Pi.single j 1) i) U :=
    fun i j => (continuous_apply i).comp_continuousOn (hcv.clm_apply continuousOn_const)
  have hint1 : IntegrableOn
      (fun x => ∑ i, ∑ j, σ x i j * smallStrain (displacementGradient v x) i j) (Set.Icc a b) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    have hc : ContinuousOn (fun x => ∑ i, ∑ j, σ x i j *
        ((fderiv ℝ v x (Pi.single j 1) i + fderiv ℝ v x (Pi.single i 1) j) / 2)) (Set.Icc a b) := by
      refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
      exact (((hσ i j).continuousOn).mul (((hgradc i j).add (hgradc j i)).div_const 2)).mono hbox
    refine hc.congr fun x hx => ?_
    simp only [smallStrain_apply, displacementGradient_eq_fderiv hU hv (hbox hx)]
  have hint2 : IntegrableOn (fun x => body x ⬝ᵥ v x) (Set.Icc a b) := by
    have hc : ContinuousOn (fun x => -(stressDivergence σ x ⬝ᵥ v x)) (Set.Icc a b) := by
      simp only [stressDivergence, divergence, MathlibExt.Probability.FokkerPlanck.pderiv,
        dotProduct]
      refine (continuousOn_finsetSum _ fun i _ => ?_).neg
      refine (continuousOn_finsetSum _ fun j _ => ?_).mul ?_
      · exact (((hcσ i j).clm_apply continuousOn_const)).mono hbox
      · exact ((contDiffOn_pi.1 hv i).continuousOn).mono hbox
    refine (hc.integrableOn_compact isCompact_Icc).congr_fun (fun x hx => ?_) measurableSet_Icc
    change -(stressDivergence σ x ⬝ᵥ v x) = body x ⬝ᵥ v x
    rw [eq_neg_of_add_eq_zero_left (heq x hx), neg_dotProduct, neg_neg]
  rw [integral_sub hint1 hint2] at hdiv
  linarith

/-! ## G. Clamped faces and rigid virtual displacements -/

/-- The upper face `x i = b i` does no work if `v` vanishes on it. -/
lemma upperFaceWork_eq_zero {a b : Fin 3 → ℝ} {σ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    {v : (Fin 3 → ℝ) → Fin 3 → ℝ} {i : Fin 3}
    (hv : ∀ y ∈ Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), v (i.insertNth (b i) y) = 0) :
    upperFaceWork a b σ v i = 0 := by
  unfold upperFaceWork
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (0 : ℝ))
    fun y hy => by simp only [hv y hy, dotProduct_zero]]
  simp

/-- The lower face `x i = a i` does no work if `v` vanishes on it. -/
lemma lowerFaceWork_eq_zero {a b : Fin 3 → ℝ} {σ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    {v : (Fin 3 → ℝ) → Fin 3 → ℝ} {i : Fin 3}
    (hv : ∀ y ∈ Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), v (i.insertNth (a i) y) = 0) :
    lowerFaceWork a b σ v i = 0 := by
  unfold lowerFaceWork
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (0 : ℝ))
    fun y hy => by simp only [hv y hy, dotProduct_zero]]
  simp

/-- Removing a clamped face: let the box `[a, b]` be nondegenerate (`a i < b i`) and contained in
an open set `U`, let the stress `σ` have components continuously differentiable on `U` and be
symmetric on the box, let `div σ + body = 0` on the box, and let the virtual displacement `v` be
continuously differentiable on `U`. If `v` vanishes on the lower face `x i₀ = a i₀`, then
`∫ σ : ε(v) = ∫ body · v` plus the traction work on the other five faces: the identity holds with
that face, and only that face, removed. -/
lemma virtualWork_box_of_lowerFace_eq_zero {a b : Fin 3 → ℝ} (hab : ∀ i, a i < b i)
    {U : Set (Fin 3 → ℝ)} (hU : IsOpen U) (hbox : Set.Icc a b ⊆ U)
    {σ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {v body : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hσ : ∀ i j, ContDiffOn ℝ 1 (fun x => σ x i j) U)
    (hsymm : ∀ x ∈ Set.Icc a b, IsSymmetricStress (σ x)) (hv : ContDiffOn ℝ 1 v U)
    (heq : ∀ x ∈ Set.Icc a b, stressDivergence σ x + body x = 0) (i₀ : Fin 3)
    (hclamp : ∀ y ∈ Set.Icc (a ∘ i₀.succAbove) (b ∘ i₀.succAbove), v (i₀.insertNth (a i₀) y) = 0) :
    ∫ x in Set.Icc a b, ∑ i, ∑ j, σ x i j * smallStrain (displacementGradient v x) i j =
      (∫ x in Set.Icc a b, body x ⬝ᵥ v x) + ∑ i, upperFaceWork a b σ v i +
        ∑ i ∈ Finset.univ.erase i₀, lowerFaceWork a b σ v i := by
  rw [virtualWork_box hab hU hbox hσ hsymm hv heq, boxTractionWork, Finset.sum_add_distrib,
    ← Finset.add_sum_erase Finset.univ (fun i => lowerFaceWork a b σ v i) (Finset.mem_univ i₀),
    lowerFaceWork_eq_zero hclamp, zero_add, add_assoc]

/-- Rigid virtual displacements do no work: let the box `[a, b]` be nondegenerate (`a i < b i`)
and contained in an open set `U`, let the stress `σ` have components continuously differentiable
on `U` and be symmetric on the box, and let `div σ + body = 0` on the box. A rigid virtual
displacement `v x = W x` with `Wᵀ = -W` does no internal work, so its external virtual work, the
body-force work `∫ body · v` plus the traction work on the six faces, vanishes. -/
lemma virtualWork_box_rigid {a b : Fin 3 → ℝ} (hab : ∀ i, a i < b i) {U : Set (Fin 3 → ℝ)}
    (hU : IsOpen U) (hbox : Set.Icc a b ⊆ U) {σ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    {body : (Fin 3 → ℝ) → Fin 3 → ℝ} (hσ : ∀ i j, ContDiffOn ℝ 1 (fun x => σ x i j) U)
    (hsymm : ∀ x ∈ Set.Icc a b, IsSymmetricStress (σ x))
    (heq : ∀ x ∈ Set.Icc a b, stressDivergence σ x + body x = 0)
    {W : Matrix (Fin 3) (Fin 3) ℝ} (hW : Wᵀ = -W) :
    (∫ x in Set.Icc a b, body x ⬝ᵥ (W *ᵥ x)) + boxTractionWork a b σ (fun x => W *ᵥ x) = 0 := by
  have hv : ContDiffOn ℝ 1 (fun x : Fin 3 → ℝ => W *ᵥ x) U := by
    refine (contDiff_pi.2 fun i => ?_).contDiffOn
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have h := virtualWork_box hab hU hbox hσ hsymm hv heq
  have h0 : ∀ x, smallStrain (displacementGradient (fun x => W *ᵥ x) x) = 0 :=
    fun x => smallStrain_rigid W x hW
  simp only [h0, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, integral_zero] at h
  linarith

/-! ## H. Validation of the virtual work identity -/

/-- The simple-shear stress `τ (e₀ e₁ᵀ + e₁ e₀ᵀ)`. -/
def simpleShearStress (τ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, τ, 0; τ, 0, 0; 0, 0, 0]

/-- The engineering shear factor: let `τ ≠ 0` and `γ ≠ 0`. For simple shear `u x = (γ x₁, 0, 0)`
under the shear stress `τ` the virtual work density is `σ : ε = τ γ`; contracting with the
engineering shear `γ₀₁ = 2 ε₀₁` in both off-diagonal slots gives `2 τ γ`, which differs from
`τ γ` since `τ γ ≠ 0`. -/
lemma simpleShear_engineering_double_count {τ γ : ℝ} (hτ : τ ≠ 0) (hγ : γ ≠ 0) (x : Fin 3 → ℝ) :
    ∑ i, ∑ j, simpleShearStress τ i j *
        smallStrain (displacementGradient (simpleShearField γ) x) i j = τ * γ ∧
      simpleShearStress τ 0 1 * engineeringShear (smallStrain (displacementGradient
          (simpleShearField γ) x)) +
        simpleShearStress τ 1 0 * engineeringShear (smallStrain (displacementGradient
          (simpleShearField γ) x)) = 2 * (τ * γ) ∧
      2 * (τ * γ) ≠ τ * γ := by
  rw [simpleShear_smallStrain]
  refine ⟨?_, ?_, ?_⟩
  · simp [simpleShearStress, Fin.sum_univ_three]
    ring
  · simp [simpleShearStress, engineeringShear]
    ring
  · intro h
    have : τ * γ = 0 := by linarith
    exact mul_ne_zero hτ hγ this

end VirtualWork

end Elasticity.WeakAndVirtualWork

end
