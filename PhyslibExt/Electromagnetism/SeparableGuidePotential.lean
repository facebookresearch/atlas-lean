/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Physlib.Electromagnetism.Kinematics.EMPotential
public import Physlib.Electromagnetism.Kinematics.ScalarPotential
public import Physlib.Electromagnetism.Kinematics.VectorPotential
public import Physlib.Electromagnetism.Kinematics.ElectricField
public import Physlib.Electromagnetism.Kinematics.MagneticField
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Separable guide potential

## i. Overview

A separable electromagnetic guide potential built from a
longitudinal profile and a time/transverse mode has vanishing
scalar potential, an explicitly computable vector potential,
and electric/magnetic fields given by the standard potential
formulas, against the canonical Physlib
`ElectromagneticPotential` API (imported, not copied).

## ii. Key results

- `separableGuidePotential_fields`: the electric and magnetic
  fields of the separable guide potential.
- `vectorPotential_separableGuidePotential`: the vector
  potential in components.

## iii. Table of contents

- A. The separable guide potential

## iv. References

- J. D. Jackson, *Classical Electrodynamics*, third edition,
  Wiley, 1998: electromagnetic potentials and guided waves.

## A. The separable guide potential
-/

@[expose] public section

open scoped ContDiff
open SpaceTime _root_.Electromagnetism

namespace PhyslibExt.Electromagnetism.SeparableGuidePotential

open _root_.Electromagnetism

/-- The separable guide potential `A_y = a(x) f(t, z)`, `A_x = A_z = φ = 0`, as a Physlib
electromagnetic potential. It is built with the canonical constructor `ofVectorPotential c`,
whose `timeSlice c` reads the spacetime time coordinate `x⁰` as the physical time `x⁰ / c`. -/
noncomputable def separableGuidePotential (c : SpeedOfLight) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    ElectromagneticPotential :=
  ElectromagneticPotential.ofVectorPotential c (fun t p => WithLp.toLp 2 ![0, a (p 0) * f t.val (p 2), 0])

/-- The time-coordinate/speed-of-light conversion, explicitly: at a spacetime point `x` the
potential has `A^y(x) = a(x¹) f(x⁰ / c, x³)` and every other component zero. -/
lemma separableGuidePotential_apply (c : SpeedOfLight) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (x : SpaceTime) (μ : Fin 1 ⊕ Fin 3) :
    separableGuidePotential c a f x μ =
      if μ = Sum.inr 1 then a (x (Sum.inr 0)) * f (x (Sum.inl 0) / c) (x (Sum.inr 2)) else 0 := by
  rcases μ with μ | μ <;> fin_cases μ <;> rfl

open SpaceTime in
private lemma symm_apply (c : SpeedOfLight) (t : Time) (p : Space) (μ : Fin 1 ⊕ Fin 3) :
    (toTimeAndSpace c).symm (t, p) μ = Sum.elim (fun _ => c * t.val) p μ := by
  rcases μ with _ | _ <;> rfl

private lemma timeSlice_apply {M : Type} (c : SpeedOfLight) (g : SpaceTime → M) (t : Time)
    (p : Space) : SpaceTime.timeSlice c g t p = g ((SpaceTime.toTimeAndSpace c).symm (t, p)) := rfl

/-- `φ = 0`. -/
lemma scalarPotential_separableGuidePotential (c : SpeedOfLight) (a : ℝ → ℝ)
    (f : ℝ → ℝ → ℝ) :
    (separableGuidePotential c a f).scalarPotential c = 0 := by
  funext t p
  simp [ElectromagneticPotential.scalarPotential, timeSlice_apply, separableGuidePotential_apply]

/-- `A = (0, a(x) f(t, z), 0)` in physical time `t`. -/
lemma vectorPotential_separableGuidePotential (c : SpeedOfLight) (a : ℝ → ℝ)
    (f : ℝ → ℝ → ℝ) (t : Time) (p : Space) :
    (separableGuidePotential c a f).vectorPotential c t p =
      WithLp.toLp 2 ![0, a (p 0) * f t.val (p 2), 0] := by
  ext i
  fin_cases i <;> simp [ElectromagneticPotential.vectorPotential, timeSlice_apply,
    separableGuidePotential_apply, symm_apply, c.pos.ne']

private lemma basis_apply (μ j : Fin 3) : (Space.basis μ : Space) j = if j = μ then 1 else 0 := by
  rw [← Space.basis.repr_symm_single]
  exact PiLp.single_apply (p := 2) (i := μ) (a := (1 : ℝ)) (j := j)

/-- Coordinate projection on `Space`. -/
private noncomputable def coord (i : Fin 3) : Space →L[ℝ] ℝ :=
  LinearMap.mkContinuous ⟨⟨fun p => p i, fun _ _ => rfl⟩, fun _ _ => rfl⟩ 1 fun p => by
    rw [one_mul]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => p j ^ 2)
      (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i))

@[simp] private lemma coord_apply (i : Fin 3) (p : Space) : coord i p = p i := rfl

/-- The time coordinate as a continuous linear map. -/
private noncomputable def timeCoord : Time →L[ℝ] ℝ :=
  LinearMap.mkContinuous ⟨⟨Time.val, fun _ _ => rfl⟩, fun _ _ => rfl⟩ 1 fun t => by
    rw [one_mul]; rfl

@[simp] private lemma timeCoord_apply (t : Time) : timeCoord t = t.val := rfl

@[simp] private lemma time_one_val : (1 : Time).val = 1 := Nat.cast_one

private lemma space_deriv_mul (a F : ℝ → ℝ) (p : Space) (ha : DifferentiableAt ℝ a (p 0))
    (hF : DifferentiableAt ℝ F (p 2)) (μ : Fin 3) :
    Space.deriv μ (fun q : Space => a (q 0) * F (q 2)) p =
      a (p 0) * (deriv F (p 2) * if 2 = μ then 1 else 0) +
        F (p 2) * (deriv a (p 0) * if 0 = μ then 1 else 0) := by
  have h : HasFDerivAt (fun q : Space => a (q 0) * F (q 2)) _ p :=
    (ha.hasDerivAt.comp_hasFDerivAt p (coord 0).hasFDerivAt).mul
      (hF.hasDerivAt.comp_hasFDerivAt p (coord 2).hasFDerivAt)
  simp [Space.deriv, h.fderiv, basis_apply]

private lemma electricField_of (c : SpeedOfLight) (A : ElectromagneticPotential) (t : Time)
    (p : Space) (g : ℝ → ℝ) (g' : ℝ) (hφ : A.scalarPotential c = 0)
    (hA : ∀ s, A.vectorPotential c s p = WithLp.toLp 2 ![0, g s.val, 0])
    (hg : HasDerivAt g g' t.val) :
    A.electricField c t p = WithLp.toLp 2 ![0, -g', 0] := by
  have e : (fun s => A.vectorPotential c s p) =
      fun s => g (timeCoord s) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
    funext s; rw [hA]; ext i; fin_cases i <;> simp
  have h : HasFDerivAt (fun s => g (timeCoord s) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) _ t :=
    (hg.comp_hasFDerivAt (x := t) timeCoord.hasFDerivAt).smul_const _
  simp only [ElectromagneticPotential.electricField, Time.deriv, hφ, e]
  rw [h.fderiv]
  ext i; fin_cases i <;> simp [Space.grad, Space.deriv]

private lemma diff_t {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ ∞ (Function.uncurry f)) (z : ℝ) :
    Differentiable ℝ (fun s => f s z) :=
  (hf.differentiable (by simp)).comp (differentiable_id.prodMk (differentiable_const z))

private lemma diff_z {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ ∞ (Function.uncurry f)) (t : ℝ) :
    Differentiable ℝ (f t) :=
  (hf.differentiable (by simp)).comp ((differentiable_const t).prodMk differentiable_id)

/-- `E = (0, -a f_t, 0)`. -/
lemma electricField_separableGuidePotential (c : SpeedOfLight) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (t : Time) (p : Space) {ft : ℝ} (hf : HasDerivAt (fun s => f s (p 2)) ft t.val) :
    (separableGuidePotential c a f).electricField c t p =
      WithLp.toLp 2 ![0, -(a (p 0) * deriv (fun s => f s (p 2)) t.val), 0] := by
  rw [hf.deriv]
  exact electricField_of c _ t p _ _ (scalarPotential_separableGuidePotential c a f)
    (fun s => vectorPotential_separableGuidePotential c a f s p) (hf.const_mul (a (p 0)))

private lemma space_deriv_zero (μ : Fin 3) (p : Space) :
    Space.deriv μ (fun _ : Space => (0 : ℝ)) p = 0 := by
  simp [Space.deriv]

/-- `B = (-a f_z, 0, a' f)`. -/
lemma magneticField_separableGuidePotential (c : SpeedOfLight) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (t : Time) (p : Space) (ha : DifferentiableAt ℝ a (p 0))
    (hf : DifferentiableAt ℝ (f t.val) (p 2)) :
    (separableGuidePotential c a f).magneticField c t p =
      WithLp.toLp 2 ![-(a (p 0) * deriv (f t.val) (p 2)), 0, deriv a (p 0) * f t.val (p 2)] := by
  have e : (separableGuidePotential c a f).vectorPotential c t =
      fun q => WithLp.toLp 2 ![0, a (q 0) * f t.val (q 2), 0] :=
    funext (vectorPotential_separableGuidePotential c a f t)
  have hd := space_deriv_mul a (f t.val) p ha hf
  ext i; fin_cases i <;> simp [ElectromagneticPotential.magneticField, e, Space.curl, hd, space_deriv_zero,
    mul_comm]

/-- The Euclidean identification of `Lorentz.Vector` as a continuous linear equivalence. -/
private noncomputable def ev : Lorentz.Vector 3 ≃L[ℝ] EuclideanSpace ℝ (Fin 1 ⊕ Fin 3) :=
  (Lorentz.Vector.equivEuclid 3).toContinuousLinearEquiv

/-- A spacetime coordinate as a continuous linear map. -/
private noncomputable def stc (μ : Fin 1 ⊕ Fin 3) : SpaceTime →L[ℝ] ℝ :=
  (EuclideanSpace.proj μ).comp ev.toContinuousLinearMap

/-- The potential is `C^∞` on spacetime (premise `hA` of Physlib's `IsExtrema` equivalences). -/
lemma contDiff_separableGuidePotential (c : SpeedOfLight) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (separableGuidePotential c a f) := by
  have h : ∀ μ, ContDiff ℝ ∞ fun x : SpaceTime => ev (separableGuidePotential c a f x) μ := by
    intro μ
    change ContDiff ℝ ∞ fun x => separableGuidePotential c a f x μ
    simp only [separableGuidePotential_apply]
    split_ifs
    · exact (ha.comp (stc _).contDiff).mul
        (hf.comp (((stc _).contDiff.div_const _).prodMk (stc _).contDiff))
    · exact contDiff_const
  simpa [Function.comp_def] using ev.symm.contDiff.comp ((contDiff_piLp 2).2 h)

/-- **Fields of the separable guide potential.** For `C^∞` `a` and `f` and any speed of light
`c`, the potential `A_y = a(x) f(t, z)`, `A_x = A_z = φ = 0` (with `t = x⁰ / c`) has
`E = (0, -a f_t, 0)` and `B = (-a f_z, 0, a' f)`, and the potential is `C^∞`. -/
lemma separableGuidePotential_fields (c : SpeedOfLight) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    (∀ t p, (separableGuidePotential c a f).electricField c t p =
      WithLp.toLp 2 ![0, -(a (p 0) * deriv (fun s => f s (p 2)) t.val), 0]) ∧
    (∀ t p, (separableGuidePotential c a f).magneticField c t p =
      WithLp.toLp 2 ![-(a (p 0) * deriv (f t.val) (p 2)), 0, deriv a (p 0) * f t.val (p 2)]) ∧
    ContDiff ℝ ∞ (separableGuidePotential c a f) := by
  exact ⟨fun t p => electricField_separableGuidePotential c a f t p (diff_t hf _ _).hasDerivAt,
    fun t p => magneticField_separableGuidePotential c a f t p (ha.differentiable (by simp) _)
      (diff_z hf _ _),
    contDiff_separableGuidePotential c a f ha hf⟩

/-! ### Validation: sinusoidal `a`, time-space `f` -/

/-- `a(x) = sin x`, `f(t, z) = cos (2 t - 3 z)`. -/
noncomputable def sinusoidalGuidePotential (c : SpeedOfLight) : ElectromagneticPotential :=
  separableGuidePotential c Real.sin (fun t z => Real.cos (2 * t - 3 * z))

private lemma contDiff_cos_wave :
    ContDiff ℝ ∞ (Function.uncurry fun t z : ℝ => Real.cos (2 * t - 3 * z)) :=
  Real.contDiff_cos.comp ((contDiff_const.mul contDiff_fst).sub (contDiff_const.mul contDiff_snd))

private lemma deriv_wave_t (t z : ℝ) :
    deriv (fun s => Real.cos (2 * s - 3 * z)) t = -(2 * Real.sin (2 * t - 3 * z)) := by
  rw [(((hasDerivAt_id' t).const_mul 2).sub_const (3 * z)).cos.deriv]; ring

private lemma deriv_wave_z (t z : ℝ) :
    deriv (fun w => Real.cos (2 * t - 3 * w)) z = 3 * Real.sin (2 * t - 3 * z) := by
  rw [(((hasDerivAt_id' z).const_mul 3).const_sub (2 * t)).cos.deriv]; ring

/-- `E = (0, 2 sin x sin (2 t - 3 z), 0)`. -/
lemma sinusoidal_electricField (c : SpeedOfLight) (t : Time) (p : Space) :
    (sinusoidalGuidePotential c).electricField c t p =
      WithLp.toLp 2 ![0, 2 * Real.sin (p 0) * Real.sin (2 * t.val - 3 * p 2), 0] := by
  rw [sinusoidalGuidePotential, electricField_separableGuidePotential c _ _ t p
    (diff_t contDiff_cos_wave _ _).hasDerivAt, deriv_wave_t]
  ring_nf

/-- `B = (-3 sin x sin (2 t - 3 z), 0, cos x cos (2 t - 3 z))`. -/
lemma sinusoidal_magneticField (c : SpeedOfLight) (t : Time) (p : Space) :
    (sinusoidalGuidePotential c).magneticField c t p =
      WithLp.toLp 2 ![-(3 * Real.sin (p 0) * Real.sin (2 * t.val - 3 * p 2)), 0,
        Real.cos (p 0) * Real.cos (2 * t.val - 3 * p 2)] := by
  rw [sinusoidalGuidePotential, magneticField_separableGuidePotential c _ _ t p
    (Real.differentiable_sin _) (diff_z contDiff_cos_wave _ _), deriv_wave_z, Real.deriv_sin]
  ring_nf

/-- Nonzero derivatives at explicit points: at `t = 0`, `(x, y, z) = (π/2, 0, -π/6)` the
fields are `E = (0, 2, 0)` and `B = (-3, 0, 0)`; at `t = 0` and the origin, `B_z = 1`. -/
lemma sinusoidal_fields_at_point (c : SpeedOfLight) :
    (sinusoidalGuidePotential c).electricField c ⟨0⟩ ⟨![Real.pi / 2, 0, -(Real.pi / 6)]⟩ =
        WithLp.toLp 2 ![0, 2, 0] ∧
      (sinusoidalGuidePotential c).magneticField c ⟨0⟩ ⟨![Real.pi / 2, 0, -(Real.pi / 6)]⟩ =
        WithLp.toLp 2 ![-3, 0, 0] ∧
      (sinusoidalGuidePotential c).magneticField c ⟨0⟩ ⟨![0, 0, 0]⟩ 2 = 1 := by
  have h : Real.sin (3 * (Real.pi / 6)) = 1 := by
    rw [show 3 * (Real.pi / 6) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  refine ⟨?_, ?_, by simp [sinusoidal_magneticField]⟩ <;>
    first | rw [sinusoidal_electricField] | rw [sinusoidal_magneticField]
  all_goals ext i; fin_cases i <;> simp [h]

/-- A reversed curl sign is exposed by `B_x`: the formula `B_x = + a f_z` fails. -/
lemma sinusoidal_reversed_curl_sign_fails (c : SpeedOfLight) :
    ¬ ∀ (t : Time) (p : Space), (sinusoidalGuidePotential c).magneticField c t p 0 =
      Real.sin (p 0) * deriv (fun z => Real.cos (2 * t.val - 3 * z)) (p 2) := by
  intro H
  have h : Real.sin (3 * (Real.pi / 6)) = 1 := by
    rw [show 3 * (Real.pi / 6) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  have := H ⟨0⟩ ⟨![Real.pi / 2, 0, -(Real.pi / 6)]⟩
  rw [sinusoidal_magneticField, deriv_wave_z] at this
  norm_num [h] at this

/-- Skipping the time conversion (feeding the spacetime coordinate `x⁰` straight into `f`)
rescales the electric field: `E_y = -c a(x) f_t(c t, z)`. -/
lemma unconvertedPotential_electricField (c : SpeedOfLight) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (t : Time) (p : Space) :
    (⟨fun x μ => if μ = Sum.inr 1 then a (x (Sum.inr 0)) * f (x (Sum.inl 0)) (x (Sum.inr 2))
        else 0⟩ : ElectromagneticPotential).electricField c t p =
      WithLp.toLp 2 ![0, -((c : ℝ) * (a (p 0) * deriv (fun s => f s (p 2)) (c * t.val))), 0] := by
  rw [electricField_of c _ t p (fun s => a (p 0) * f (c * s) (p 2)) _ ?_ ?_
    ((((diff_t hf (p 2)) _).hasDerivAt.comp t.val ((hasDerivAt_id t.val).const_mul _)).const_mul _)]
  · ext i; fin_cases i <;> simp; ring
  · funext s q; simp [ElectromagneticPotential.scalarPotential, timeSlice_apply]
  · intro s; ext i; fin_cases i <;>
      simp [ElectromagneticPotential.vectorPotential, timeSlice_apply, symm_apply]

end PhyslibExt.Electromagnetism.SeparableGuidePotential
