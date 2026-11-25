/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureProjectionValued
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# A two-point normal spectral measure on complex Euclidean space

On the Hilbert space `ℂ²`, let `Q` project onto the second coordinate and put `T = i • Q`.
The spectrum is `{0,i}`. The projection-valued measure constructed from the continuous
functional calculus of `T` assigns the first coordinate projection to `{0}` and the second
coordinate projection to `{i}`. Both are nonzero and they have different actions on the two
canonical unit vectors. Integrating the spectral coordinate recovers the same operator `T`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped CStarAlgebra InnerProductSpace Pointwise
open MathlibExt.MeasureTheory.Function
open MathlibExt.Analysis.InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure

namespace TwoPointNormalCFCSmoke

private abbrev H := EuclideanSpace ℂ (Fin 2)
private abbrev Op := H →L[ℂ] H
private def e0 : H := EuclideanSpace.single 0 1
private def e1 : H := EuclideanSpace.single 1 1
private def Q : Op := InnerProductSpace.rankOne ℂ e1 e1
private def T : Op := Complex.I • Q

private theorem norm_e0 : ‖e0‖ = 1 :=
  (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Fin 2)).norm_eq_one 0

private theorem norm_e1 : ‖e1‖ = 1 :=
  (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Fin 2)).norm_eq_one 1

private theorem e0_ne_zero : e0 ≠ 0 := by
  intro h
  have hn := norm_e0
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

private theorem e1_ne_zero : e1 ≠ 0 := by
  intro h
  have hn := norm_e1
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

private theorem Q_projection : IsStarProjection Q :=
  InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) norm_e1

private theorem T_normal : IsStarNormal T := by
  let : IsStarNormal Q := Q_projection.isSelfAdjoint.isStarNormal
  exact inferInstanceAs (IsStarNormal (Complex.I • Q))

private theorem Q_apply (x : H) : Q x = x 1 • e1 := by
  simp only [Q, InnerProductSpace.rankOne_apply, e1,
    EuclideanSpace.inner_single_left, map_one, one_mul]

private theorem Q_e0 : Q e0 = 0 := by
  rw [Q_apply]
  simp [e0]

private theorem Q_e1 : Q e1 = e1 := by
  rw [Q_apply]
  simp [e1]

private theorem firstProjection_e0 : (1 - Q : Op) e0 = e0 := by
  change e0 - Q e0 = e0
  rw [Q_e0, sub_zero]

private theorem firstProjection_e1 : (1 - Q : Op) e1 = 0 := by
  change e1 - Q e1 = 0
  rw [Q_e1, sub_self]

private theorem Q_ne_zero : Q ≠ 0 := by
  intro h
  have hx : Q e1 = 0 := congrArg (fun S : Op => S e1) h
  exact e1_ne_zero (Q_e1.symm.trans hx)

private theorem firstProjection_ne_zero : (1 - Q : Op) ≠ 0 := by
  intro h
  have hx : (1 - Q : Op) e0 = 0 := congrArg (fun S : Op => S e0) h
  exact e0_ne_zero (firstProjection_e0.symm.trans hx)

private theorem T_ne_zero : T ≠ 0 :=
  smul_ne_zero Complex.I_ne_zero Q_ne_zero

private abbrev Spec := spectrum ℂ T

private theorem spectral_values (z : Spec) : (z : ℂ) = 0 ∨ (z : ℂ) = Complex.I := by
  let u : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  have hscale : spectrum ℂ T = u • spectrum ℂ Q := by
    simpa only [T, u, Units.smul_def, Units.val_mk0] using
      spectrum.unit_smul_eq_smul (R := ℂ) Q u
  have hz : (z : ℂ) ∈ u • spectrum ℂ Q := hscale ▸ z.property
  rcases hz with ⟨w, hw, hwz⟩
  have hvalues := Q_projection.isIdempotentElem.spectrum_subset ℂ hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvalues
  rcases hvalues with rfl | rfl
  · left
    simpa using hwz.symm
  · right
    simpa [u, Units.smul_def] using hwz.symm

private def cut0 : Set Spec := {z | (z : ℂ) = 0}
private def cutI : Set Spec := {z | (z : ℂ) = Complex.I}

private theorem cutI_measurable : MeasurableSet cutI :=
  (isClosed_eq continuous_subtype_val continuous_const).measurableSet

private theorem cut0_eq_compl : cut0 = cutIᶜ := by
  ext z
  rcases spectral_values z with hz | hz
  · simp [cut0, cutI, hz, Complex.I_ne_zero.symm]
  · simp [cut0, cutI, hz, Complex.I_ne_zero]

private def P : ProjectionValuedMeasure Spec H := normalCFCPVM T T_normal

private def coordinate : C(Spec, ℂ) := (ContinuousMap.id ℂ).restrict (spectrum ℂ T)

private theorem scaledCoordinate_indicator :
    BoundedMeasurableFunction.ofContinuousMap ((-Complex.I) • coordinate) =
      BoundedMeasurableFunction.indicator cutI cutI_measurable := by
  apply Subtype.ext
  apply lp.ext
  funext z
  rcases spectral_values z with hz | hz
  · simp [BoundedMeasurableFunction.indicator_apply, cutI, coordinate, hz,
      Complex.I_ne_zero.symm]
  · simp [BoundedMeasurableFunction.indicator_apply, cutI, coordinate, hz,
      Complex.I_mul_I]

private theorem P_cutI : P cutI = Q := by
  calc
    P cutI = P.spectralIntegral
        (BoundedMeasurableFunction.indicator cutI cutI_measurable) :=
      (spectralIntegral_indicator P cutI cutI_measurable).symm
    _ = P.spectralIntegral
        (BoundedMeasurableFunction.ofContinuousMap ((-Complex.I) • coordinate)) := by
      rw [scaledCoordinate_indicator]
    _ = cfcHom T_normal ((-Complex.I) • coordinate) :=
      normalCFCPVM_spectralIntegral_continuous T T_normal _
    _ = Q := by
      change cfcHom T_normal
        ((-Complex.I) • (ContinuousMap.id ℂ).restrict (spectrum ℂ T)) = Q
      rw [map_smul, cfcHom_id, T, smul_smul, neg_mul, Complex.I_mul_I,
        neg_neg, one_smul]

private theorem P_cut0 : P cut0 = 1 - Q := by
  rw [cut0_eq_compl, ProjectionValuedMeasure.compl P cutI_measurable, P_cutI]

private theorem zero_mem_spectrum : (0 : ℂ) ∈ spectrum ℂ T := by
  by_contra h
  have hempty : cut0 = ∅ := by
    ext z
    change (z : ℂ) = 0 ↔ False
    constructor
    · intro hz
      exact h (hz ▸ z.property)
    · exact False.elim
  apply firstProjection_ne_zero
  rw [← P_cut0, hempty, ProjectionValuedMeasure.empty]

private theorem imag_mem_spectrum : Complex.I ∈ spectrum ℂ T := by
  by_contra h
  have hempty : cutI = ∅ := by
    ext z
    change (z : ℂ) = Complex.I ↔ False
    constructor
    · intro hz
      exact h (hz ▸ z.property)
    · exact False.elim
  apply Q_ne_zero
  rw [← P_cutI, hempty, ProjectionValuedMeasure.empty]

private def zeroPoint : Spec := ⟨0, zero_mem_spectrum⟩
private def imagPoint : Spec := ⟨Complex.I, imag_mem_spectrum⟩

private theorem cut0_singleton : cut0 = {zeroPoint} := by
  ext z
  change (z : ℂ) = 0 ↔ z = zeroPoint
  constructor
  · intro h
    apply Subtype.ext
    exact h
  · intro h
    exact congrArg (fun w : Spec => (w : ℂ)) h

private theorem cutI_singleton : cutI = {imagPoint} := by
  ext z
  change (z : ℂ) = Complex.I ↔ z = imagPoint
  constructor
  · intro h
    apply Subtype.ext
    exact h
  · intro h
    exact congrArg (fun w : Spec => (w : ℂ)) h

example (x : H) : (T x) 0 = 0 ∧ (T x) 1 = Complex.I * x 1 := by
  constructor <;> simp [T, Q_apply, e1, smul_smul]

example : spectrum ℂ T = {0, Complex.I} := by
  apply Set.Subset.antisymm
  · intro z hz
    have hvalues : z = 0 ∨ z = Complex.I := spectral_values (⟨z, hz⟩ : Spec)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hvalues
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact zero_mem_spectrum
    · exact imag_mem_spectrum

example : P {zeroPoint} = 1 - Q ∧ P {imagPoint} = Q := by
  rw [← cut0_singleton, ← cutI_singleton]
  exact ⟨P_cut0, P_cutI⟩

example : P {zeroPoint} e0 = e0 ∧ P {zeroPoint} e1 = 0 ∧
    P {imagPoint} e0 = 0 ∧ P {imagPoint} e1 = e1 := by
  rw [← cut0_singleton, ← cutI_singleton, P_cut0, P_cutI]
  exact ⟨firstProjection_e0, firstProjection_e1, Q_e0, Q_e1⟩

example : P {zeroPoint} ≠ 0 ∧ P {imagPoint} ≠ 0 ∧ P {zeroPoint} ≠ P {imagPoint} := by
  rw [← cut0_singleton, ← cutI_singleton, P_cut0, P_cutI]
  refine ⟨firstProjection_ne_zero, Q_ne_zero, ?_⟩
  intro h
  have hx := congrArg (fun S : Op => S e0) h
  rw [firstProjection_e0, Q_e0] at hx
  exact e0_ne_zero hx

example : P.spectralIntegral (BoundedMeasurableFunction.ofContinuousMap coordinate) = T ∧
    T ≠ 0 := by
  exact ⟨normalCFCPVM_spectralIntegral_coordinate T T_normal, T_ne_zero⟩

end TwoPointNormalCFCSmoke
