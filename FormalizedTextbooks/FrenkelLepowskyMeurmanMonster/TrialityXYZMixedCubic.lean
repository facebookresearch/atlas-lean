/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The nonzero mixed XYZ cubic in the actual source coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityXYZSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityMixedSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOctadXYZCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ParkerCyclicPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOddSpinPair

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual X,Y,Z cubic separates into its physical spatial coefficient and spin pairing. -/
theorem trialityXYZ_cubic_mixed_coefficient (d e f : Fin 2048) (j k l : Fin 24) :
    griessForm (griessProd (trialityXYZBasis 0 (finProdFinEquiv (d,j)))
      (trialityXYZBasis 1 (finProdFinEquiv (e,k))))
        (trialityXYZBasis 2 (finProdFinEquiv (f,l))) =
      conwayTensorCoefficient (Sum.inr (Sum.inr (d,j))) k l / 8 *
        ∑ t, spinOperator (griessShortQ (Sum.inr (Sum.inr (d,j))))
          (fun v => trialityYTensor e k v k) t * trialityZTensor f l t l := by
  rw [griessForm_eq_conwayRawForm, griessProd_encode, griessConwayEncode_X_basis,
    griessConwayEncode_Y_basis, griessConwayEncode_Z_basis,
    trialityYTensor_column, trialityZTensor_column]
  have h := conwayRawCubic_short_columns (Sum.inr (Sum.inr (d,j)))
    (trialityYSpin e k) (trialityZSpin f) k l
  have hy : trialityYSpin e k = fun v => trialityYTensor e k v k := by
    funext v
    simp only [trialityYSpin, trialityYTensor, ite_true, mul_one]
  have hz : trialityZSpin f = fun v => trialityZTensor f l v l := by
    funext v
    simp only [trialityZSpin, trialityZTensor, ite_true, mul_one]
  simpa only [hy, hz, conwaySpinColumn, ite_true, conwayShortBasis] using h

lemma qSign_boolean (b : Bool) :
    qSign (golayBooleanCast b) = if b then (-1 : ℝ) else 1 := by
  cases b <;> simp [golayBooleanCast]

/-- Source code addition multiplies the real coordinate signs. -/
theorem trialityCodeSign_add (d e f : Fin 2048)
    (hf : golayLabelCoefficients ⟨d.val, by omega⟩ +
      golayLabelCoefficients ⟨e.val, by omega⟩ =
        golayLabelCoefficients ⟨f.val, by omega⟩) (i : Fin 24) :
    (if (golayEncodedMask f.val).testBit i.val then (-1 : ℝ) else 1) =
      (if (golayEncodedMask d.val).testBit i.val then -1 else 1) *
        (if (golayEncodedMask e.val).testBit i.val then -1 else 1) := by
  have h := congrArg (fun a : SpinIndex => qSign (golayEncoder a i)) hf
  rw [map_add] at h
  simp only [Pi.add_apply, golayLabelEncoder_boolean, qSign_add, qSign_boolean] at h
  exact h.symm

/-- Adding a lower source label twice cancels it in the actual binary coordinates. -/
theorem trialityCode_add_cycle (d e f : Fin 2048) :
    (golayLabelCoefficients ⟨d.val, by omega⟩ +
      golayLabelCoefficients ⟨e.val, by omega⟩ =
        golayLabelCoefficients ⟨f.val, by omega⟩) ↔
    (golayLabelCoefficients ⟨f.val, by omega⟩ +
      golayLabelCoefficients ⟨d.val, by omega⟩ =
        golayLabelCoefficients ⟨e.val, by omega⟩) := by
  constructor
  · intro h
    rw [← h]
    have hz : golayLabelCoefficients ⟨d.val, by omega⟩ +
        golayLabelCoefficients ⟨d.val, by omega⟩ = (0 : SpinIndex) :=
      ZModModule.add_self _
    calc
      _ = (golayLabelCoefficients ⟨d.val, by omega⟩ +
        golayLabelCoefficients ⟨d.val, by omega⟩) +
        golayLabelCoefficients ⟨e.val, by omega⟩ := by abel
      _ = _ := by rw [hz, zero_add]
  · intro h
    rw [← h]
    have hz : golayLabelCoefficients ⟨d.val, by omega⟩ +
        golayLabelCoefficients ⟨d.val, by omega⟩ = (0 : SpinIndex) :=
      ZModModule.add_self _
    calc
      _ = golayLabelCoefficients ⟨f.val, by omega⟩ +
        (golayLabelCoefficients ⟨d.val, by omega⟩ +
          golayLabelCoefficients ⟨d.val, by omega⟩) := by abel
      _ = _ := by rw [hz, add_zero]

/-- The explicit nonzero source XYZ cubic value after its spin phase is evaluated. -/
noncomputable def trialityXYZCubicValue (d e f : Fin 2048) (j k l : Fin 24) : ℝ :=
  trialityXYZSpatial j k l / 8 *
    (qSign (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) *
      qSign (spinDot (sourceWordTheta ⟨d.val, by omega⟩)
        (golayLabelCoefficients ⟨e.val, by omega⟩))) *
    (if (golayEncodedMask d.val).testBit k.val then -1 else 1) *
    (if (golayEncodedMask d.val).testBit l.val then -1 else 1) *
    (if (golayEncodedMask e.val).testBit j.val then -1 else 1) *
    (if (golayEncodedMask e.val).testBit k.val then -1 else 1)

/-- The spatial and Parker phases give the same explicit cubic after cycling X,Y,Z. -/
theorem trialityXYZCubicValue_cycle (d e f : Fin 2048) (j k l : Fin 24)
    (hf : golayLabelCoefficients ⟨d.val, by omega⟩ +
      golayLabelCoefficients ⟨e.val, by omega⟩ =
        golayLabelCoefficients ⟨f.val, by omega⟩) :
    trialityXYZCubicValue d e f j k l = trialityXYZCubicValue f d e l j k := by
  unfold trialityXYZCubicValue
  rw [trialityXYZSpatial_cycle j k l, trialityCodeSign_add d e f hf j,
    trialityCodeSign_add d e f hf k,
    parkerCyclicPhase ⟨d.val, by omega⟩ ⟨e.val, by omega⟩ ⟨f.val, by omega⟩ hf.symm]
  have hsq : (if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) *
      (if (golayEncodedMask d.val).testBit j.val then -1 else 1) = 1 := by
    split_ifs <;> norm_num
  calc
    _ = ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) *
      (if (golayEncodedMask d.val).testBit j.val then -1 else 1)) *
      (trialityXYZSpatial l j k / 8 *
        (qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) *
          qSign (spinDot (sourceWordTheta ⟨f.val, by omega⟩)
            (golayLabelCoefficients ⟨d.val, by omega⟩))) *
        (if (golayEncodedMask d.val).testBit k.val then -1 else 1) *
        (if (golayEncodedMask d.val).testBit l.val then -1 else 1) *
        (if (golayEncodedMask e.val).testBit j.val then -1 else 1) *
        (if (golayEncodedMask e.val).testBit k.val then -1 else 1)) := by rw [hsq, one_mul]
    _ = _ := by ring

/-- The actual mixed XYZ cubic is its explicit value times the actual code-addition indicator. -/
theorem trialityXYZ_cubic_mixed_value (d e f : Fin 2048) (j k l : Fin 24) :
    griessForm (griessProd (trialityXYZBasis 0 (finProdFinEquiv (d,j)))
      (trialityXYZBasis 1 (finProdFinEquiv (e,k))))
        (trialityXYZBasis 2 (finProdFinEquiv (f,l))) =
      trialityXYZCubicValue d e f j k l *
        (if golayLabelCoefficients ⟨d.val, by omega⟩ +
          golayLabelCoefficients ⟨e.val, by omega⟩ =
            golayLabelCoefficients ⟨f.val, by omega⟩ then 1 else 0) := by
  rw [trialityXYZ_cubic_mixed_coefficient, trialitySpinPair_odd_YZ_all,
    conwayTensorCoefficient_odd_spatial]
  unfold trialityXYZCubicValue
  ring

/-- The actual X,Y,Z cubic is unchanged when the source colors and labels are cycled. -/
theorem trialityXYZ_cubic_mixed_cycle (d e f : Fin 2048) (j k l : Fin 24) :
    griessForm (griessProd (trialityXYZBasis 0 (finProdFinEquiv (d,j)))
      (trialityXYZBasis 1 (finProdFinEquiv (e,k))))
        (trialityXYZBasis 2 (finProdFinEquiv (f,l))) =
    griessForm (griessProd (trialityXYZBasis 0 (finProdFinEquiv (f,l)))
      (trialityXYZBasis 1 (finProdFinEquiv (d,j))))
        (trialityXYZBasis 2 (finProdFinEquiv (e,k))) := by
  rw [trialityXYZ_cubic_mixed_value, trialityXYZ_cubic_mixed_value]
  by_cases hf : golayLabelCoefficients ⟨d.val, by omega⟩ +
      golayLabelCoefficients ⟨e.val, by omega⟩ = golayLabelCoefficients ⟨f.val, by omega⟩
  · have hfc := (trialityCode_add_cycle d e f).mp hf
    simp only [hf, hfc, ite_true, mul_one]
    exact trialityXYZCubicValue_cycle d e f j k l hf
  · have hfc := mt (trialityCode_add_cycle d e f).mpr hf
    simp only [hf, hfc, ite_false, mul_zero]

/-- Actual triality preserves the nonzero mixed XYZ cubic for every source label and position. -/
theorem trialityXYZ_cubic_mixed_preserved (d e f : Fin 2048) (j k l : Fin 24) :
    griessForm
      (griessProd (sExtra (trialityXYZBasis 0 (finProdFinEquiv (d,j))))
        (sExtra (trialityXYZBasis 1 (finProdFinEquiv (e,k)))))
      (sExtra (trialityXYZBasis 2 (finProdFinEquiv (f,l)))) =
    griessForm (griessProd (trialityXYZBasis 0 (finProdFinEquiv (d,j)))
      (trialityXYZBasis 1 (finProdFinEquiv (e,k))))
        (trialityXYZBasis 2 (finProdFinEquiv (f,l))) := by
  rw [sExtra_XYZ_basis, sExtra_XYZ_basis, sExtra_XYZ_basis]
  have h0 : trialityCycle 0 = 1 := by decide +kernel
  have h1 : trialityCycle 1 = 2 := by decide +kernel
  have h2 : trialityCycle 2 = 0 := by decide +kernel
  rw [h0, h1, h2]
  calc
    _ = griessForm (trialityXYZBasis 0 (finProdFinEquiv (f,l)))
      (griessProd (trialityXYZBasis 1 (finProdFinEquiv (d,j)))
        (trialityXYZBasis 2 (finProdFinEquiv (e,k)))) := griessForm_swap _ _
    _ = griessForm (griessProd (trialityXYZBasis 0 (finProdFinEquiv (f,l)))
      (trialityXYZBasis 1 (finProdFinEquiv (d,j))))
        (trialityXYZBasis 2 (finProdFinEquiv (e,k))) := (griessProd_frobenius _ _ _).symm
    _ = _ := (trialityXYZ_cubic_mixed_cycle d e f j k l).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
