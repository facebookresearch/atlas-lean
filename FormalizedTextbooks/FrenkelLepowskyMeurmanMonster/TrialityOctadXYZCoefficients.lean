/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact spin-matrix coefficients of the nonzero octad/XYZ cubic families. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOctadXYZ

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Embed a spin vector in one physical tensor column. -/
noncomputable def conwaySpinColumn (f : SpinSpace) (i : Fin 24)
    (t : SpinIndex) (j : Fin 24) : ℝ := if j = i then f t else 0

private theorem spinOperator_column (q : Q) (f : SpinSpace) (i j : Fin 24)
    (t : SpinIndex) :
    spinOperator q (fun v => conwaySpinColumn f i v j) t =
      if j = i then spinOperator q f t else 0 := by
  by_cases h : j = i <;> simp [spinOperator, conwaySpinColumn, h]

theorem conwayShortTensorProduct_column (r : GriessShortIndex) (f : SpinSpace)
    (i j : Fin 24) (t : SpinIndex) :
    conwayShortTensorProduct (Pi.single r 1) (conwaySpinColumn f i) t j =
      spinOperator (griessShortQ r) f t * conwayTensorCoefficient r i j / 8 := by
  rw [xyzShortTensor_single_apply]
  simp only [spinOperator_column, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The exact 1/8 coefficient separates the physical matrix and spin pairing. -/
theorem conwayRawCubic_short_columns (r : GriessShortIndex) (f g : SpinSpace)
    (i j : Fin 24) :
    conwayRawForm (conwayRawProduct (conwayShortBasis r) (0, (0, conwaySpinColumn f i)))
      (0, (0, conwaySpinColumn g j)) =
      conwayTensorCoefficient r i j / 8 *
        ∑ t, spinOperator (griessShortQ r) f t * g t := by
  have hT : (conwayRawProduct (conwayShortBasis r) (0, (0, conwaySpinColumn f i))).2.2 =
      conwayShortTensorProduct (Pi.single r 1) (conwaySpinColumn f i) := by
    ext t k
    rw [conwayShortTensorProduct_apply]
    simp [conwayRawProduct, conwayShortBasis, spinOperator]
  simp only [conwayRawForm, conwayMatrixForm_eq_sum, Matrix.zero_apply, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, zero_add]
  rw [hT]
  change (∑ t, ∑ k, conwayShortTensorProduct (Pi.single r 1)
    (conwaySpinColumn f i) t k * conwaySpinColumn g j t k) = _
  simp only [conwaySpinColumn, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, conwayShortTensorProduct_column]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

noncomputable def trialityYSpin (d : Fin 2048) (j : Fin 24) : SpinSpace :=
  fun t => qSign (t 11) *
    (if (golayEncodedMask d.val).testBit j.val then -1 else 1) *
    (if spinDictionaryCode t = d then 1 else 0) / Real.sqrt 2

noncomputable def trialityZSpin (d : Fin 2048) : SpinSpace :=
  fun t => qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
    (if spinDictionaryCode t = d then 1 else 0) / Real.sqrt 2

theorem trialityYTensor_column (d : Fin 2048) (j : Fin 24) :
    trialityYTensor d j = conwaySpinColumn (trialityYSpin d j) j := by
  ext t i
  by_cases h : i = j <;> simp [trialityYTensor, conwaySpinColumn, trialityYSpin, h]

theorem trialityZTensor_column (d : Fin 2048) (j : Fin 24) :
    trialityZTensor d j = conwaySpinColumn (trialityZSpin d) j := by
  ext t i
  by_cases h : i = j <;> simp [trialityZTensor, conwaySpinColumn, trialityZSpin, h]

/-- The OXX coefficient is the actual preferred-Q product phase and base match. -/
theorem trialityOctadXYZ_cubic_XX_coefficient (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 0 (finProdFinEquiv (d,i))))
        (trialityXYZBasis 0 (finProdFinEquiv (f,j))) =
      if (griessShortQ (Sum.inr (Sum.inl (o,e))) *
        griessShortQ (Sum.inr (Sum.inr (d,i)))).base =
          (griessShortQ (Sum.inr (Sum.inr (f,j)))).base then
        qSign (Multiplicative.toAdd (griessShortQ (Sum.inr (Sum.inl (o,e))) *
          griessShortQ (Sum.inr (Sum.inr (d,i)))).coeff) else 0 := by
  rw [griessForm_eq_conwayRawForm, griessProd_encode, griessConwayEncode_octadBasis,
    griessConwayEncode_X_basis, griessConwayEncode_X_basis]
  exact conwayRawCubic_short_basis _ _ _

/-- The OYY coefficient uses the actual signed-octad matrix and spin operator. -/
theorem trialityOctadXYZ_cubic_YY_coefficient (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 1 (finProdFinEquiv (d,i))))
        (trialityXYZBasis 1 (finProdFinEquiv (f,j))) =
      conwayTensorCoefficient (Sum.inr (Sum.inl (o,e))) i j / 8 *
        ∑ t, spinOperator (griessShortQ (Sum.inr (Sum.inl (o,e))))
          (trialityYSpin d i) t * trialityYSpin f j t := by
  rw [griessForm_eq_conwayRawForm, griessProd_encode, griessConwayEncode_octadBasis,
    griessConwayEncode_Y_basis, griessConwayEncode_Y_basis,
    trialityYTensor_column, trialityYTensor_column]
  exact conwayRawCubic_short_columns _ _ _ _ _

/-- The OZZ coefficient has the same matrix coefficient and the even spin basis. -/
theorem trialityOctadXYZ_cubic_ZZ_coefficient (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 2 (finProdFinEquiv (d,i))))
        (trialityXYZBasis 2 (finProdFinEquiv (f,j))) =
      conwayTensorCoefficient (Sum.inr (Sum.inl (o,e))) i j / 8 *
        ∑ t, spinOperator (griessShortQ (Sum.inr (Sum.inl (o,e))))
          (trialityZSpin d) t * trialityZSpin f t := by
  rw [griessForm_eq_conwayRawForm, griessProd_encode, griessConwayEncode_octadBasis,
    griessConwayEncode_Z_basis, griessConwayEncode_Z_basis,
    trialityZTensor_column, trialityZTensor_column]
  exact conwayRawCubic_short_columns _ _ _ _ _

/-- A function supported on one dictionary code sums over exactly its two Ω representatives. -/
theorem spinSum_supported_code (F : SpinIndex → ℝ) (d : Fin 2048)
    (hF : ∀ t, spinDictionaryCode t ≠ d → F t = 0) :
    (∑ t, F t) = F (golayLabelCoefficients ⟨d.val, by omega⟩) +
      F (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) := by
  let u := golayLabelCoefficients ⟨d.val, by omega⟩
  let v := golayLabelCoefficients ⟨d.val + 2048, by omega⟩
  have huv : u ≠ v := by
    intro h
    have hh := congrArg (fun t : SpinIndex => t 11) h
    change golayLabelCoefficients ⟨d.val, by omega⟩ 11 =
      golayLabelCoefficients ⟨d.val + 2048, by omega⟩ 11 at hh
    rw [golayLabel_low_last, golayLabel_high_last] at hh
    exact zero_ne_one hh
  have hs : ({u,v} : Finset SpinIndex) ⊆ Finset.univ := Finset.subset_univ _
  have he := Finset.sum_subset hs (fun t _ ht => show F t = 0 from by
    apply hF t
    intro hc
    rcases spinDictionaryIndex_cases t with h | h
    · have hu : t = u := by simpa only [hc] using h
      exact ht (Finset.mem_insert.mpr (Or.inl hu))
    · have hv : t = v := by simpa only [hc] using h
      exact ht (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hv))))
  rw [← he, Finset.sum_pair huv]

/-- Same-parity spin pairings for an even-modulation lift reduce to one representative. -/
theorem spinPairing_same_parity_code (q : Q) (hq : spinModulation q 11 = 0)
    (f g : SpinSpace) (d : Fin 2048) (a : ℝ) (ha : a * a = 1)
    (hf : ∀ t, f (t + trialitySpinOmega) = a * f t)
    (hg : ∀ t, g (t + trialitySpinOmega) = a * g t)
    (hsupp : ∀ t, spinDictionaryCode t ≠ d → g t = 0) :
    (∑ t, spinOperator q f t * g t) =
      2 * (spinOperator q f (golayLabelCoefficients ⟨d.val, by omega⟩) *
        g (golayLabelCoefficients ⟨d.val, by omega⟩)) := by
  rw [spinSum_supported_code _ d (fun t h => by rw [hsupp t h, mul_zero])]
  have hhigh : golayLabelCoefficients ⟨d.val + 2048, by omega⟩ =
      golayLabelCoefficients ⟨d.val, by omega⟩ + trialitySpinOmega :=
    (golayLabel_low_add_omega d).symm
  rw [hhigh, spinOperator_omega_parity_even q hq f a hf, hg]
  calc
    _ = (1 + a * a) *
      (spinOperator q f (golayLabelCoefficients ⟨d.val, by omega⟩) *
        g (golayLabelCoefficients ⟨d.val, by omega⟩)) := by ring
    _ = _ := by rw [ha]; ring

theorem trialityYSpin_omega (d : Fin 2048) (j : Fin 24) (t : SpinIndex) :
    trialityYSpin d j (t + trialitySpinOmega) = -trialityYSpin d j t := by
  simpa only [trialityYTensor_column, conwaySpinColumn, ite_true, trialitySpinOmega] using
    trialityYTensor_add_omega d j t j

theorem trialityZSpin_omega (d : Fin 2048) (t : SpinIndex) :
    trialityZSpin d (t + trialitySpinOmega) = trialityZSpin d t := by
  simpa only [trialityZTensor_column, conwaySpinColumn, ite_true, trialitySpinOmega] using
    trialityZTensor_add_omega d (0 : Fin 24) t (0 : Fin 24)

/-- The OYY coefficient needs just one of the two actual spin representatives. -/
theorem trialityOctadXYZ_cubic_YY_one_spin (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 1 (finProdFinEquiv (d,i))))
        (trialityXYZBasis 1 (finProdFinEquiv (f,j))) =
      conwayTensorCoefficient (Sum.inr (Sum.inl (o,e))) i j / 4 *
        (spinOperator (griessShortQ (Sum.inr (Sum.inl (o,e))))
          (trialityYSpin d i) (golayLabelCoefficients ⟨f.val, by omega⟩) *
            trialityYSpin f j (golayLabelCoefficients ⟨f.val, by omega⟩)) := by
  rw [trialityOctadXYZ_cubic_YY_coefficient]
  rw [spinPairing_same_parity_code _ (griessOctad_modulation_last o e)
    _ _ f (-1) (by norm_num)
    (fun t => by simpa only [neg_one_mul] using trialityYSpin_omega d i t)
    (fun t => by simpa only [neg_one_mul] using trialityYSpin_omega f j t)
    (fun t h => by simp [trialityYSpin, h])]
  ring

/-- The OZZ coefficient likewise reduces to one actual spin representative. -/
theorem trialityOctadXYZ_cubic_ZZ_one_spin (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24) :
    griessForm (griessProd (trialityOctadBasis o e)
      (trialityXYZBasis 2 (finProdFinEquiv (d,i))))
        (trialityXYZBasis 2 (finProdFinEquiv (f,j))) =
      conwayTensorCoefficient (Sum.inr (Sum.inl (o,e))) i j / 4 *
        (spinOperator (griessShortQ (Sum.inr (Sum.inl (o,e))))
          (trialityZSpin d) (golayLabelCoefficients ⟨f.val, by omega⟩) *
            trialityZSpin f (golayLabelCoefficients ⟨f.val, by omega⟩)) := by
  rw [trialityOctadXYZ_cubic_ZZ_coefficient]
  rw [spinPairing_same_parity_code _ (griessOctad_modulation_last o e)
    _ _ f 1 (by norm_num)
    (fun t => by simpa only [one_mul] using trialityZSpin_omega d t)
    (fun t => by simpa only [one_mul] using trialityZSpin_omega f t)
    (fun t h => by simp [trialityZSpin, h])]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
