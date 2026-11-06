/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Cubic reduction and mixed-color vanishing for actual octad×XYZ source products. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityXYZCubic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairOdd
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityFrobeniusReduction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Even all-one modulation preserves the all-one parity of a spin vector. -/
theorem spinOperator_omega_parity_even (q : Q) (hq : spinModulation q 11 = 0)
    (f : SpinSpace) (a : ℝ) (hf : ∀ t, f (t + trialitySpinOmega) = a * f t)
    (t : SpinIndex) :
    spinOperator q f (t + trialitySpinOmega) = a * spinOperator q f t := by
  have hdot : spinDot (spinModulation q) trialitySpinOmega = 0 := by
    simp [spinDot, trialitySpinOmega, Pi.single_apply, hq]
  have hphase : spinPhase q (t + trialitySpinOmega) = spinPhase q t := by
    simp only [spinPhase, spinDot_add_right, hdot, add_zero]
  have ht : t + trialitySpinOmega + spinTranslation q =
      (t + spinTranslation q) + trialitySpinOmega := by abel
  change qSign (spinPhase q (t + trialitySpinOmega)) *
    f (t + trialitySpinOmega + spinTranslation q) =
      a * (qSign (spinPhase q t) * f (t + spinTranslation q))
  rw [hphase, ht, hf]
  ring

/-- The exact short/tensor product inherits a short lift's even all-one modulation. -/
theorem conwayShortTensorProduct_single_omega_even (r : GriessShortIndex)
    (hr : spinModulation (griessShortQ r) 11 = 0)
    (f : SpinIndex → Fin 24 → ℝ) (a : ℝ)
    (hf : ∀ t i, f (t + trialitySpinOmega) i = a * f t i) (t : SpinIndex) (i : Fin 24) :
    conwayShortTensorProduct (Pi.single r 1) f (t + trialitySpinOmega) i =
      a * conwayShortTensorProduct (Pi.single r 1) f t i := by
  simp only [xyzShortTensor_single_apply]
  have hs (j : Fin 24) := spinOperator_omega_parity_even (griessShortQ r) hr
    (fun v => f v j) a (fun v => hf v j) t
  simp_rw [hs]
  have hsum : (∑ j, (a * spinOperator (griessShortQ r) (fun v => f v j) t) *
      conwayTensorCoefficient r j i) =
      a * ∑ j, spinOperator (griessShortQ r) (fun v => f v j) t *
        conwayTensorCoefficient r j i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

/-- An even-modulation short lift has zero cubic coefficient on opposite-parity tensors. -/
theorem conwayRawCubic_short_tensor_opposite_parity_zero (r : GriessShortIndex)
    (hr : spinModulation (griessShortQ r) 11 = 0)
    (f g : SpinIndex → Fin 24 → ℝ) (a b : ℝ) (hab : a * b = -1)
    (hf : ∀ t i, f (t + trialitySpinOmega) i = a * f t i)
    (hg : ∀ t i, g (t + trialitySpinOmega) i = b * g t i) :
    conwayRawForm (conwayRawProduct (conwayShortBasis r) (0, (0, f))) (0, (0, g)) = 0 := by
  have hT : (conwayRawProduct (conwayShortBasis r) (0, (0, f))).2.2 =
      conwayShortTensorProduct (Pi.single r 1) f := by
    ext t i
    rw [conwayShortTensorProduct_apply]
    simp [conwayRawProduct, conwayShortBasis, spinOperator]
  simp only [conwayRawForm, conwayMatrixForm_eq_sum, Matrix.zero_apply, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, zero_add]
  rw [hT]
  exact conwayTensorForm_zero_of_omega_parity _ _ a b hab
    (conwayShortTensorProduct_single_omega_even r hr f a hf) hg

/-- Octad-X-Y and octad-X-Z cubic coefficients vanish by the raw block decomposition. -/
theorem trialityOctadXYZ_cubic_X_tensor_zero (o : Fin 759) (e : Fin 64)
    (k l : Fin 49152) (s : Fin 3) (hs : s ≠ 0) :
    griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis 0 k))
      (trialityXYZBasis s l) = 0 := by
  apply griessCubic_noTensor_tensor_zero
  · rw [griessConwayEncode_octadBasis]; rfl
  · exact trialityXYZBasis_X_tensor_zero _
  · exact trialityXYZBasis_matrix_zero _ _
  · exact trialityXYZBasis_nonzero_short_zero _ _ hs

/-- Octad-Y-Z vanishes: all signed-octad spin lifts preserve Ω parity. -/
theorem trialityOctadXYZ_cubic_Y_Z_zero (o : Fin 759) (e : Fin 64) (k l : Fin 49152) :
    griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis 1 k))
      (trialityXYZBasis 2 l) = 0 := by
  obtain ⟨⟨d,i⟩, rfl⟩ := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).surjective k
  obtain ⟨⟨f,j⟩, rfl⟩ := (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).surjective l
  rw [griessForm_eq_conwayRawForm, griessProd_encode, griessConwayEncode_octadBasis,
    griessConwayEncode_Y_basis, griessConwayEncode_Z_basis]
  apply conwayRawCubic_short_tensor_opposite_parity_zero _
    (griessOctad_modulation_last o e) _ _ (-1) 1 (by norm_num)
  · intro t i
    simpa only [neg_one_mul, trialitySpinOmega] using trialityYTensor_add_omega d _ t i
  · intro t i
    simpa only [one_mul, trialitySpinOmega] using trialityZTensor_add_omega f _ t i

/-- Frobenius symmetry exchanges the last two entries of an actual cubic coefficient. -/
theorem griessCubic_swap_right (x y z : GriessSpace) :
    griessForm (griessProd x y) z = griessForm (griessProd x z) y := by
  rw [griessProd_frobenius, griessProd_frobenius, griessProd_comm y z]

/-- Every octad cubic with two different XYZ colors is zero. -/
theorem trialityOctadXYZ_cubic_mixed_zero (o : Fin 759) (e : Fin 64)
    (s t : Fin 3) (k l : Fin 49152) (hst : s ≠ t) :
    griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis s k))
      (trialityXYZBasis t l) = 0 := by
  fin_cases s <;> fin_cases t
  · exact False.elim (hst rfl)
  · exact trialityOctadXYZ_cubic_X_tensor_zero o e k l 1 (by decide)
  · exact trialityOctadXYZ_cubic_X_tensor_zero o e k l 2 (by decide)
  · rw [griessCubic_swap_right]
    exact trialityOctadXYZ_cubic_X_tensor_zero o e l k 1 (by decide)
  · exact False.elim (hst rfl)
  · exact trialityOctadXYZ_cubic_Y_Z_zero o e k l
  · rw [griessCubic_swap_right]
    exact trialityOctadXYZ_cubic_X_tensor_zero o e l k 2 (by decide)
  · rw [griessCubic_swap_right]
    exact trialityOctadXYZ_cubic_Y_Z_zero o e l k
  · exact False.elim (hst rfl)

/-- The transformed octad cubic is its exact DH/8 Fourier sum. -/
theorem trialityOctadXYZ_cubic_transform (o : Fin 759) (e : Fin 64)
    (s t : Fin 3) (k l : Fin 49152) :
    griessForm (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityXYZBasis s k))) (sExtra (trialityXYZBasis t l)) =
      ∑ f, trialityRealMatrix f e *
        griessForm (griessProd (trialityOctadBasis o f)
          (trialityXYZBasis (trialityCycle s) k)) (trialityXYZBasis (trialityCycle t) l) := by
  rw [sExtra_octadBasis, sExtra_XYZ_basis, sExtra_XYZ_basis]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul]

/-- All mixed-color octad cubic identities already satisfy actual triality covariance. -/
theorem trialityOctadXYZ_cubic_mixed (o : Fin 759) (e : Fin 64)
    (s t : Fin 3) (k l : Fin 49152) (hst : s ≠ t) :
    griessForm (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityXYZBasis s k))) (sExtra (trialityXYZBasis t l)) =
      griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis s k))
        (trialityXYZBasis t l) := by
  rw [trialityOctadXYZ_cubic_transform, trialityOctadXYZ_cubic_mixed_zero o e s t k l hst]
  apply Finset.sum_eq_zero
  intro f _
  have hc : trialityCycle s ≠ trialityCycle t := by
    fin_cases s <;> fin_cases t
    all_goals first | exact False.elim (hst rfl) | decide +kernel
  rw [trialityOctadXYZ_cubic_mixed_zero o f _ _ k l hc, mul_zero]

/-- Actual octad×XYZ preservation reduces to OXX, OYY and OZZ cubic identities.
Diagonal and pair tests use already proved multiplication, and octad tests
use the explicitly supplied octad×octad theorem. -/
theorem trialityOctadXYZ_of_same_color_cubic
    (hOO : ∀ o e p f, TrialityProductPreserved
      (trialityOctadBasis o e) (trialityOctadBasis p f))
    (hdiag : ∀ o e s k l,
      griessForm (griessProd (sExtra (trialityOctadBasis o e))
        (sExtra (trialityXYZBasis s k))) (sExtra (trialityXYZBasis s l)) =
        griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis s k))
          (trialityXYZBasis s l))
    (o : Fin 759) (e : Fin 64) (s : Fin 3) (k : Fin 49152) :
    TrialityProductPreserved (trialityOctadBasis o e) (trialityXYZBasis s k) := by
  apply (trialityProductPreserved_iff_source_cubic _ _).mpr
  intro i
  rcases i with i | (⟨t,p⟩ | (⟨v,f⟩ | ⟨t,l⟩)) <;> simp only [trialitySourceBasis]
  · rw [griessCubic_triality_cycle]
    apply griessCubic_triality_of_pair
    exact (trialityProductPreserved_symm _ _).mpr
      (sExtra_preserves_diagonal_product _ _)
  · rw [griessCubic_triality_cycle]
    apply griessCubic_triality_of_pair
    apply (trialityProductPreserved_symm _ _).mpr
    obtain ⟨⟨d,j⟩, rfl⟩ :=
      (finProdFinEquiv : Fin 2048 × Fin 24 ≃ Fin 49152).surjective k
    exact triality_ABC_XYZ_product t s p d j
  · rw [griessCubic_triality_cycle, griessCubic_triality_cycle]
    exact griessCubic_triality_of_pair _ _ _ (hOO v f o e)
  · by_cases h : s = t
    · subst t
      exact hdiag o e s k l
    · exact trialityOctadXYZ_cubic_mixed o e s t k l h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
