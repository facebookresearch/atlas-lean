/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Same-octad products reduce to the explicit mixed A/B/C-octad checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityFrobeniusReduction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The Griess pairing against one octad block is its ordinary coordinate pairing. -/
theorem griessForm_octadVector (x : GriessSpace) (p : Fin 759) (v : Fin 64 → ℝ) :
    griessForm x (trialityOctadVector p v) =
      ∑ e, (trialityBlocksEquiv x).2.2.1 p e * v e := by
  rw [griessForm_eq_trialityBlockForm, trialityOctadVector_blocks]
  simp [trialityBlockForm, Pi.single_apply, ite_apply, mul_ite, Finset.sum_ite_eq']

/-- The Griess pairing against an X/Y/Z basis vector extracts that coordinate. -/
theorem griessForm_XYZ_basis (x : GriessSpace) (s : Fin 3) (k : Fin 49152) :
    griessForm x (trialityXYZBasis s k) = (trialityBlocksEquiv x).2.2.2 s k := by
  rw [griessForm_eq_trialityBlockForm, trialityXYZBasis_blocks]
  simp [trialityBlockForm, Pi.single_apply, ite_apply, mul_ite, Finset.sum_ite_eq']

/-- Transformed octad basis products are their explicit finite bilinear Fourier expansion. -/
theorem griessProd_transformed_octad_sum (o p : Fin 759) (e f : Fin 64) :
    griessProd (sExtra (trialityOctadBasis o e)) (sExtra (trialityOctadBasis p f)) =
      ∑ g, ∑ h, (trialityRealMatrix g e * trialityRealMatrix h f) •
        griessProd (trialityOctadBasis o g) (trialityOctadBasis p h) := by
  rw [sExtra_octad_basis, sExtra_octad_basis]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- Fourier transforms within one octad still have zero octad product output. -/
theorem griessProd_transformed_sameOctad_octad_zero (o : Fin 759) (e f : Fin 64) :
    (trialityBlocksEquiv (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityOctadBasis o f)))).2.2.1 = 0 := by
  rw [griessProd_transformed_octad_sum, map_sum]
  simp only [map_sum, map_smul, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst,
    griessProd_sameOctad_octad_zero, smul_zero, Finset.sum_const_zero]

/-- Fourier transforms within one octad still have zero X/Y/Z product output. -/
theorem griessProd_transformed_sameOctad_XYZ_zero (o : Fin 759) (e f : Fin 64) :
    (trialityBlocksEquiv (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityOctadBasis o f)))).2.2.2 = 0 := by
  rw [griessProd_transformed_octad_sum, map_sum]
  simp only [map_sum, map_smul, Prod.snd_sum, Prod.smul_snd,
    griessProd_sameOctad_XYZ_zero, smul_zero, Finset.sum_const_zero]

/-- Same-octad products need only the actual mixed A/B/C-octad preservation
checks; all other source tests vanish or follow from the proved diagonal case. -/
theorem sExtra_sameOctad_product_of_ABC
    (o : Fin 759)
    (hAO : ∀ s p g, TrialityProductPreserved (trialityABCBasis s p) (trialityOctadBasis o g))
    (e f : Fin 64) :
    TrialityProductPreserved (trialityOctadBasis o e) (trialityOctadBasis o f) := by
  apply (trialityProductPreserved_iff_source_cubic _ _).mpr
  intro i
  rcases i with i | (⟨s,p⟩ | (⟨p,g⟩ | ⟨s,k⟩)) <;> simp only [trialitySourceBasis]
  · apply (griessCubic_triality_cycle _ _ _).mpr
    apply griessCubic_triality_of_pair
    exact (trialityProductPreserved_symm _ _).mp (sExtra_preserves_diagonal_product _ _)
  · apply (griessCubic_triality_cycle _ _ _).mpr
    apply griessCubic_triality_of_pair
    exact (trialityProductPreserved_symm _ _).mp (hAO s p f)
  · rw [trialityOctadBasis_eq_vector p g, sExtra_octadVector,
      griessForm_octadVector, griessForm_octadVector]
    simp only [griessProd_transformed_sameOctad_octad_zero, griessProd_sameOctad_octad_zero,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  · rw [sExtra_XYZ_basis, griessForm_XYZ_basis, griessForm_XYZ_basis,
      griessProd_transformed_sameOctad_XYZ_zero, griessProd_sameOctad_XYZ_zero]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
