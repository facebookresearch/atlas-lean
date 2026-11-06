/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The unconditional octad-X-X cubic triality transition. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadXXFourier
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadXXCubic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The actual OXX coefficients equal the triality transform of OYY. -/
theorem octadTensor_XX_fourier (o : Fin 759) (d f : Fin 2048) (i j : Fin 24) (e : Fin 64) :
    (∑ g, trialityRealMatrix g e *
      griessForm (griessProd (trialityOctadBasis o g)
        (trialityXYZBasis 1 (finProdFinEquiv (d,i))))
          (trialityXYZBasis 1 (finProdFinEquiv (f,j)))) =
      griessForm (griessProd (trialityOctadBasis o e)
        (trialityXYZBasis 0 (finProdFinEquiv (d,i))))
          (trialityXYZBasis 0 (finProdFinEquiv (f,j))) := by
  have hmem (k : Fin 24) : k ∈ golayOctadSupport o ↔
      (golayEncodedMask (golayOctadLabel o).val).testBit k.val = true := by
    simp only [golayOctadSupport, golayMaskSupport, Finset.mem_filter,
      Finset.mem_univ, true_and]
  by_cases hij : i=j
  · subst j
    by_cases hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true
    · obtain ⟨a,ha⟩ := golayOctadCoordinate_surjective o i hi
      rw [← ha, octadTensor_YY_fourier_inside_diagonal, octadXXCubic_inside_diagonal]
    · rw [octadTensor_YY_fourier_outside_diagonal o d f i e hi,
        octadXXCubic_outside_diagonal o e d f i ((hmem i).not.mpr hi)]
  · by_cases hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true
    · by_cases hj : (golayEncodedMask (golayOctadLabel o).val).testBit j.val = true
      · obtain ⟨a,ha⟩ := golayOctadCoordinate_surjective o i hi
        obtain ⟨b,hb⟩ := golayOctadCoordinate_surjective o j hj
        have hab : a ≠ b := by intro he; subst b; exact hij (ha.symm.trans hb)
        rw [← ha, ← hb, octadTensor_YY_fourier_inside_pair o d f a b hab e,
          octadXXCubic_inside_pair o e d f a b hab]
      · rw [octadTensor_YY_fourier_outside_offdiagonal o d f i j hij e (Or.inr hj),
          octadXXCubic_outside_offdiagonal o e d f i j hij (Or.inr ((hmem j).not.mpr hj))]
    · rw [octadTensor_YY_fourier_outside_offdiagonal o d f i j hij e (Or.inl hi),
        octadXXCubic_outside_offdiagonal o e d f i j hij (Or.inl ((hmem i).not.mpr hi))]

/-- Triality preserves every actual octad-X-X cubic coefficient. -/
theorem trialityOctadXYZ_cubic_X_to_Y (o : Fin 759) (e : Fin 64) (k l : Fin 49152) :
    griessForm (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityXYZBasis 0 k))) (sExtra (trialityXYZBasis 0 l)) =
      griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis 0 k))
        (trialityXYZBasis 0 l) := by
  rw [trialityOctadXYZ_cubic_transform]
  have hcycle : trialityCycle (0 : Fin 3) = 1 := by decide +kernel
  rw [hcycle]
  let d := ((finProdFinEquiv : (Fin 2048 × Fin 24) ≃ Fin 49152).symm k).1
  let i := ((finProdFinEquiv : (Fin 2048 × Fin 24) ≃ Fin 49152).symm k).2
  let f := ((finProdFinEquiv : (Fin 2048 × Fin 24) ≃ Fin 49152).symm l).1
  let j := ((finProdFinEquiv : (Fin 2048 × Fin 24) ≃ Fin 49152).symm l).2
  have hk : finProdFinEquiv (d,i) = k :=
    (finProdFinEquiv : (Fin 2048 × Fin 24) ≃ Fin 49152).apply_symm_apply k
  have hl : finProdFinEquiv (f,j) = l :=
    (finProdFinEquiv : (Fin 2048 × Fin 24) ≃ Fin 49152).apply_symm_apply l
  rw [← hk, ← hl]
  exact octadTensor_XX_fourier o d f i j e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
