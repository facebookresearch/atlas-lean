/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual transformed X cubic coefficients from the octad Y-spin normalform. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTensorFourier
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadXYZFourier

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The quadratic source character transforms to its single actual label. -/
theorem octadTensor_quadratic_character_fourier (o : Fin 759) (f : Fin 2048)
    (e : Fin 64) :
    (∑ g, trialityRealMatrix g e *
      ((trialityIntegerDiagonal g : ℝ) * octadNegativeCharacter o g f)) =
        if e = octadTensorCharacterLabel o f then (8 : ℝ) else 0 := by
  simp_rw [octadTensorCharacterLabel_character]
  exact trialityOctad_fourier_quadratic_character _ _

/-- A physical pair shifts the unique transformed character label. -/
theorem octadTensor_quadratic_pair_fourier (o : Fin 759) (f : Fin 2048)
    (e : Fin 64) (a b : Fin 8) (hab : a ≠ b) :
    (∑ g, trialityRealMatrix g e *
      ((trialityIntegerDiagonal g : ℝ) * octadNegativeCharacter o g f *
        (octadPhysicalSign o g (golayOctadCoordinate o a) *
          octadPhysicalSign o g (golayOctadCoordinate o b)))) =
      if e = trialityXor (octadTensorCharacterLabel o f) (trialityOctadPairShift a b)
        then (8 : ℝ) else 0 := by
  have hp (g : Fin 64) :
      octadPhysicalSign o g (golayOctadCoordinate o a) *
        octadPhysicalSign o g (golayOctadCoordinate o b) =
          (trialityHadamard (trialityOctadPairShift a b) g : ℝ) := by
    rw [octadPhysicalSign_pair, trialityOctadPairShift_hadamard a b hab]
  simp_rw [hp, octadTensorCharacterLabel_character]
  have ht (g : Fin 64) :
      (trialityIntegerDiagonal g : ℝ) *
        (trialityHadamard (octadTensorCharacterLabel o f) g : ℝ) *
          (trialityHadamard (trialityOctadPairShift a b) g : ℝ) =
      (trialityIntegerDiagonal g : ℝ) *
        (trialityHadamard (trialityXor (octadTensorCharacterLabel o f)
          (trialityOctadPairShift a b)) g : ℝ) := by
    rw [trialityHadamard_xor]
    push_cast
    ring
  simp_rw [ht]
  exact trialityOctad_fourier_quadratic_character _ _

set_option backward.isDefEq.respectTransparency false in
theorem octadTensor_YY_quadratic_fourier_factor (o : Fin 759) (d f : Fin 2048)
    (i j : Fin 24) (e : Fin 64) :
    (∑ g, trialityRealMatrix g e *
      griessForm (griessProd (trialityOctadBasis o g)
        (trialityXYZBasis 1 (finProdFinEquiv (d,i))))
          (trialityXYZBasis 1 (finProdFinEquiv (f,j)))) =
      octadYSpinConstant o d f i j / 8 *
        ∑ g, trialityRealMatrix g e *
          ((trialityIntegerDiagonal g : ℝ) * octadNegativeCharacter o g f *
            ((if i=j then 1 else 0) -
              octadPhysicalSign o g i * octadPhysicalSign o g j)) := by
  simp_rw [trialityOctadXYZ_cubic_YY_normalform, griessOctadOmegaCoefficient_sign]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Outside the octad, a diagonal source tensor selects the unshifted character. -/
theorem octadTensor_YY_fourier_outside_diagonal (o : Fin 759) (d f : Fin 2048)
    (i : Fin 24) (e : Fin 64)
    (hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val ≠ true) :
    (∑ g, trialityRealMatrix g e *
      griessForm (griessProd (trialityOctadBasis o g)
        (trialityXYZBasis 1 (finProdFinEquiv (d,i))))
          (trialityXYZBasis 1 (finProdFinEquiv (f,i)))) =
      octadYSpinConstant o d f i i *
        (if e = octadTensorCharacterLabel o f then 1 else 0) := by
  rw [octadTensor_YY_quadratic_fourier_factor]
  have hs (g : Fin 64) := octadPhysicalSign_outside o g i hi
  simp only [ite_true, hs, zero_mul, sub_zero, mul_one]
  rw [octadTensor_quadratic_character_fourier]
  split_ifs <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- Inside the octad, two different tensor coordinates select the pair-shifted label. -/
theorem octadTensor_YY_fourier_inside_pair (o : Fin 759) (d f : Fin 2048)
    (a b : Fin 8) (hab : a ≠ b) (e : Fin 64) :
    (∑ g, trialityRealMatrix g e *
      griessForm (griessProd (trialityOctadBasis o g)
        (trialityXYZBasis 1 (finProdFinEquiv (d,golayOctadCoordinate o a))))
          (trialityXYZBasis 1 (finProdFinEquiv (f,golayOctadCoordinate o b)))) =
      -octadYSpinConstant o d f (golayOctadCoordinate o a) (golayOctadCoordinate o b) *
        (if e = trialityXor (octadTensorCharacterLabel o f) (trialityOctadPairShift a b)
          then 1 else 0) := by
  rw [octadTensor_YY_quadratic_fourier_factor]
  have heq : golayOctadCoordinate o a ≠ golayOctadCoordinate o b :=
    (golayOctadCoordinate_injective o).ne hab
  simp only [heq, ite_false, zero_sub, mul_neg]
  rw [Finset.sum_neg_distrib, octadTensor_quadratic_pair_fourier o f e a b hab]
  split_ifs <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal tensor contraction vanishes on every octad coordinate. -/
theorem octadTensor_YY_fourier_inside_diagonal (o : Fin 759) (d f : Fin 2048)
    (a : Fin 8) (e : Fin 64) :
    (∑ g, trialityRealMatrix g e *
      griessForm (griessProd (trialityOctadBasis o g)
        (trialityXYZBasis 1 (finProdFinEquiv (d,golayOctadCoordinate o a))))
          (trialityXYZBasis 1 (finProdFinEquiv (f,golayOctadCoordinate o a)))) = 0 := by
  rw [octadTensor_YY_quadratic_fourier_factor]
  have hs (g : Fin 64) :
      octadPhysicalSign o g (golayOctadCoordinate o a) *
        octadPhysicalSign o g (golayOctadCoordinate o a) = 1 := by
    rw [octadPhysicalSign_local]
    split_ifs <;> norm_num
  simp only [ite_true, hs, sub_self, mul_zero, Finset.sum_const_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Different coordinates give zero if either coordinate is outside the octad. -/
theorem octadTensor_YY_fourier_outside_offdiagonal (o : Fin 759) (d f : Fin 2048)
    (i j : Fin 24) (hij : i ≠ j) (e : Fin 64)
    (hout : (golayEncodedMask (golayOctadLabel o).val).testBit i.val ≠ true ∨
      (golayEncodedMask (golayOctadLabel o).val).testBit j.val ≠ true) :
    (∑ g, trialityRealMatrix g e *
      griessForm (griessProd (trialityOctadBasis o g)
        (trialityXYZBasis 1 (finProdFinEquiv (d,i))))
          (trialityXYZBasis 1 (finProdFinEquiv (f,j)))) = 0 := by
  rw [octadTensor_YY_quadratic_fourier_factor]
  rcases hout with hi | hj
  · have hs (g : Fin 64) := octadPhysicalSign_outside o g i hi
    simp only [hij, ite_false, hs, zero_mul, sub_self, mul_zero, Finset.sum_const_zero]
  · have hs (g : Fin 64) := octadPhysicalSign_outside o g j hj
    simp only [hij, ite_false, hs, mul_zero, sub_self, mul_zero, Finset.sum_const_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
