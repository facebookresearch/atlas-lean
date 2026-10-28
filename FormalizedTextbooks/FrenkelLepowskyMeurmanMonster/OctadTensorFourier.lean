/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Fourier identities for actual octad tensor cubic coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTensorCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadXYZSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadSignSpace
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPairFourier
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCodeWeight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCodeSigns

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

def octadTensorRestriction (o : Fin 759) (f : Fin 2048) (k : Fin 8) : ZMod 2 :=
  golayEncoder (octadSpinLow f) (golayOctadCoordinate o k)
noncomputable def octadTensorCharacterLabel (o : Fin 759) (f : Fin 2048) : Fin 64 :=
  octadSignLabelEquiv.symm (octadSignNormalize (octadTensorRestriction o f))

theorem octadTensorRestriction_even (o : Fin 759) (f : Fin 2048) :
    ∑ k, octadTensorRestriction o f k = 0 := golayEncoder_octad_restriction_even o _

theorem octadTensorCharacterLabel_bits (o : Fin 759) (f : Fin 2048) (k : Fin 8) :
    trialityBinaryBit (octadTensorCharacterLabel o f) k =
      octadTensorRestriction o f k + octadTensorRestriction o f 7 := by
  have h := octadSignRepresentative_normalize (octadTensorRestriction o f)
    (octadTensorRestriction_even o f)
  have he : octadSignLabelEquiv (octadTensorCharacterLabel o f) =
      octadSignNormalize (octadTensorRestriction o f) := octadSignLabelEquiv.apply_symm_apply _
  rw [← he, octadSignRepresentative_label] at h
  exact congrFun h k

private theorem hadamard_qSign (c e : Fin 64) :
    (trialityHadamard c e : ℝ) = qSign (trialityBinaryPair c e) := by
  rw [trialityHadamard_binary]
  unfold trialityIntegerSign qSign
  split_ifs <;> norm_num

theorem octadTensorCharacterLabel_character (o : Fin 759) (f : Fin 2048) (e : Fin 64) :
    octadNegativeCharacter o e f = (trialityHadamard (octadTensorCharacterLabel o f) e : ℝ) := by
  have he : (∑ k, trialityBinaryBit e k) = 0 := by
    have h := octadSignRepresentative_even (octadSignLabelEquiv e)
    rw [octadSignRepresentative_label] at h
    exact h
  have hp : trialityBinaryPair (octadTensorCharacterLabel o f) e =
      ∑ k, trialityBinaryBit e k * octadTensorRestriction o f k := by
    simp only [trialityBinaryPair, octadTensorCharacterLabel_bits, add_mul,
      Finset.sum_add_distrib]
    rw [← Finset.mul_sum, he, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  rw [hadamard_qSign, hp]
  exact congrArg qSign (griessOctadNegative_character_local o e (octadSpinLow f))

set_option maxHeartbeats 0 in
-- This is a fixed 64-label, two-complement-bit parity certificate in the kernel.
set_option maxRecDepth 10000 in
private theorem even_label_complement_halfweight : ∀ (c : Fin 64) (a : ZMod 2),
    (((∑ k : Fin 8, (trialityBinaryBit c k + a).val) / 2 : ℕ) : ZMod 2) =
      griessOctadOmegaCoefficient c := by
  unfold trialityBinaryBit golayBooleanCast griessOctadOmegaCoefficient
  decide +kernel

/-- The quadratic phase of the actual character label is half the restriction weight. -/
theorem octadTensorCharacterLabel_diagonal (o : Fin 759) (f : Fin 2048) :
    (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) =
      qSign ((∑ k : Fin 8, (octadTensorRestriction o f k).val) / 2 : ℕ) := by
  have hv : octadTensorRestriction o f =
      fun k => trialityBinaryBit (octadTensorCharacterLabel o f) k +
        octadTensorRestriction o f 7 := by
    ext k
    rw [octadTensorCharacterLabel_bits, add_assoc, ZModModule.add_self, add_zero]
  rw [hv]
  rw [even_label_complement_halfweight, griessOctadOmegaCoefficient_sign]
theorem octadPhysicalSign_pair (o : Fin 759) (e : Fin 64) (a b : Fin 8) :
    octadPhysicalSign o e (golayOctadCoordinate o a) *
      octadPhysicalSign o e (golayOctadCoordinate o b) = (trialityOctadPairSign a b e : ℝ) := by
  rw [octadPhysicalSign_local, octadPhysicalSign_local]
  unfold trialityOctadPairSign
  cases ha : (trialityEvenMask e).testBit a.val <;>
    cases hb : (trialityEvenMask e).testBit b.val <;> norm_num

theorem octadTensor_diagonal_xor (e c : Fin 64) :
    (trialityIntegerDiagonal (trialityXor e c) : ℝ) =
      (trialityIntegerDiagonal e : ℝ) * (trialityIntegerDiagonal c : ℝ) *
        (trialityHadamard c e : ℝ) := by
  rw [trialityIntegerDiagonal_xor, trialityHadamard_symmetric e c]
  push_cast
  rfl

theorem octadTensor_character_fourier (o : Fin 759) (f : Fin 2048) (e : Fin 64) :
    (∑ g, trialityRealMatrix g e * octadNegativeCharacter o g f) =
      (trialityIntegerDiagonal e : ℝ) *
        (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) *
          octadNegativeCharacter o e f := by
  simp_rw [octadTensorCharacterLabel_character]
  rw [trialityOctad_fourier_character, octadTensor_diagonal_xor]

theorem octadTensor_character_pair_fourier (o : Fin 759) (f : Fin 2048) (e : Fin 64)
    (a b : Fin 8) (hab : a ≠ b) :
    (∑ g, trialityRealMatrix g e * octadNegativeCharacter o g f *
      (octadPhysicalSign o g (golayOctadCoordinate o a) *
        octadPhysicalSign o g (golayOctadCoordinate o b))) =
      (trialityIntegerDiagonal e : ℝ) *
        (trialityIntegerDiagonal (trialityXor (octadTensorCharacterLabel o f)
          (trialityOctadPairShift a b)) : ℝ) * octadNegativeCharacter o e f *
            (octadPhysicalSign o e (golayOctadCoordinate o a) *
              octadPhysicalSign o e (golayOctadCoordinate o b)) := by
  have hp (g : Fin 64) :
      (octadPhysicalSign o g (golayOctadCoordinate o a) *
        octadPhysicalSign o g (golayOctadCoordinate o b)) =
          (trialityHadamard (trialityOctadPairShift a b) g : ℝ) := by
    rw [octadPhysicalSign_pair, trialityOctadPairShift_hadamard a b hab]
  simp_rw [hp, octadTensorCharacterLabel_character]
  have hprod (g : Fin 64) :
      trialityRealMatrix g e * (trialityHadamard (octadTensorCharacterLabel o f) g : ℝ) *
        (trialityHadamard (trialityOctadPairShift a b) g : ℝ) =
      trialityRealMatrix g e *
        (trialityHadamard
          (trialityXor (octadTensorCharacterLabel o f) (trialityOctadPairShift a b)) g : ℝ) := by
    rw [trialityHadamard_xor]
    push_cast
    ring
  simp_rw [hprod]
  rw [trialityOctad_fourier_character, octadTensor_diagonal_xor, trialityHadamard_xor]
  push_cast
  ring

/-- The signed-pair shifted character phase is minus the original phase times
 the two physical code signs in the character label. -/
theorem octadTensor_pair_diagonal (o : Fin 759) (f : Fin 2048) (a b : Fin 8) (hab : a ≠ b) :
    (trialityIntegerDiagonal (trialityXor (octadTensorCharacterLabel o f)
      (trialityOctadPairShift a b)) : ℝ) =
      -(trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) *
        qSign (octadTensorRestriction o f a) * qSign (octadTensorRestriction o f b) := by
  rw [trialityIntegerDiagonal_xor, trialityOctadPairShift_diagonal a b hab]
  have hp := trialityOctadPairShift_hadamard a b hab (octadTensorCharacterLabel o f)
  rw [trialityHadamard_symmetric] at hp
  rw [hp]
  unfold trialityOctadPairSign
  have hs (k : Fin 8) :
      (if (trialityEvenMask (octadTensorCharacterLabel o f)).testBit k.val
        then (-1 : ℤ) else 1 : ℤ) =
        trialityIntegerSign (trialityBinaryBit (octadTensorCharacterLabel o f) k) := by
    unfold trialityBinaryBit golayBooleanCast trialityIntegerSign
    cases hk : (trialityEvenMask (octadTensorCharacterLabel o f)).testBit k.val <;> norm_num
  rw [hs a, hs b]
  push_cast
  have hsign (k : Fin 8) :
      (trialityIntegerSign (trialityBinaryBit (octadTensorCharacterLabel o f) k) : ℝ) =
        qSign (octadTensorRestriction o f k) * qSign (octadTensorRestriction o f 7) := by
    rw [octadTensorCharacterLabel_bits]
    have he (x : ZMod 2) : (trialityIntegerSign x : ℝ) = qSign x := by
      unfold trialityIntegerSign qSign
      split_ifs <;> norm_num
    rw [he, qSign_add]
  rw [hsign a, hsign b]
  have hz := qSign_sq (octadTensorRestriction o f 7)
  calc
    _ = -(trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) *
        qSign (octadTensorRestriction o f a) * qSign (octadTensorRestriction o f b) *
          (qSign (octadTensorRestriction o f 7) * qSign (octadTensorRestriction o f 7)) := by ring
    _ = _ := by rw [hz]; ring

set_option backward.isDefEq.respectTransparency false in
theorem octadTensor_ZZ_fourier_factor (o : Fin 759) (d f : Fin 2048)
    (i j : Fin 24) (e : Fin 64) :
    (∑ g, trialityRealMatrix g e *
      griessForm (griessProd (trialityOctadBasis o g)
        (trialityXYZBasis 2 (finProdFinEquiv (d,i))))
          (trialityXYZBasis 2 (finProdFinEquiv (f,j)))) =
      octadZSpinConstant o d f / 8 *
        ∑ g, trialityRealMatrix g e * octadNegativeCharacter o g f *
          ((if i=j then 1 else 0) - octadPhysicalSign o g i * octadPhysicalSign o g j) := by
  simp_rw [trialityOctadXYZ_cubic_ZZ_normalform]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The two spatial constant ratios suffice for the actual Y-to-Z cubic transition. -/
theorem octadTensor_YY_fourier_of_constants (o : Fin 759) (d f : Fin 2048)
    (hdiag : ∀ i : Fin 24,
      (golayEncodedMask (golayOctadLabel o).val).testBit i.val ≠ true →
      octadYSpinConstant o d f i i = octadZSpinConstant o d f *
        (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ))
    (hpair : ∀ (a b : Fin 8), a ≠ b →
      octadYSpinConstant o d f (golayOctadCoordinate o a) (golayOctadCoordinate o b) =
        octadZSpinConstant o d f *
          (trialityIntegerDiagonal (trialityXor (octadTensorCharacterLabel o f)
            (trialityOctadPairShift a b)) : ℝ))
    (i j : Fin 24) (e : Fin 64) :
    (∑ g, trialityRealMatrix g e *
      griessForm (griessProd (trialityOctadBasis o g)
        (trialityXYZBasis 2 (finProdFinEquiv (d,i))))
          (trialityXYZBasis 2 (finProdFinEquiv (f,j)))) =
      griessForm (griessProd (trialityOctadBasis o e)
        (trialityXYZBasis 1 (finProdFinEquiv (d,i))))
          (trialityXYZBasis 1 (finProdFinEquiv (f,j))) := by
  rw [octadTensor_ZZ_fourier_factor, trialityOctadXYZ_cubic_YY_normalform,
    griessOctadOmegaCoefficient_sign]
  by_cases hij : i=j
  · subst j
    by_cases hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true
    · obtain ⟨a,ha⟩ := golayOctadCoordinate_surjective o i hi
      have hs (g : Fin 64) : octadPhysicalSign o g i * octadPhysicalSign o g i = 1 := by
        rw [← ha, octadPhysicalSign_local]
        split_ifs <;> norm_num
      simp only [ite_true, hs, sub_self, mul_zero, Finset.sum_const_zero]
    · have hs (g : Fin 64) := octadPhysicalSign_outside o g i hi
      simp only [ite_true, hs, zero_mul, sub_zero, mul_one]
      rw [octadTensor_character_fourier, hdiag i hi]
      ring
  · by_cases hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true
    · by_cases hj : (golayEncodedMask (golayOctadLabel o).val).testBit j.val = true
      · obtain ⟨a,ha⟩ := golayOctadCoordinate_surjective o i hi
        obtain ⟨b,hb⟩ := golayOctadCoordinate_surjective o j hj
        have hab : a ≠ b := by intro he; subst b; exact hij (ha.symm.trans hb)
        rw [← ha, ← hb]
        have heq : golayOctadCoordinate o a ≠ golayOctadCoordinate o b :=
          (golayOctadCoordinate_injective o).ne hab
        simp only [heq, ite_false, zero_sub, mul_neg]
        rw [Finset.sum_neg_distrib, octadTensor_character_pair_fourier o f e a b hab,
          hpair a b hab]
        ring
      · have hs (g : Fin 64) := octadPhysicalSign_outside o g j hj
        simp only [hij, ite_false, hs, mul_zero, sub_self, mul_zero, Finset.sum_const_zero]
    · have hs (g : Fin 64) := octadPhysicalSign_outside o g i hi
      simp only [hij, ite_false, hs, zero_mul, sub_self, mul_zero, Finset.sum_const_zero]


/-- The actual source constants differ by the character's quadratic phase
and the three indicated physical code signs. -/
theorem octadTensor_spinConstant_ratio (o : Fin 759) (d f : Fin 2048) (i j : Fin 24) :
    octadYSpinConstant o d f i j = octadZSpinConstant o d f *
      (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) *
        (if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then -1 else 1) *
          (if (golayEncodedMask f.val).testBit i.val then -1 else 1) *
            (if (golayEncodedMask f.val).testBit j.val then -1 else 1) := by
  by_cases hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d
  · have hw := octadSpinCode_weight_phase o d f hd
    have hwD :
        qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          qSign (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) =
            (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) := by
      rw [octadTensorCharacterLabel_diagonal]
      exact hw
    have hY : octadYSpinConstant o d f i j =
        qSign (spinDot (sourceWordTheta (golayOctadLabel o)) (octadSpinLow f)) *
          (if (golayEncodedMask f.val).testBit i.val then -1 else 1) *
            (if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then -1 else 1) *
              (if (golayEncodedMask f.val).testBit j.val then -1 else 1) *
                octadSpinSelector o d f := by
      unfold octadYSpinConstant
      have hs := octadCodeSign_transport o d f i hd
      calc
        _ = qSign (spinDot (sourceWordTheta (golayOctadLabel o)) (octadSpinLow f)) *
            (qSign ((octadSpinLow f + octadSpinCode o) 11) *
              (if (golayEncodedMask d.val).testBit i.val then -1 else 1)) *
                (if (golayEncodedMask f.val).testBit j.val then -1 else 1) *
                octadSpinSelector o d f := by ring
        _ = _ := by rw [hs]; ring
    have hZ : octadZSpinConstant o d f =
        qSign (spinDot (sourceWordTheta (golayOctadLabel o)) (octadSpinLow f)) *
          (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) *
                octadSpinSelector o d f := by
      unfold octadZSpinConstant
      calc
        _ = qSign (spinDot (sourceWordTheta (golayOctadLabel o)) (octadSpinLow f)) *
          (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
            qSign (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ)) *
                octadSpinSelector o d f := by ring
        _ = _ := by rw [hwD]
    have hsquare : (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) *
        (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) = 1 := by
      exact_mod_cast trialityIntegerDiagonal_sq (octadTensorCharacterLabel o f)
    rw [hY, hZ]
    calc
      _ = qSign (spinDot (sourceWordTheta (golayOctadLabel o)) (octadSpinLow f)) *
          (if (golayEncodedMask f.val).testBit i.val then -1 else 1) *
            (if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then -1 else 1) *
              (if (golayEncodedMask f.val).testBit j.val then -1 else 1) * octadSpinSelector o d f *
                ((trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) *
                  (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ)) := by
          rw [hsquare, mul_one]
      _ = _ := by ring
  · simp only [octadYSpinConstant, octadZSpinConstant, octadSpinSelector, hd,
      ite_false, mul_zero, zero_mul]

theorem octadTensor_spinConstant_diagonal (o : Fin 759) (d f : Fin 2048) (i : Fin 24)
    (hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val ≠ true) :
    octadYSpinConstant o d f i i = octadZSpinConstant o d f *
      (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) := by
  rw [octadTensor_spinConstant_ratio]
  simp only [hi]
  cases hb : (golayEncodedMask f.val).testBit i.val <;> simp

theorem octadTensor_spinConstant_pair (o : Fin 759) (d f : Fin 2048) (a b : Fin 8)
    (hab : a ≠ b) :
    octadYSpinConstant o d f (golayOctadCoordinate o a) (golayOctadCoordinate o b) =
      octadZSpinConstant o d f *
        (trialityIntegerDiagonal (trialityXor (octadTensorCharacterLabel o f)
          (trialityOctadPairShift a b)) : ℝ) := by
  rw [octadTensor_spinConstant_ratio, octadTensor_pair_diagonal o f a b hab]
  have hs (k : Fin 8) : qSign (octadTensorRestriction o f k) =
      if (golayEncodedMask f.val).testBit (golayOctadCoordinate o k).val then -1 else 1 := by
    exact qSign_golayEncoder_label ⟨f.val, by omega⟩ _
  rw [hs a, hs b]
  simp only [golayOctadCoordinate_mem, ite_true]
  ring

/-- The actual OYY coefficients are exactly the triality transform of OZZ. -/
theorem octadTensor_YY_fourier (o : Fin 759) (d f : Fin 2048) (i j : Fin 24) (e : Fin 64) :
    (∑ g, trialityRealMatrix g e *
      griessForm (griessProd (trialityOctadBasis o g)
        (trialityXYZBasis 2 (finProdFinEquiv (d,i))))
          (trialityXYZBasis 2 (finProdFinEquiv (f,j)))) =
      griessForm (griessProd (trialityOctadBasis o e)
        (trialityXYZBasis 1 (finProdFinEquiv (d,i))))
          (trialityXYZBasis 1 (finProdFinEquiv (f,j))) :=
  octadTensor_YY_fourier_of_constants o d f
    (octadTensor_spinConstant_diagonal o d f) (octadTensor_spinConstant_pair o d f) i j e

/-- Triality preserves every actual octad-Y-Y cubic coefficient. -/
theorem trialityOctadXYZ_cubic_Y_to_Z (o : Fin 759) (e : Fin 64) (k l : Fin 49152) :
    griessForm (griessProd (sExtra (trialityOctadBasis o e))
      (sExtra (trialityXYZBasis 1 k))) (sExtra (trialityXYZBasis 1 l)) =
      griessForm (griessProd (trialityOctadBasis o e) (trialityXYZBasis 1 k))
        (trialityXYZBasis 1 l) := by
  rw [trialityOctadXYZ_cubic_transform]
  have hcycle : trialityCycle (1 : Fin 3) = 2 := by decide +kernel
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
  exact octadTensor_YY_fourier o d f i j e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
