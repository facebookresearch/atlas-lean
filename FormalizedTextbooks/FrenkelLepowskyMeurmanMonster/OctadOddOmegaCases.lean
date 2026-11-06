/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact Ω-coordinate cases in actual octad/odd preferred-Q selectors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTensorFourier
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOddSpinPair
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadIntersection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Under the dictionary selector, the Ω-coordinate sign is a physical code
character times the two actual quadratic source phases. -/
theorem octadOddOmega_sign (o : Fin 759) (e : Fin 64) (d f : Fin 2048)
    (i j : Fin 24)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d) :
    qSign (griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
      griessOddOmegaCoefficient f j + octadSpinCode o 11) =
    (trialityIntegerDiagonal e : ℝ) *
      (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) *
      qSign (golayEncoder (octadSpinLow f) i) *
      qSign (golayEncoder (octadSpinLow f) j) *
      qSign (golayEncoder (octadSpinCode o) i) := by
  have hw : qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      qSign (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) =
        (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) := by
    rw [octadTensorCharacterLabel_diagonal]
    exact octadSpinCode_weight_phase o d f hd
  have hs : qSign (octadSpinCode o 11) * qSign (golayEncoder (octadSpinLow d) i) =
      qSign (golayEncoder (octadSpinLow f) i) *
        qSign (golayEncoder (octadSpinCode o) i) := by
    have h := octadCodeSign_transport o d f i hd
    simpa only [Pi.add_apply, octadSpinLow, octadSpinCode, golayLabel_low_last,
      zero_add, qSign_golayEncoder_label] using h
  rw [griessOddOmegaCoefficient_quarter, griessOddOmegaCoefficient_quarter]
  simp only [qSign_add]
  rw [griessOctadOmegaCoefficient_sign]
  calc
    _ = (trialityIntegerDiagonal e : ℝ) *
        (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          qSign (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ)) *
        (qSign (octadSpinCode o 11) * qSign (golayEncoder (octadSpinLow d) i)) *
          qSign (golayEncoder (octadSpinLow f) j) := by
      dsimp only [octadSpinLow]
      ring
    _ = _ := by rw [hw, hs]; ring

private theorem diagonal_real_sq (c : Fin 64) :
    (trialityIntegerDiagonal c : ℝ) * (trialityIntegerDiagonal c : ℝ) = 1 := by
  exact_mod_cast trialityIntegerDiagonal_sq c

/-- With equal physical indices and the unshifted character label, the Ω
coordinate vanishes exactly outside the actual octad. -/
theorem octadOddOmega_same (o : Fin 759) (d f : Fin 2048) (i : Fin 24)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d) :
    griessOctadOmegaCoefficient (octadTensorCharacterLabel o f) +
      griessOddOmegaCoefficient d i + griessOddOmegaCoefficient f i +
        octadSpinCode o 11 = 0 ↔ i ∉ golayOctadSupport o := by
  have hs := octadOddOmega_sign o (octadTensorCharacterLabel o f) d f i i hd
  rw [diagonal_real_sq] at hs
  simp only [one_mul, qSign_sq] at hs
  calc
    _ ↔ qSign (griessOctadOmegaCoefficient (octadTensorCharacterLabel o f) +
      griessOddOmegaCoefficient d i + griessOddOmegaCoefficient f i +
        octadSpinCode o 11) = 1 := (qSign_eq_one_iff _).symm
    _ ↔ qSign (golayEncoder (octadSpinCode o) i) = 1 := by rw [hs]
    _ ↔ golayEncoder (octadSpinCode o) i = 0 := qSign_eq_one_iff _
    _ ↔ i ∉ golayOctadSupport o := by
      change golayOctadWord o i = 0 ↔ _
      simpa only [ne_eq, not_not] using not_congr (golayOctadWord_ne_zero_iff o i)

/-- At two distinct local positions, the pair-shifted character gives zero
Ω coordinate. This includes the octad source label's actual highest bit. -/
theorem octadOddOmega_inside (o : Fin 759) (d f : Fin 2048) (a b : Fin 8)
    (hab : a ≠ b)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d) :
    griessOctadOmegaCoefficient (trialityXor (octadTensorCharacterLabel o f)
      (trialityOctadPairShift a b)) +
      griessOddOmegaCoefficient d (golayOctadCoordinate o a) +
      griessOddOmegaCoefficient f (golayOctadCoordinate o b) +
        octadSpinCode o 11 = 0 := by
  apply (qSign_eq_one_iff _).mp
  rw [octadOddOmega_sign o _ d f _ _ hd, octadTensor_pair_diagonal o f a b hab]
  have ho : qSign (golayEncoder (octadSpinCode o) (golayOctadCoordinate o a)) = -1 := by
    rw [show octadSpinCode o = golayLabelCoefficients (golayOctadLabel o) from rfl,
      qSign_golayEncoder_label, golayOctadCoordinate_mem]
    rfl
  rw [ho]
  change -(trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) *
    qSign (octadTensorRestriction o f a) * qSign (octadTensorRestriction o f b) *
    (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) *
    qSign (octadTensorRestriction o f a) * qSign (octadTensorRestriction o f b) * (-1) = 1
  calc
    _ = ((trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ) *
      (trialityIntegerDiagonal (octadTensorCharacterLabel o f) : ℝ)) *
      (qSign (octadTensorRestriction o f a) * qSign (octadTensorRestriction o f a)) *
      (qSign (octadTensorRestriction o f b) * qSign (octadTensorRestriction o f b)) := by ring
    _ = 1 := by rw [diagonal_real_sq, qSign_sq, qSign_sq]; norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
