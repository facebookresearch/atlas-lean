/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The actual pair-vector lifts and their spin operators in the source dictionary.
Source: Seysen, arXiv:2002.10921v3, §§6.1–6.2 and Table 5.
The two signs are derived from the physical lattice representatives,
including the all-one translation of the plus-pair lift.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceCocode

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

theorem leechModTwo_two_smul (u : LeechModTwo) : (2 : ℕ) • u = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
  have hn : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [hn, zero_smul]

theorem griessPairMinus_lift (p : Fin 276) :
    griessShortLatticeVector (Sum.inl (0, p)) =
      leechCocodeLift (Pi.single (griessCoordinatePair p).1 1 +
        Pi.single (griessCoordinatePair p).2 1) -
        (2 : ℕ) • leechCocodeLift (Pi.single (griessCoordinatePair p).1 1) := by
  apply Subtype.ext
  funext i
  simp [griessShortLatticeVector, griessShortIntegral, leechCocodeLift, leechCocodeVector,
    Finset.sum_add_distrib, Pi.single_apply]
  split_ifs <;> ring

theorem griessPairMinus_class (p : Fin 276) :
    griessShortClass (Sum.inl (0, p)) =
      leechReduction (leechCocodeLift (Pi.single (griessCoordinatePair p).1 1 +
        Pi.single (griessCoordinatePair p).2 1)) := by
  rw [griessShortClass, griessPairMinus_lift, map_sub, map_nsmul,
    leechModTwo_two_smul, sub_zero]

set_option maxHeartbeats 2000000 in
-- Check the all-one source-frame column and its zero Parker adjustment.
theorem leechSourceFrameLift_omega_vector :
    (leechSourceFrameLift (Fin.castAdd 12 (11 : Fin 12))).val = fun _ => 2 := by
  rw [leechSourceFrameLift_vector]
  unfold Matrix.col leechSourceFrameVectors leechSourceCodeVector leechSourceCocodeVector
  decide +kernel

theorem griessPairPlus_lift (p : Fin 276) :
    griessShortLatticeVector (Sum.inl (1, p)) =
      griessShortLatticeVector (Sum.inl (0, p)) +
        leechSourceFrameLift (Fin.castAdd 12 (11 : Fin 12)) -
        (2 : ℕ) • leechCocodeLift (Pi.single (griessCoordinatePair p).2 1) := by
  apply Subtype.ext
  change griessShortIntegral (Sum.inl (1, p)) =
    griessShortIntegral (Sum.inl (0, p)) +
      (leechSourceFrameLift (Fin.castAdd 12 (11 : Fin 12))).val -
      (2 : ℕ) • leechCocodeVector (Pi.single (griessCoordinatePair p).2 1)
  rw [leechSourceFrameLift_omega_vector]
  funext i
  simp [griessShortIntegral, leechCocodeVector, Pi.single_apply]
  split_ifs <;> ring

theorem griessPairPlus_class (p : Fin 276) :
    griessShortClass (Sum.inl (1, p)) =
      griessShortClass (Sum.inl (0, p)) +
        leechReduction (leechSourceFrameLift (Fin.castAdd 12 (11 : Fin 12))) := by
  rw [griessShortClass, griessPairPlus_lift, map_sub, map_add, map_nsmul,
    leechModTwo_two_smul, sub_zero]
  rfl

def griessPairSyndrome (p : Fin 276) : Fin 12 → ZMod 2 := fun k =>
  (golayGeneratorBit k (griessCoordinatePair p).1 : ZMod 2) +
    (golayGeneratorBit k (griessCoordinatePair p).2 : ZMod 2)

theorem griessPairSyndrome_cocode (p : Fin 276) :
    golaySyndrome (integerParity (Pi.single (griessCoordinatePair p).1 1 +
      Pi.single (griessCoordinatePair p).2 1)) = griessPairSyndrome p := by
  ext k
  simp [golaySyndrome, integerParity, griessPairSyndrome, Pi.single_apply,
    add_mul, Finset.sum_add_distrib]

theorem griessPairMinus_coordinates (p : Fin 276) :
    leechHyperbolicCoordinates (griessShortClass (Sum.inl (0, p))) =
      binaryCocodeEmbedding (griessPairSyndrome p) := by
  rw [griessPairMinus_class, leechCocodeLift_coordinates, griessPairSyndrome_cocode]

theorem griessPairPlus_coordinates (p : Fin 276) :
    leechHyperbolicCoordinates (griessShortClass (Sum.inl (1, p))) =
      binaryCocodeEmbedding (griessPairSyndrome p) +
        Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1 := by
  rw [griessPairPlus_class, map_add, griessPairMinus_coordinates,
    leechSourceFrameLift_hyperbolic]

theorem griessPairMinus_translation (p : Fin 276) :
    spinTranslation (griessShortQ (Sum.inl (0, p))) = 0 := by
  ext k
  change leechHyperbolicCoordinates (griessShortClass (Sum.inl (0, p))) (Fin.castAdd 12 k) = 0
  rw [griessPairMinus_coordinates, binaryCocodeEmbedding_left]

theorem griessPairMinus_modulation (p : Fin 276) :
    spinModulation (griessShortQ (Sum.inl (0, p))) = griessPairSyndrome p := by
  ext k
  change leechHyperbolicCoordinates (griessShortClass (Sum.inl (0, p))) (Fin.natAdd 12 k) = _
  rw [griessPairMinus_coordinates, binaryCocodeEmbedding_right]

theorem griessPairPlus_translation (p : Fin 276) :
    spinTranslation (griessShortQ (Sum.inl (1, p))) = Pi.single 11 1 := by
  ext k
  change leechHyperbolicCoordinates (griessShortClass (Sum.inl (1, p))) (Fin.castAdd 12 k) = _
  rw [griessPairPlus_coordinates]
  change binaryCocodeEmbedding (griessPairSyndrome p) (Fin.castAdd 12 k) +
    (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1 : Fin 24 → ZMod 2) (Fin.castAdd 12 k) = _
  rw [binaryCocodeEmbedding_left, zero_add]
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]

theorem griessPairPlus_modulation (p : Fin 276) :
    spinModulation (griessShortQ (Sum.inl (1, p))) = griessPairSyndrome p := by
  ext k
  change leechHyperbolicCoordinates (griessShortClass (Sum.inl (1, p))) (Fin.natAdd 12 k) = _
  rw [griessPairPlus_coordinates]
  have hn : Fin.natAdd 12 k ≠ Fin.castAdd 12 (11 : Fin 12) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  change binaryCocodeEmbedding (griessPairSyndrome p) (Fin.natAdd 12 k) +
    (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1 : Fin 24 → ZMod 2) (Fin.natAdd 12 k) = _
  rw [binaryCocodeEmbedding_right]
  simp only [Pi.single_apply, ite_eq_right hn, add_zero]

theorem griessPairSyndrome_dot (p : Fin 276) (t : SpinIndex) :
    spinDot (griessPairSyndrome p) t =
      golayEncoder t (griessCoordinatePair p).1 + golayEncoder t (griessCoordinatePair p).2 := by
  change (∑ k, ((golayGeneratorBit k (griessCoordinatePair p).1 : ZMod 2) +
    (golayGeneratorBit k (griessCoordinatePair p).2 : ZMod 2)) * t k) =
      (∑ k, t k * (golayGeneratorBit k (griessCoordinatePair p).1 : ZMod 2)) +
      (∑ k, t k * (golayGeneratorBit k (griessCoordinatePair p).2 : ZMod 2))
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> exact mul_comm _ _

/-- The minus-pair lift is exactly the source diagonal character on spin coordinates. -/
theorem spinOperator_griessPairMinus (p : Fin 276) (f : SpinSpace) (t : SpinIndex) :
    spinOperator (griessShortQ (Sum.inl (0, p))) f t =
      qSign (golayEncoder t (griessCoordinatePair p).1 +
        golayEncoder t (griessCoordinatePair p).2) * f t := by
  change qSign (0 + spinDot (spinModulation (griessShortQ (Sum.inl (0, p)))) t) *
    f (t + spinTranslation (griessShortQ (Sum.inl (0, p)))) = _
  rw [griessPairMinus_modulation, griessPairMinus_translation, griessPairSyndrome_dot]
  simp

/-- The plus-pair lift has the same character and translates by the all-one codeword. -/
theorem spinOperator_griessPairPlus (p : Fin 276) (f : SpinSpace) (t : SpinIndex) :
    spinOperator (griessShortQ (Sum.inl (1, p))) f t =
      qSign (golayEncoder t (griessCoordinatePair p).1 +
        golayEncoder t (griessCoordinatePair p).2) * f (t + Pi.single 11 1) := by
  change qSign (0 + spinDot (spinModulation (griessShortQ (Sum.inl (1, p)))) t) *
    f (t + spinTranslation (griessShortQ (Sum.inl (1, p)))) = _
  rw [griessPairPlus_modulation, griessPairPlus_translation, griessPairSyndrome_dot]
  simp
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
