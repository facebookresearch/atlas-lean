/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortArithmeticData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairQProducts

/-! Original preferred pair coordinates simplify the repeated finite central-phase checks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The genuine source syndrome of the explicitly listed physical pair. -/
def generatedSeventhXiShortInputSyndrome (p : Fin 276) : SpinIndex := fun k =>
  (golayGeneratorBit k (generatedSeventhXiShortInputCoordinates p).1 : ZMod 2) +
    (golayGeneratorBit k (generatedSeventhXiShortInputCoordinates p).2 : ZMod 2)

/-- The original preferred pair lift expressed in its explicit source hyperbolic coordinates. -/
def generatedSeventhXiShortInputQ (s : Fin 2) (p : Fin 276) : Q :=
  ⟨ofAdd (binaryCocodeEmbedding (generatedSeventhXiShortInputSyndrome p) +
    if s = 0 then 0 else Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1), 1⟩

/-- The preferred integer formula equals the genuine pair coordinates with central bit zero. -/
theorem generatedSeventhXiShortIntegerQ_input (s : Fin 2) (p : Fin 276)
    (hp : (generatedSeventhXiShortInputCoordinates p).1 <
      (generatedSeventhXiShortInputCoordinates p).2) :
    generatedSeventhXiShortIntegerQ (generatedSeventhXiShortInputIntegral s p) =
      generatedSeventhXiShortInputQ s p := by
  let a := (generatedSeventhXiShortInputCoordinates p).1
  let b := (generatedSeventhXiShortInputCoordinates p).2
  let j := griessPairIndex a b (ne_of_lt hp)
  have hj : griessCoordinatePair j = generatedSeventhXiShortInputCoordinates p := by
    have hab : a < b := hp
    simpa only [hab, ite_true] using griessPairIndex_coordinates a b (ne_of_lt hp)
  have hi : griessShortIntegral (Sum.inl (s, j)) =
      generatedSeventhXiShortInputIntegral s p := by
    funext i
    simp only [griessShortIntegral, hj, generatedSeventhXiShortInputIntegral]
    split_ifs <;> norm_num
  have he : generatedSeventhXiShortIntegerQ (generatedSeventhXiShortInputIntegral s p) =
      griessShortQ (Sum.inl (s, j)) := by
    rw [← monsterNortonShortQ_eq]
    simp only [monsterNortonShortQ, hi, generatedSeventhXiShortIntegerQ]
  have hsyn : griessPairSyndrome j = generatedSeventhXiShortInputSyndrome p := by
    funext k
    rw [griessPairSyndrome, hj]
    rfl
  rw [he]
  apply NormalizedCocycleExtension.Extension.ext
  · change ofAdd (leechHyperbolicCoordinates (griessShortClass (Sum.inl (s, j)))) = _
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · rw [griessPairMinus_coordinates, hsyn]
      simp only [generatedSeventhXiShortInputQ, ite_true, add_zero]
    · rw [griessPairPlus_coordinates, hsyn]
      rfl
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
