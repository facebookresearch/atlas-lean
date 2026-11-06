/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortArithmeticCertificates

/-! Explicit physical pair inputs retain the original catalogue and genuine local phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The genuine preferred-pair catalogue index of an explicitly checked physical pair. -/
def generatedSeventhXiShortInputIndex (p : Fin 276) : Fin 276 :=
  griessPairIndex (generatedSeventhXiShortInputCoordinates p).1
    (generatedSeventhXiShortInputCoordinates p).2
    (ne_of_lt (generatedSeventhXiShort_input_pairs.1 p))

/-- The catalogue index has exactly its certified physical coordinates. -/
theorem generatedSeventhXiShortInputIndex_coordinates (p : Fin 276) :
    griessCoordinatePair (generatedSeventhXiShortInputIndex p) =
      generatedSeventhXiShortInputCoordinates p := by
  rw [generatedSeventhXiShortInputIndex, griessPairIndex_coordinates,
    ite_eq_left (generatedSeventhXiShort_input_pairs.1 p)]

/-- The explicitly listed input pairs cover the entire genuine pair catalogue. -/
def generatedSeventhXiShortInputEquiv : Equiv.Perm (Fin 276) :=
  Equiv.ofBijective generatedSeventhXiShortInputIndex (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_, rfl⟩
    intro p q h
    apply generatedSeventhXiShort_input_pairs.2 p q
    simpa only [generatedSeventhXiShortInputIndex_coordinates] using
      congrArg griessCoordinatePair h)

/-- The actual preferred short label of each explicitly enumerated input. -/
def generatedSeventhXiShortInputLabel (s : Fin 2) (p : Fin 276) : GriessShortIndex :=
  Sum.inl (s, generatedSeventhXiShortInputIndex p)

/-- The explicit arithmetic vector is exactly the genuine preferred short vector. -/
theorem generatedSeventhXiShortInputLabel_integral (s : Fin 2) (p : Fin 276) :
    griessShortIntegral (generatedSeventhXiShortInputLabel s p) =
      generatedSeventhXiShortInputIntegral s p := by
  funext i
  simp only [generatedSeventhXiShortInputLabel, griessShortIntegral,
    generatedSeventhXiShortInputIndex_coordinates, generatedSeventhXiShortInputIntegral]
  split_ifs <;> rfl

/-- Each finite physical and phase certificate applies to its actual pair input. -/
theorem generatedSeventhXiShort_arithmetic_point (s : Fin 2) (p : Fin 276) :
    (∀ j : Fin 24,
      8 * generatedSeventhXiShortPhysicalSign s p * generatedSeventhXiShortOutputIntegral s p j =
        ∑ k : Fin 24, generatedSeventhFrameVectorData 7 k j *
          generatedSeventhXiShortInputIntegral s p k) ∧
    toAdd (generatedSeventhXiMiddleQHom
      (generatedSeventhXiShortIntegerQ (generatedSeventhXiShortInputIntegral s p))).coeff =
        (generatedSeventhXiShortPhaseBit s p : ZMod 2) := by
  let b : Fin 18 := ⟨p.val / 16, by omega⟩
  let i : Fin 16 := ⟨p.val % 16, Nat.mod_lt _ (by decide)⟩
  have hp : 16 * b.val + i.val < 276 := by dsimp only [b, i]; omega
  have hd : (⟨16 * b.val + i.val, hp⟩ : Fin 276) = p := by
    apply Fin.ext
    dsimp only [b, i]
    omega
  have hc := generatedSeventhXiShort_arithmetic s b i
  rw [dite_eq_left hp] at hc
  dsimp only at hc
  rw [hd] at hc
  rw [generatedSeventhXiShortIntegerQ_input s p
    (generatedSeventhXiShort_input_pairs.1 p)]
  exact hc

/-- Every listed input's central phase is the original genuine local short-action phase. -/
theorem generatedSeventhXiShortInputLabel_phase (s : Fin 2) (p : Fin 276) :
    localShortPhase generatedSeventhLocalFiber (generatedSeventhXiShortInputLabel s p) =
      (generatedSeventhXiShortPhaseBit s p : ZMod 2) := by
  have he : griessShortQ (generatedSeventhXiShortInputLabel s p) =
      generatedSeventhXiShortIntegerQ (generatedSeventhXiShortInputIntegral s p) := by
    rw [← monsterNortonShortQ_eq]
    simp only [monsterNortonShortQ, generatedSeventhXiShortInputLabel_integral,
      generatedSeventhXiShortIntegerQ]
  change toAdd (spinConjugation generatedSeventhLocalFiber.val.1
    (griessShortQ (generatedSeventhXiShortInputLabel s p))).coeff = _
  rw [he]
  have hh := DFunLike.congr_fun generatedSeventhXiMiddleQHom_eq_original
    (generatedSeventhXiShortIntegerQ (generatedSeventhXiShortInputIntegral s p))
  change generatedSeventhXiMiddleQHom _ = spinConjugation generatedSeventhLocalFiber.val.1 _ at hh
  rw [← hh]
  exact (generatedSeventhXiShort_arithmetic_point s p).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
