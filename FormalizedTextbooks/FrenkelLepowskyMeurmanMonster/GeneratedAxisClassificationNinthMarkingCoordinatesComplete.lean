/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinateCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesPacket08

/-! The144 original candidate marking labels have their actual integer and intrinsic binary
coordinates, after all eighteen finite coordinate certificates have been kernel checked.
Actual coefficient classification remains the separate original source replay. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Every original candidate marking label has both checked actual coordinate certificates. -/
theorem generatedNinth_marking_coordinate_certificate_all (k : Fin 144) :
    GeneratedNinthMarkingCoordinateCertificate k := by
  have hblock : ∀ (j : Fin 9) (n : Fin 16),
      GeneratedNinthMarkingCoordinateCertificate ⟨16 * j.val + n.val, by omega⟩ := by
    intro j
    fin_cases j <;> intro n
    · exact ⟨generatedNinth_marking_integer_packet_00 n,
        generatedNinth_marking_binary_packet_00 n⟩
    · exact ⟨generatedNinth_marking_integer_packet_01 n,
        generatedNinth_marking_binary_packet_01 n⟩
    · exact ⟨generatedNinth_marking_integer_packet_02 n,
        generatedNinth_marking_binary_packet_02 n⟩
    · exact ⟨generatedNinth_marking_integer_packet_03 n,
        generatedNinth_marking_binary_packet_03 n⟩
    · exact ⟨generatedNinth_marking_integer_packet_04 n,
        generatedNinth_marking_binary_packet_04 n⟩
    · exact ⟨generatedNinth_marking_integer_packet_05 n,
        generatedNinth_marking_binary_packet_05 n⟩
    · exact ⟨generatedNinth_marking_integer_packet_06 n,
        generatedNinth_marking_binary_packet_06 n⟩
    · exact ⟨generatedNinth_marking_integer_packet_07 n,
        generatedNinth_marking_binary_packet_07 n⟩
    · exact ⟨generatedNinth_marking_integer_packet_08 n,
        generatedNinth_marking_binary_packet_08 n⟩
  let j : Fin 9 := ⟨k.val / 16, by omega⟩
  let n : Fin 16 := ⟨k.val % 16, Nat.mod_lt _ (by decide)⟩
  have hk : (⟨16 * j.val + n.val, by omega⟩ : Fin 144) = k := by
    apply Fin.ext
    dsimp [j, n]
    omega
  rw [← hk]
  exact hblock j n

/-- Every original candidate marking mask is the actual base of its intrinsic preferred lift. -/
theorem generatedNinth_marking_coordinate_all (k : Fin 144) :
    toAdd (griessShortQ (generatedNinthMarkingLabel k)).base =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthMarkingMask k) :=
  generatedNinth_marking_coordinate_actual k
    (generatedNinth_marking_coordinate_certificate_all k)

/-- The144 finite masks give exactly the complete actual candidate short-class carrier. -/
theorem generatedNinth_marked_short_classes_eq_coordinate_range :
    generatedNinthMarkedShortClasses = Set.range (fun k : Fin 144 =>
      leechHyperbolicCoordinates.symm
        (monsterCo1GeometryBinaryMaskDecode (generatedNinthMarkingMask k))) :=
  generatedNinth_marked_short_classes_of_coordinate_certificates
    generatedNinth_marking_coordinate_certificate_all

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
