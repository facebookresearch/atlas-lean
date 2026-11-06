/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedData

/-! Finite evaluators for every labelled signed coefficient of the canonical short packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Read the complete source code of an occurring octad family. -/
def generatedSeventhXiShortPackedOctadCode (g : Fin 231) : Fin 4096 :=
  ⟨(generatedSeventhXiShortPackedOctadCodeRows ⟨g.val / 64, by omega⟩ >>>
    (12 * (g.val % 64))) % 4096, Nat.mod_lt _ (by decide)⟩

/-- Read the complete source theta of an occurring octad family. -/
def generatedSeventhXiShortPackedOctadTheta (g : Fin 231) : Fin 4096 :=
  ⟨(generatedSeventhXiShortPackedOctadThetaRows ⟨g.val / 64, by omega⟩ >>>
    (12 * (g.val % 64))) % 4096, Nat.mod_lt _ (by decide)⟩

/-- Read an increasing physical coordinate of an occurring octad. -/
def generatedSeventhXiShortPackedOctadCoordinate (g : Fin 231) (k : Fin 8) : Fin 24 :=
  ⟨((generatedSeventhXiShortPackedOctadCoordinateRows ⟨g.val / 64, by omega⟩ >>>
    (40 * (g.val % 64) + 5 * k.val)) % 32) % 24, Nat.mod_lt _ (by decide)⟩

/-- Read one original sign-and-weight slot of an occurring octad family. -/
def generatedSeventhXiShortPackedOctadSlot (g : Fin 231) (k : Fin 3) : ℕ :=
  (generatedSeventhXiShortPackedOctadSlotRows ⟨g.val / 64, by omega⟩ >>>
    (27 * (g.val % 64) + 9 * k.val)) % 512

/-- Read an original sixty-four-state sign label, with zero for an absent slot. -/
def generatedSeventhXiShortPackedOctadSign (g : Fin 231) (k : Fin 3) : Fin 64 :=
  ⟨generatedSeventhXiShortPackedOctadSlot g k % 64, Nat.mod_lt _ (by decide)⟩

/-- Decode the complete signed integer incoming weight; absent slots have zero. -/
def generatedSeventhXiShortPackedOctadWeight (g : Fin 231) (k : Fin 3) : ℤ :=
  let w := (generatedSeventhXiShortPackedOctadSlot g k >>> 6) % 8
  if w = 1 then 1 else if w = 2 then -1 else if w = 3 then 3 else if w = 4 then -3 else 0

/-- Read every selected physical negative-position syndrome of an occurring octad. -/
def generatedSeventhXiShortPackedOctadSyndrome (g : Fin 231) (e : Fin 64) : Fin 4096 :=
  ⟨(generatedSeventhXiShortPackedOctadSyndromeRows
      ⟨g.val / 16, by omega⟩ ⟨g.val % 16, Nat.mod_lt _ (by decide)⟩ >>>
    (12 * e.val)) % 4096, Nat.mod_lt _ (by decide)⟩

/-- Read a low code label with nonzero canonical outgoing odd coefficients. -/
def generatedSeventhXiShortPackedOddCode (g : Fin 512) : Fin 2048 :=
  ⟨(generatedSeventhXiShortPackedOddCodeRows ⟨g.val / 64, by omega⟩ >>>
    (11 * (g.val % 64))) % 2048, Nat.mod_lt _ (by decide)⟩

/-- Read the complete theta of an occurring odd code family. -/
def generatedSeventhXiShortPackedOddTheta (g : Fin 512) : Fin 4096 :=
  ⟨(generatedSeventhXiShortPackedOddThetaRows ⟨g.val / 64, by omega⟩ >>>
    (12 * (g.val % 64))) % 4096, Nat.mod_lt _ (by decide)⟩

/-- Read the full physical Golay mask of an occurring odd code. -/
def generatedSeventhXiShortPackedOddMask (g : Fin 512) : ℕ :=
  (generatedSeventhXiShortPackedOddMaskRows ⟨g.val / 64, by omega⟩ >>>
    (24 * (g.val % 64))) % 16777216

/-- Read the low-code family's inverse index, retaining the explicit absent-family sentinel. -/
def generatedSeventhXiShortPackedOddInverse (d : Fin 2048) : ℕ :=
  (generatedSeventhXiShortPackedOddInverseRows ⟨d.val / 64, by omega⟩ >>>
    (10 * (d.val % 64))) % 1024

/-- Read the complete original sixty-four-row integer Fourier sign. -/
def generatedSeventhXiShortPackedFourierSign (e f : Fin 64) : ℤ :=
  if (generatedSeventhXiShortPackedFourierSignRows e).testBit f.val then -1 else 1

/-- The source half-weight bit of the octad representative. -/
def generatedSeventhXiShortPackedOmega (e : Fin 64) : Bool :=
  generatedSeventhXiShortPackedOmegaBits.testBit e.val

/-- The complete finite preferred-Q mask of an occurring octad and sign. -/
def generatedSeventhXiShortPackedOctadMask (g : Fin 231) (e : Fin 64) : ℕ :=
  ((generatedSeventhXiShortPackedOctadCode g).val ^^^
    (if generatedSeventhXiShortPackedOmega e then 2048 else 0)) % 4096 |||
    ((((generatedSeventhXiShortPackedOctadTheta g).val ^^^
      (generatedSeventhXiShortPackedOctadSyndrome g e).val) % 4096) <<< 12)

/-- The complete finite preferred-Q mask of an occurring odd vector. -/
def generatedSeventhXiShortPackedOddPreferredMask (g : Fin 512) (j : Fin 24) : ℕ :=
  let b := Bool.xor (generatedSeventhXiShortPackedOddWeightBits.testBit g.val)
    ((generatedSeventhXiShortPackedOddMask g).testBit j.val)
  ((generatedSeventhXiShortPackedOddCode g).val ^^^ (if b then 2048 else 0)) % 4096 |||
    ((((generatedSeventhXiShortPackedOddTheta g).val ^^^
      (generatedSeventhXiShortCocodeColumn j).val) % 4096) <<< 12)

/-- The complete outgoing signed octad numerator, including every incoming source slot. -/
def generatedSeventhXiShortPackedOctadCoefficient (g : Fin 231) (e : Fin 64) : ℤ :=
  ∑ k : Fin 3, generatedSeventhXiShortPackedOctadWeight g k *
    generatedSeventhXiShortPackedFourierSign e (generatedSeventhXiShortPackedOctadSign g k)

/-- The complete outgoing odd numerator, retaining its original spin and quarter-weight signs. -/
def generatedSeventhXiShortPackedOddCoefficient (g : Fin 512) (j : Fin 24) : ℤ :=
  (if generatedSeventhXiShortPackedOddSignBits.testBit g.val then -1 else 1) *
    generatedSeventhXiTensorFrame j

/-- The complete source mask of each labelled coefficient in the full canonical short packet. -/
def generatedSeventhXiShortPacketMask (k : Fin 27624) : ℕ :=
  if h : k.val < 552 then
    let s : Fin 2 := ⟨k.val / 276, by omega⟩
    let p : Fin 276 := ⟨k.val % 276, Nat.mod_lt _ (by decide)⟩
    generatedSeventhXiShortQJoinMask (if s = 0 then 0 else 2048)
      (monsterNortonBitXor
        (generatedSeventhXiShortCocodeColumn (generatedSeventhXiShortInputCoordinates p).1)
        (generatedSeventhXiShortCocodeColumn (generatedSeventhXiShortInputCoordinates p).2))
  else if h : k.val < 15336 then
    generatedSeventhXiShortPackedOctadMask ⟨(k.val - 552) / 64, by omega⟩
      ⟨(k.val - 552) % 64, Nat.mod_lt _ (by decide)⟩
  else
    generatedSeventhXiShortPackedOddPreferredMask ⟨(k.val - 15336) / 24, by omega⟩
      ⟨(k.val - 15336) % 24, Nat.mod_lt _ (by decide)⟩

/-- Every signed integer numerator in the full canonical short packet. -/
def generatedSeventhXiShortPacketCoefficient (k : Fin 27624) : ℤ :=
  if h : k.val < 552 then
    let s : Fin 2 := ⟨k.val / 276, by omega⟩
    let p : Fin 276 := ⟨k.val % 276, Nat.mod_lt _ (by decide)⟩
    (if p.val = 248 ∨ p.val = 250 ∨ p.val = 256 then 4 else 0) +
      (if s = 0 then 1 else -1) *
        generatedSeventhXiTensorFrame (generatedSeventhXiShortInputCoordinates p).1 *
        generatedSeventhXiTensorFrame (generatedSeventhXiShortInputCoordinates p).2
  else if h : k.val < 15336 then
    generatedSeventhXiShortPackedOctadCoefficient ⟨(k.val - 552) / 64, by omega⟩
      ⟨(k.val - 552) % 64, Nat.mod_lt _ (by decide)⟩
  else
    generatedSeventhXiShortPackedOddCoefficient ⟨(k.val - 15336) / 24, by omega⟩
      ⟨(k.val - 15336) % 24, Nat.mod_lt _ (by decide)⟩

/-- A proposed finite packet index image, to be certified against the actual whole-Q action. -/
def generatedSeventhXiShortPacketImageIndex (k : Fin 27624) : Fin 27624 :=
  ⟨((generatedSeventhXiShortPackedPermutationRows ⟨k.val / 1024, by omega⟩
      ⟨(k.val / 64) % 16, Nat.mod_lt _ (by decide)⟩ >>>
    (16 * (k.val % 64))) % 65536) % 27624, Nat.mod_lt _ (by decide)⟩

/-- The proposed inverse packet index map, with no bijectivity assumed. -/
def generatedSeventhXiShortPacketInverseIndex (k : Fin 27624) : Fin 27624 :=
  ⟨((generatedSeventhXiShortPackedInverseRows ⟨k.val / 1024, by omega⟩
      ⟨(k.val / 64) % 16, Nat.mod_lt _ (by decide)⟩ >>>
    (16 * (k.val % 64))) % 65536) % 27624, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
