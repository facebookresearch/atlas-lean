/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord

/-! # Packed letter data for the Fifth-derived source words

Literal packed mask data of the code signs occurring in the source words of the Tenth, Root8 and
Ninth source vectors, the packed data of every identification letter, and the decoder of packed
short image lists. All data are re-checked by the kernel where they are used. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Literal packed mask data of the code signs of the Fifth-derived source words. -/
def srcSignP (a : ℕ) : QMaskP :=
  if a = 1024 then
    ⟨0x40010020020010000008000004000002000001000700800b00400d00200e001 |||
      (0x10000008000004000002000001000000800000400000200000100000080000 <<< 256) |||
      (0x8004004008002000 <<< 512),
      0x20000000000000000000000000000000000000800000c00000e |||
      (0x0 <<< 256) |||
      (0x8000000000 <<< 512),
      0x300⟩
  else if a = 2048 then
    ⟨0x400000200000100000080000040000020000010000008000004000002000001 |||
      (0x10000008000004000002000001000000800000400000200000100000080000 <<< 256) |||
      (0x8000004000002000 <<< 512),
      0,
      0x800000⟩
  else if a = 2304 then
    ⟨0xc0040120000010003a08002c0400c602008c0100d00080700040a0002200801 |||
      (0x10080008000004000002000001000000800000400000200000100000080020 <<< 256) |||
      (0xc011004000002000 <<< 512),
      0x4000000000000000000000000c00000800000d00000700000a0000200 |||
      (0x80000000000000000000000000000000000000000000000000000000000000 <<< 256),
      0x800401⟩
  else if a = 2816 then
    ⟨0xc0040120040110002608001a04008a0200460100600080900040f0002300801 |||
      (0x10080008000004000002000001000000800000400000200000100000080030 <<< 256) |||
      (0xc013004000002008 <<< 512),
      0x4000004000000000000000000800000400000600000900000f0000300 |||
      (0x80000000000000000000000000000000000000000000000000000000000000 <<< 256) |||
      (0x8000 <<< 512),
      0x800401⟩
  else if a = 3072 then
    ⟨0x40010020020010000008000004000002000001000700800b00400d00200e001 |||
      (0x10000008000004000002000001000000800000400000200000100000080000 <<< 256) |||
      (0x8004004008002000 <<< 512),
      0x20000000000000000000000000000000000000800000c00000e |||
      (0x0 <<< 256) |||
      (0x8000000000 <<< 512),
      0x800300⟩
  else ⟨0, 0, 0⟩

/-- Packed mask data of an identification letter. -/
def srcLetterP : IdentLetter → QMaskP
  | .xi => sourceLetterP 0
  | .mono l => sourceLetterP (monoLetterIndex l)
  | .qel g => ⟨unitsP, 0, maskOfBits (qLetterBits (qmEncode g).1)⟩
  | .sign a _ => srcSignP a.val

/-- A word with the packed mask data of its letters. -/
def srcWordData (ls : List IdentLetter) : List (IdentLetter × QMaskP) :=
  ls.map (fun l => (l, srcLetterP l))

/-- The letters of a word with data are the word. -/
theorem srcWordData_fst (ls : List IdentLetter) :
    (srcWordData ls).map Prod.fst = ls := by
  unfold srcWordData
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [List.map_cons, ih]

/-- Unpack `n` short terms from `24`-bit fields (label `17` bits, numerator `7` bits + `64`). -/
def srcDecode (t n : ℕ) : List (ℕ × ℤ) :=
  (List.range n).map (fun q => ((t >>> (24 * q)) % 131072,
    (((t >>> (24 * q + 17)) % 128 : ℕ) : ℤ) - 64))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
