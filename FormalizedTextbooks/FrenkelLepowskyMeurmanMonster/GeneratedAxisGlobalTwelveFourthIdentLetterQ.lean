/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentLetterP

/-! # Packed mask data of further code-sign letters

Literal packed mask data (`QMaskP`, worker `gident2`) of the code signs `1, 4, 460, 250` used by
the partner transports into the Fourth family (workers `gfifth`, `gtenth`), on top of
`fourthLetterP`; checked against the exact sign evaluator by `identLetterCheckP` where used. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Literal packed mask data of the further source code signs. -/
def fourthSignQ (a : ℕ) : QMaskP :=
  if a = 1 then
    ⟨0xe400100200200100000080000040010020020010400808400804400802000001 |||
    (0x10000008000004000002000001000000800000400000200000180000080000 <<< 256) |||
    (0x80e0014000002000 <<< 512),
      0x200000000000000000000000020000400000400000400000000 |||
    (0x80000000000000 <<< 256),
      0x330⟩
  else if a = 4 then
    ⟨0xb4000e02000701002700803900403900201e0010400808000004400802400801 |||
    (0x10000008000004000002000001000000800000480000200000100000080000 <<< 256) |||
    (0x80b0044000002000 <<< 512),
      0x2000003800003800001e0000400000000000400000400 |||
    (0x80000000000000000000000000 <<< 256),
      0xf0⟩
  else if a = 460 then
    ⟨0xc40047ba000b6900124880202040380020306010600008590804350002200801 |||
    (0x10080008080004080002000001000000880000480000200000100000080020 <<< 256) |||
    (0xb859cc4000002000 <<< 512),
      0x400000000000100000200000380000300000600000590000350000200 |||
    (0x80000080000080000000000000000080000080000000000000000000000000 <<< 256),
      0x389⟩
  else if a = 250 then
    ⟨0xac0004c20002c1000340802188401898200c5010760008390804400802030801 |||
    (0x10000008080004080002080001080000880000400000280000100000080000 <<< 256) |||
    (0xc678fa4000002000 <<< 512),
      0x2000001800000c0000760000390000400000030 |||
    (0x80000080000080000080000080000000000080000000000000000000 <<< 256),
      0x46d⟩
  else fourthSignP a

/-- Packed mask data of an identification letter, including the further code signs. -/
def fourthLetterQ : IdentLetter → QMaskP
  | .sign a _ => fourthSignQ a.val
  | l => fourthLetterP l

/-- A word with the packed mask data of its letters. -/
def fourthWordDataQ (ls : List IdentLetter) : List (IdentLetter × QMaskP) :=
  ls.map (fun l => (l, fourthLetterQ l))

/-- The letters of a word with data are the word. -/
theorem fourthWordDataQ_fst (ls : List IdentLetter) : (fourthWordDataQ ls).map Prod.fst = ls := by
  unfold fourthWordDataQ
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [List.map_cons, ih]

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
