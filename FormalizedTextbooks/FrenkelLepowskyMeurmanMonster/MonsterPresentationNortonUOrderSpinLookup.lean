/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Kernel-checked finite lookup tables for the exact Norton spin numerator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinGamma

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Sixty-four-bit blocks of the negative signs in source lookup table 0. -/
def monsterNortonSpinSignWords0 : Vector ℕ 64 :=
⟨#[
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117
], by decide⟩

/-- Sixty-four-bit blocks of the negative signs in source lookup table 1. -/
def monsterNortonSpinSignWords1 : Vector ℕ 64 :=
⟨#[
  0x2e1221e27bb87448, 0x21e22e1274487bb8, 0xdee2d1128b4884b8, 0xd112dee284b88b48,
  0x2e1221e27bb87448, 0x21e22e1274487bb8, 0xdee2d1128b4884b8, 0xd112dee284b88b48,
  0x74b77b47dee2d112, 0x7b4774b7d112dee2, 0x7bb87448d1edde1d, 0x74487bb8de1dd1ed,
  0x8b4884b8211d2eed, 0x84b88b482eed211d, 0x84478bb72e1221e2, 0x8bb7844721e22e12,
  0x2e1221e27bb87448, 0x21e22e1274487bb8, 0xdee2d1128b4884b8, 0xd112dee284b88b48,
  0x2e1221e27bb87448, 0x21e22e1274487bb8, 0xdee2d1128b4884b8, 0xd112dee284b88b48,
  0x8b4884b8211d2eed, 0x84b88b482eed211d, 0x84478bb72e1221e2, 0x8bb7844721e22e12,
  0x74b77b47dee2d112, 0x7b4774b7d112dee2, 0x7bb87448d1edde1d, 0x74487bb8de1dd1ed,
  0x2e1221e27bb87448, 0x21e22e1274487bb8, 0xdee2d1128b4884b8, 0xd112dee284b88b48,
  0x2e1221e27bb87448, 0x21e22e1274487bb8, 0xdee2d1128b4884b8, 0xd112dee284b88b48,
  0x74b77b47dee2d112, 0x7b4774b7d112dee2, 0x7bb87448d1edde1d, 0x74487bb8de1dd1ed,
  0x8b4884b8211d2eed, 0x84b88b482eed211d, 0x84478bb72e1221e2, 0x8bb7844721e22e12,
  0x2e1221e27bb87448, 0x21e22e1274487bb8, 0xdee2d1128b4884b8, 0xd112dee284b88b48,
  0x2e1221e27bb87448, 0x21e22e1274487bb8, 0xdee2d1128b4884b8, 0xd112dee284b88b48,
  0x8b4884b8211d2eed, 0x84b88b482eed211d, 0x84478bb72e1221e2, 0x8bb7844721e22e12,
  0x74b77b47dee2d112, 0x7b4774b7d112dee2, 0x7bb87448d1edde1d, 0x74487bb8de1dd1ed
], by decide⟩

/-- Sixty-four-bit blocks of the negative signs in source lookup table 2. -/
def monsterNortonSpinSignWords2 : Vector ℕ 64 :=
⟨#[
  0xf66090069006f660, 0x3aac5cca5cca3aac, 0x3aac5cca5cca3aac, 0xf66090069006f660,
  0xa335c5533aac5cca, 0x6ff9099ff6609006, 0x9006f660099f6ff9, 0x5cca3aacc553a335,
  0xa3353aacc5535cca, 0x9006099ff6606ff9, 0x6ff9f660099f9006, 0x5ccac5533aaca335,
  0xf6606ff96ff9f660, 0xc5535cca5ccac553, 0xc5535cca5ccac553, 0xf6606ff96ff9f660,
  0xf66090069006f660, 0x3aac5cca5cca3aac, 0x3aac5cca5cca3aac, 0xf66090069006f660,
  0xa335c5533aac5cca, 0x6ff9099ff6609006, 0x9006f660099f6ff9, 0x5cca3aacc553a335,
  0xa3353aacc5535cca, 0x9006099ff6606ff9, 0x6ff9f660099f9006, 0x5ccac5533aaca335,
  0xf6606ff96ff9f660, 0xc5535cca5ccac553, 0xc5535cca5ccac553, 0xf6606ff96ff9f660,
  0xf66090069006f660, 0x3aac5cca5cca3aac, 0x3aac5cca5cca3aac, 0xf66090069006f660,
  0xa335c5533aac5cca, 0x6ff9099ff6609006, 0x9006f660099f6ff9, 0x5cca3aacc553a335,
  0xa3353aacc5535cca, 0x9006099ff6606ff9, 0x6ff9f660099f9006, 0x5ccac5533aaca335,
  0xf6606ff96ff9f660, 0xc5535cca5ccac553, 0xc5535cca5ccac553, 0xf6606ff96ff9f660,
  0xf66090069006f660, 0x3aac5cca5cca3aac, 0x3aac5cca5cca3aac, 0xf66090069006f660,
  0xa335c5533aac5cca, 0x6ff9099ff6609006, 0x9006f660099f6ff9, 0x5cca3aacc553a335,
  0xa3353aacc5535cca, 0x9006099ff6606ff9, 0x6ff9f660099f9006, 0x5ccac5533aaca335,
  0xf6606ff96ff9f660, 0xc5535cca5ccac553, 0xc5535cca5ccac553, 0xf6606ff96ff9f660
], by decide⟩

/-- Sixty-four-bit blocks of the negative signs in source lookup table 3. -/
def monsterNortonSpinSignWords3 : Vector ℕ 64 :=
⟨#[
  0xf0f00ff5555a55a, 0xff0f0fa55a5555, 0xf00f0000aa55a5a5, 0xf00fa5a5aa55,
  0xf0f00ff5555a55a, 0xff0f0fa55a5555, 0xf00f0000aa55a5a5, 0xf00fa5a5aa55,
  0xff00f0f05aa5aaaa, 0xf0f0ff00aaaa5aa5, 0xffff0ff05a5a55aa, 0xff0ffff55aa5a5a,
  0xff00f0f05aa5aaaa, 0xf0f0ff00aaaa5aa5, 0xffff0ff05a5a55aa, 0xff0ffff55aa5a5a,
  0xaa55a5a5f00f0000, 0xa5a5aa550000f00f, 0x5555a55a0f0f00ff, 0xa55a555500ff0f0f,
  0xaa55a5a5f00f0000, 0xa5a5aa550000f00f, 0x5555a55a0f0f00ff, 0xa55a555500ff0f0f,
  0x5a5a55aaffff0ff0, 0x55aa5a5a0ff0ffff, 0x5aa5aaaaff00f0f0, 0xaaaa5aa5f0f0ff00,
  0x5a5a55aaffff0ff0, 0x55aa5a5a0ff0ffff, 0x5aa5aaaaff00f0f0, 0xaaaa5aa5f0f0ff00,
  0xf0f00ff5555a55a, 0xff0f0fa55a5555, 0xf00f0000aa55a5a5, 0xf00fa5a5aa55,
  0xf0f00ff5555a55a, 0xff0f0fa55a5555, 0xf00f0000aa55a5a5, 0xf00fa5a5aa55,
  0xff0f0fa55a5555, 0xf0f00ff5555a55a, 0xf00fa5a5aa55, 0xf00f0000aa55a5a5,
  0xff0f0fa55a5555, 0xf0f00ff5555a55a, 0xf00fa5a5aa55, 0xf00f0000aa55a5a5,
  0xaa55a5a5f00f0000, 0xa5a5aa550000f00f, 0x5555a55a0f0f00ff, 0xa55a555500ff0f0f,
  0xaa55a5a5f00f0000, 0xa5a5aa550000f00f, 0x5555a55a0f0f00ff, 0xa55a555500ff0f0f,
  0xa5a5aa550000f00f, 0xaa55a5a5f00f0000, 0xa55a555500ff0f0f, 0x5555a55a0f0f00ff,
  0xa5a5aa550000f00f, 0xaa55a5a5f00f0000, 0xa55a555500ff0f0f, 0x5555a55a0f0f00ff
], by decide⟩

/-- Sixty-four-bit blocks of the negative signs in source lookup table 4. -/
def monsterNortonSpinSignWords4 : Vector ℕ 64 :=
⟨#[
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3,
  0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3, 0x3cc33cc33cc33cc3
], by decide⟩

/-- Sixty-four-bit blocks of the negative signs in source lookup table 5. -/
def monsterNortonSpinSignWords5 : Vector ℕ 64 :=
⟨#[
  0x6996699669966996, 0x6996699669966996, 0x6996699669966996, 0x6996699669966996,
  0x9669966996699669, 0x9669966996699669, 0x9669966996699669, 0x9669966996699669,
  0x9669966996699669, 0x9669966996699669, 0x9669966996699669, 0x9669966996699669,
  0x6996699669966996, 0x6996699669966996, 0x6996699669966996, 0x6996699669966996,
  0x9669966996699669, 0x9669966996699669, 0x9669966996699669, 0x9669966996699669,
  0x6996699669966996, 0x6996699669966996, 0x6996699669966996, 0x6996699669966996,
  0x6996699669966996, 0x6996699669966996, 0x6996699669966996, 0x6996699669966996,
  0x9669966996699669, 0x9669966996699669, 0x9669966996699669, 0x9669966996699669,
  0x6996699669966996, 0x6996699669966996, 0x6996699669966996, 0x6996699669966996,
  0x9669966996699669, 0x9669966996699669, 0x9669966996699669, 0x9669966996699669,
  0x9669966996699669, 0x9669966996699669, 0x9669966996699669, 0x9669966996699669,
  0x6996699669966996, 0x6996699669966996, 0x6996699669966996, 0x6996699669966996,
  0x9669966996699669, 0x9669966996699669, 0x9669966996699669, 0x9669966996699669,
  0x6996699669966996, 0x6996699669966996, 0x6996699669966996, 0x6996699669966996,
  0x6996699669966996, 0x6996699669966996, 0x6996699669966996, 0x6996699669966996,
  0x9669966996699669, 0x9669966996699669, 0x9669966996699669, 0x9669966996699669
], by decide⟩

/-- Exact signs for gamma, both Parker inverses, y82 affine phase, and both Q factors. -/
def monsterNortonSpinSign (k : Fin 6) (n : Fin 4096) : ℤ :=
  if ((![monsterNortonSpinSignWords0, monsterNortonSpinSignWords1, monsterNortonSpinSignWords2,
      monsterNortonSpinSignWords3, monsterNortonSpinSignWords4, monsterNortonSpinSignWords5] k).get
      (Fin.ofNat 64 (n.val / 64))).testBit (n.val % 64) then -1 else 1

/-- The actual source column labels of the two code permutation matrices. -/
def monsterNortonSpinCodeColumns (k : Fin 2) : Fin 12 → ℕ :=
  ![![4093, 782, 2316, 2572, 816, 2593, 960, 2383, 12, 2052, 2046, 2048],
    ![684, 1020, 1028, 1032, 16, 64, 32, 128, 51, 205, 1024, 2048]] k

/-- Bitwise linear evaluation of the source permutation column labels. -/
def monsterNortonSpinCodeIndex (k : Fin 2) (n : Fin 4096) : Fin 4096 :=
  Fin.ofNat 4096 ((List.finRange 12).foldl (fun a j =>
    if n.val.testBit j.val then a ^^^ monsterNortonSpinCodeColumns k j else a) 0)

/-- Exact source label changes for both Parker inverses and the y82 affine operator. -/
def monsterNortonSpinIndex (k : Fin 3) (n : Fin 4096) : Fin 4096 :=
  ![monsterNortonSpinCodeIndex 0 n, monsterNortonSpinCodeIndex 1 n,
    if n.val.testBit 11 then n else monsterNortonSpinXor n 82] k

/-- Compact actual y82 quadratic phase row masks. -/
def monsterNortonSpinY82PhaseRows : Fin 12 → ℕ :=
  ![1057, 0, 1652, 1752, 176, 608, 192, 640, 0, 0, 0, 512]

/-- Actual y82 quadratic coefficients read from their compact row masks. -/
def monsterNortonSpinY82PhaseMatrix (i j : Fin 12) : ZMod 2 :=
  if (monsterNortonSpinY82PhaseRows i).testBit j.val then 1 else 0

set_option maxHeartbeats 2000000 in
-- Compact the 144 actual y82 phase coefficients before the 4096-label sign check.
/-- The compact coefficients equal the complete actual source quadratic. -/
theorem monsterNortonSpinY82PhaseMatrix_eq :
    monsterSourceYPhaseMatrix monsterSourceY82Code = monsterNortonSpinY82PhaseMatrix := by
  have h : ∀ i j : Fin 12,
      monsterSourceYPhaseMatrix monsterSourceY82Code i j = monsterNortonSpinY82PhaseMatrix i j := by
    decide +kernel
  exact funext (fun i => funext (h i))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
