/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ParkerThetaAddition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddTheta
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseLabels

/-! Small candidate tables for the original Parker theta, with explicit source semantics. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Candidate lower-half theta masks; equality with the original formula is checked separately. -/
def generatedSeventhXiShortThetaLowBits : ℕ :=
  0xa1e468c2a202100f00f40140240c40440a40900740840640500b40300d00e000 +
    (0x856c62d86d76c978a39454c15201100f00042e6ad6835eb5c57463687677495c <<< 256) +
    (0x43e7fd7c367b6455861b85b758964a2747cc3f203100f00041e55d54379b7 <<< 512)

/-- Candidate upper-half theta masks, including the actual omega coefficient. -/
def generatedSeventhXiShortThetaHighBits : ℕ :=
  0x360100e00e00e00043342941540142541343940141943542340100e00e00e000 +
    (0x1343940141943542340100e00e00e00073372971570152551353950161963562 <<< 256) +
    (0x73372971570152551353950161963562360100e00e00e0004334294154014254 <<< 512)

/-- Candidate cross-polar masks of the six lower basis elements against upper-half words. -/
def generatedSeventhXiShortThetaCrossBits : Fin 6 → ℕ :=
  ![
    0xe20e00e00e00e00e300300300300100100100100200200200200000000000000 +
    (0x10010020020020020000000000000030e30e30e30e10e10e10e10e20e20e20 <<< 256) +
    (0x30e30e30e30e10e10e10e10e20e20e20e20e00e00e00e00e3003003003001001 <<< 512),
    0xd0ad3fd15d2ad00d3001a02500f03a01002f00503501f02000a03f01502a0000 +
    (0x2f00503501f02000a03f01502a000030d1ad25d0fd3ad10d2fd05d35d1fd20 <<< 256) +
    (0x30d1ad25d0fd3ad10d2fd05d35d1fd20d0ad3fd15d2ad00d3001a02500f03a01 <<< 512),
    0xb07b1eb27b39b00b1702e03000901002903700e01902003e00701e0270390000 +
    (0x903700e01902003e00701e027039000017b2eb30b09b10b29b37b0eb19b20b3e <<< 256) +
    (0x17b2eb30b09b10b29b37b0eb19b20b3eb07b1eb27b39b00b1702e03000901002 <<< 512),
    0x70d72d73671b70072b03001d00602603d01000b02003b01600d02d03601b0000 +
    (0xd01000b02003b01600d02d03601b00002b73071d70672673d71070b72073b716 <<< 256) +
    (0x2b73071d70672673d71070b72073b71670d72d73671b70072b03001d00602603 <<< 512),
    0x8c10a30620c00014c34024a0461c03cc2c60ca18638a28008c10a30620c000 +
    (0xcc2c60ca18638a28008c10a30620c00014c34024a0461c03cc2c60ca18638a28 <<< 256) +
    (0x14c34024a0461c03cc2c60ca18638a28008c10a30620c00014c34024a0461c03 <<< 512),
    0xc0c620610c30a00028c18638008a24a14034604c2c01ca3cc0c620610c30a000 +
    (0x4034604c2c01ca3cc0c620610c30a00028c18638008a24a14034604c2c01ca3c <<< 256) +
    (0x28c18638008a24a14034604c2c01ca3cc0c620610c30a00028c18638008a24a1 <<< 512)
  ]

/-- The lower-half source label of an original codeword. -/
def generatedSeventhXiShortThetaLowCode (d : Fin 4096) : Fin 64 :=
  ⟨d.val % 64, Nat.mod_lt _ (by norm_num)⟩

/-- The upper-half source label, retaining the original omega bit. -/
def generatedSeventhXiShortThetaHighCode (d : Fin 4096) : Fin 64 :=
  ⟨d.val / 64, by omega⟩

/-- Read one candidate theta mask for a lower source word. -/
def generatedSeventhXiShortThetaLow (d : Fin 64) : Fin 4096 :=
  ⟨(generatedSeventhXiShortThetaLowBits >>> (12*d.val)) % 4096,
    Nat.mod_lt _ (by norm_num)⟩

/-- Read one candidate theta mask for an upper source word. -/
def generatedSeventhXiShortThetaHigh (d : Fin 64) : Fin 4096 :=
  ⟨(generatedSeventhXiShortThetaHighBits >>> (12*d.val)) % 4096,
    Nat.mod_lt _ (by norm_num)⟩

/-- Read one candidate cross-polar mask against an upper source word. -/
def generatedSeventhXiShortThetaCross (i : Fin 6) (d : Fin 64) : Fin 4096 :=
  ⟨(generatedSeventhXiShortThetaCrossBits i >>> (12*d.val)) % 4096,
    Nat.mod_lt _ (by norm_num)⟩

/-- XOR of the six selected original cross-polar source masks. -/
def generatedSeventhXiShortThetaCrossSum (l h : Fin 64) : Fin 4096 :=
  (List.finRange 6).foldl (fun c i =>
    if l.val.testBit i.val then monsterNortonBitXor c (generatedSeventhXiShortThetaCross i h)
    else c) 0

/-- Candidate theta evaluator retaining both original code halves and their polar correction. -/
def generatedSeventhXiShortThetaSplit (d : Fin 4096) : Fin 4096 :=
  let l := generatedSeventhXiShortThetaLowCode d
  let h := generatedSeventhXiShortThetaHighCode d
  monsterNortonBitXor (generatedSeventhXiShortThetaLow l)
    (monsterNortonBitXor (generatedSeventhXiShortThetaHigh h)
      (generatedSeventhXiShortThetaCrossSum l h))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
