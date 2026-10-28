/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A complete inverse source catalogue for the actual sixth odd-short labels. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PhysicalSupport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The thirty-two actual reached odd-short code labels. -/
def monsterNortonLine01OddCodeLabel : Fin 32 → Fin 2048 :=
  ![1024, 1025, 1026, 1027, 1036, 1037, 1038, 1039,
      1360, 1361, 1362, 1363, 1372, 1373, 1374, 1375,
      1696, 1697, 1698, 1699, 1708, 1709, 1710, 1711,
      2032, 2033, 2034, 2035, 2044, 2045, 2046, 2047]

/-- The direct five-bit inverse on the actual reached odd-short code catalogue. -/
def monsterNortonLine01OddCodeLookup (d : Fin 2048) : Fin 32 :=
  ⟨(d.val % 2 + 2 * (d.val / 2 % 2) + 4 * (d.val / 8 % 2) +
    8 * (d.val / 256 % 2) + 16 * (d.val / 512 % 2)) % 32, Nat.mod_lt _ (by norm_num)⟩

/-- Exact membership in the reached thirty-two-code catalogue. -/
def monsterNortonLine01OddCodeSupport (d : Fin 2048) : Prop :=
  monsterNortonLine01OddCodeLabel (monsterNortonLine01OddCodeLookup d) = d

instance (d : Fin 2048) : Decidable (monsterNortonLine01OddCodeSupport d) :=
  inferInstanceAs (Decidable (_ = _))

/-- A total physical-slot lookup, exact when the physical coordinate is below sixteen. -/
def monsterNortonLine01OddPhysicalSlot (i : Fin 24) : Fin 16 :=
  ⟨i.val % 16, Nat.mod_lt _ (by norm_num)⟩

/-- The original source code index producing an actual reached odd-short label. -/
def monsterNortonLine01OddSourceA : Fin 32 → Fin 16 → Fin 64 :=
  ![![50, 4, 28, 42, 62, 8, 16, 38,
      56, 14, 22, 32, 52, 2, 26, 44],
    ![47, 25, 1, 55, 62, 8, 16, 38,
      37, 19, 11, 61, 52, 2, 26, 44],
    ![47, 25, 1, 55, 62, 8, 16, 38,
      56, 14, 22, 32, 41, 31, 7, 49],
    ![50, 4, 28, 42, 62, 8, 16, 38,
      37, 19, 11, 61, 41, 31, 7, 49],
    ![47, 25, 1, 55, 35, 21, 13, 59,
      37, 19, 11, 61, 41, 31, 7, 49],
    ![50, 4, 28, 42, 35, 21, 13, 59,
      56, 14, 22, 32, 41, 31, 7, 49],
    ![50, 4, 28, 42, 35, 21, 13, 59,
      37, 19, 11, 61, 52, 2, 26, 44],
    ![47, 25, 1, 55, 35, 21, 13, 59,
      56, 14, 22, 32, 52, 2, 26, 44],
    ![50, 4, 1, 55, 62, 8, 13, 59,
      56, 14, 11, 61, 52, 2, 7, 49],
    ![47, 25, 28, 42, 62, 8, 13, 59,
      37, 19, 22, 32, 52, 2, 7, 49],
    ![47, 25, 28, 42, 62, 8, 13, 59,
      56, 14, 11, 61, 41, 31, 26, 44],
    ![50, 4, 1, 55, 62, 8, 13, 59,
      37, 19, 22, 32, 41, 31, 26, 44],
    ![47, 25, 28, 42, 35, 21, 16, 38,
      37, 19, 22, 32, 41, 31, 26, 44],
    ![50, 4, 1, 55, 35, 21, 16, 38,
      56, 14, 11, 61, 41, 31, 26, 44],
    ![50, 4, 1, 55, 35, 21, 16, 38,
      37, 19, 22, 32, 52, 2, 7, 49],
    ![47, 25, 28, 42, 35, 21, 16, 38,
      56, 14, 11, 61, 52, 2, 7, 49],
    ![50, 25, 28, 55, 62, 21, 16, 59,
      56, 19, 22, 61, 52, 31, 26, 49],
    ![47, 4, 1, 42, 62, 21, 16, 59,
      37, 14, 11, 32, 52, 31, 26, 49],
    ![47, 4, 1, 42, 62, 21, 16, 59,
      56, 19, 22, 61, 41, 2, 7, 44],
    ![50, 25, 28, 55, 62, 21, 16, 59,
      37, 14, 11, 32, 41, 2, 7, 44],
    ![47, 4, 1, 42, 35, 8, 13, 38,
      37, 14, 11, 32, 41, 2, 7, 44],
    ![50, 25, 28, 55, 35, 8, 13, 38,
      56, 19, 22, 61, 41, 2, 7, 44],
    ![50, 25, 28, 55, 35, 8, 13, 38,
      37, 14, 11, 32, 52, 31, 26, 49],
    ![47, 4, 1, 42, 35, 8, 13, 38,
      56, 19, 22, 61, 52, 31, 26, 49],
    ![50, 25, 1, 42, 62, 21, 13, 38,
      56, 19, 11, 32, 52, 31, 7, 44],
    ![47, 4, 28, 55, 62, 21, 13, 38,
      37, 14, 22, 61, 52, 31, 7, 44],
    ![47, 4, 28, 55, 62, 21, 13, 38,
      56, 19, 11, 32, 41, 2, 26, 49],
    ![50, 25, 1, 42, 62, 21, 13, 38,
      37, 14, 22, 61, 41, 2, 26, 49],
    ![47, 4, 28, 55, 35, 8, 16, 59,
      37, 14, 22, 61, 41, 2, 26, 49],
    ![50, 25, 1, 42, 35, 8, 16, 59,
      56, 19, 11, 32, 41, 2, 26, 49],
    ![50, 25, 1, 42, 35, 8, 16, 59,
      37, 14, 22, 61, 52, 31, 7, 44],
    ![47, 4, 28, 55, 35, 8, 16, 59,
      56, 19, 11, 32, 52, 31, 7, 44]]

/-- The original physical column slot producing an actual reached odd-short label. -/
def monsterNortonLine01OddSourceK : Fin 32 → Fin 16 → Fin 16 :=
  ![![11, 11, 11, 11, 11, 11, 11, 11,
      11, 11, 11, 11, 11, 11, 11, 11],
    ![13, 13, 13, 13, 13, 13, 13, 13,
      13, 13, 13, 13, 13, 13, 13, 13],
    ![1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1],
    ![15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15],
    ![11, 11, 11, 11, 11, 11, 11, 11,
      11, 11, 11, 11, 11, 11, 11, 11],
    ![13, 13, 13, 13, 13, 13, 13, 13,
      13, 13, 13, 13, 13, 13, 13, 13],
    ![1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1],
    ![15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15],
    ![3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 3, 3, 3, 3, 3, 3],
    ![4, 4, 4, 4, 4, 4, 4, 4,
      4, 4, 4, 4, 4, 4, 4, 4],
    ![6, 6, 6, 6, 6, 6, 6, 6,
      6, 6, 6, 6, 6, 6, 6, 6],
    ![5, 5, 5, 5, 5, 5, 5, 5,
      5, 5, 5, 5, 5, 5, 5, 5],
    ![3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 3, 3, 3, 3, 3, 3],
    ![4, 4, 4, 4, 4, 4, 4, 4,
      4, 4, 4, 4, 4, 4, 4, 4],
    ![6, 6, 6, 6, 6, 6, 6, 6,
      6, 6, 6, 6, 6, 6, 6, 6],
    ![5, 5, 5, 5, 5, 5, 5, 5,
      5, 5, 5, 5, 5, 5, 5, 5],
    ![7, 7, 7, 7, 7, 7, 7, 7,
      7, 7, 7, 7, 7, 7, 7, 7],
    ![9, 9, 9, 9, 9, 9, 9, 9,
      9, 9, 9, 9, 9, 9, 9, 9],
    ![2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 2, 2, 2, 2, 2, 2],
    ![8, 8, 8, 8, 8, 8, 8, 8,
      8, 8, 8, 8, 8, 8, 8, 8],
    ![7, 7, 7, 7, 7, 7, 7, 7,
      7, 7, 7, 7, 7, 7, 7, 7],
    ![9, 9, 9, 9, 9, 9, 9, 9,
      9, 9, 9, 9, 9, 9, 9, 9],
    ![2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 2, 2, 2, 2, 2, 2],
    ![8, 8, 8, 8, 8, 8, 8, 8,
      8, 8, 8, 8, 8, 8, 8, 8],
    ![10, 10, 10, 10, 10, 10, 10, 10,
      10, 10, 10, 10, 10, 10, 10, 10],
    ![12, 12, 12, 12, 12, 12, 12, 12,
      12, 12, 12, 12, 12, 12, 12, 12],
    ![0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0],
    ![14, 14, 14, 14, 14, 14, 14, 14,
      14, 14, 14, 14, 14, 14, 14, 14],
    ![10, 10, 10, 10, 10, 10, 10, 10,
      10, 10, 10, 10, 10, 10, 10, 10],
    ![12, 12, 12, 12, 12, 12, 12, 12,
      12, 12, 12, 12, 12, 12, 12, 12],
    ![0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0],
    ![14, 14, 14, 14, 14, 14, 14, 14,
      14, 14, 14, 14, 14, 14, 14, 14]]

set_option maxRecDepth 10000 in
/-- Every inverse lookup entry has the exact actual odd family, source code, and physical label. -/
theorem monsterNortonLine01OddSource_right (p : Fin 32) (i : Fin 16) :
    monsterNortonLine01ShortInverseIsOctad (monsterNortonLine01OddSourceA p i) = false ∧
      monsterNortonLine01ShortInverseOddCode (monsterNortonLine01OddSourceA p i)
        (monsterNortonLine01OddSourceK p i) = monsterNortonLine01OddCodeLabel p ∧
      monsterNortonLine01ShortInverseOddCoordinate (monsterNortonLine01OddSourceA p i)
        (monsterNortonLine01OddSourceK p i) = ⟨i.val, by omega⟩ := by
  revert p i
  decide +kernel

set_option maxRecDepth 10000 in
/-- All actual odd-short source entries are recovered by their finite inverse catalogue. -/
theorem monsterNortonLine01OddSource_left (a : Fin 64) (k : Fin 16)
    (h : monsterNortonLine01ShortInverseIsOctad a = false) :
    monsterNortonLine01OddCodeSupport (monsterNortonLine01ShortInverseOddCode a k) ∧
      monsterNortonLine01OddSourceA
        (monsterNortonLine01OddCodeLookup (monsterNortonLine01ShortInverseOddCode a k))
        (monsterNortonLine01OddPhysicalSlot (monsterNortonLine01ShortInverseOddCoordinate a k)) =
          a ∧
      monsterNortonLine01OddSourceK
        (monsterNortonLine01OddCodeLookup (monsterNortonLine01ShortInverseOddCode a k))
        (monsterNortonLine01OddPhysicalSlot (monsterNortonLine01ShortInverseOddCoordinate a k)) =
          k := by
  revert a k h
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
