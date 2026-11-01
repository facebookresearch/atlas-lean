/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRootInputs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthNumerator

/-! Finite physical certificates for the 64 transformed odd short roots.
These arrays come from exact arithmetic in the original Xi/P0/P1 matrices;
the kernel verifies the asserted physical image before it is used. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators

/-- Original preferred input labels, recorded by physical coordinates or octad sign index. -/
def generatedFifthOddRootInputData : Fin 64 → Sum (Fin 2 × Fin 24 × Fin 24) (Fin 64) :=
  ![Sum.inl (0, 10, 18),
  Sum.inl (1, 10, 18),
  Sum.inl (0, 10, 19),
  Sum.inl (1, 10, 19),
  Sum.inl (0, 10, 22),
  Sum.inl (1, 10, 22),
  Sum.inl (0, 10, 23),
  Sum.inl (1, 10, 23),
  Sum.inl (0, 11, 18),
  Sum.inl (1, 11, 18),
  Sum.inl (0, 11, 19),
  Sum.inl (1, 11, 19),
  Sum.inl (0, 11, 22),
  Sum.inl (1, 11, 22),
  Sum.inl (0, 11, 23),
  Sum.inl (1, 11, 23),
  Sum.inl (0, 14, 18),
  Sum.inl (1, 14, 18),
  Sum.inl (0, 14, 19),
  Sum.inl (1, 14, 19),
  Sum.inl (0, 14, 22),
  Sum.inl (1, 14, 22),
  Sum.inl (0, 14, 23),
  Sum.inl (1, 14, 23),
  Sum.inl (0, 15, 18),
  Sum.inl (1, 15, 18),
  Sum.inl (0, 15, 19),
  Sum.inl (1, 15, 19),
  Sum.inl (0, 15, 22),
  Sum.inl (1, 15, 22),
  Sum.inl (0, 15, 23),
  Sum.inl (1, 15, 23),
  Sum.inr 0,
  Sum.inr 3,
  Sum.inr 5,
  Sum.inr 6,
  Sum.inr 9,
  Sum.inr 10,
  Sum.inr 12,
  Sum.inr 15,
  Sum.inr 16,
  Sum.inr 19,
  Sum.inr 21,
  Sum.inr 22,
  Sum.inr 25,
  Sum.inr 26,
  Sum.inr 28,
  Sum.inr 31,
  Sum.inr 32,
  Sum.inr 35,
  Sum.inr 37,
  Sum.inr 38,
  Sum.inr 41,
  Sum.inr 42,
  Sum.inr 44,
  Sum.inr 47,
  Sum.inr 48,
  Sum.inr 51,
  Sum.inr 53,
  Sum.inr 54,
  Sum.inr 57,
  Sum.inr 58,
  Sum.inr 60,
  Sum.inr 63]

/-- Original preferred output odd labels, with genuine Golay code index and coordinate. -/
def generatedFifthOddRootOutputData : Fin 64 → Fin 2048 × Fin 24 :=
  ![(1721, 19),
  (1719, 16),
  (1727, 16),
  (1713, 19),
  (1971, 19),
  (1981, 16),
  (1983, 16),
  (1969, 19),
  (1724, 18),
  (1714, 17),
  (1722, 17),
  (1716, 18),
  (1974, 17),
  (1976, 18),
  (1978, 18),
  (1972, 17),
  (1795, 1),
  (1805, 0),
  (1797, 1),
  (1803, 0),
  (1545, 1),
  (1543, 0),
  (1541, 1),
  (1547, 0),
  (1804, 2),
  (1794, 3),
  (1802, 2),
  (1796, 3),
  (1542, 3),
  (1544, 2),
  (1546, 3),
  (1540, 2),
  (1152, 0),
  (1163, 0),
  (1332, 1),
  (1329, 1),
  (1339, 0),
  (1342, 0),
  (1153, 1),
  (1162, 1),
  (1412, 19),
  (1423, 16),
  (1072, 16),
  (1077, 19),
  (1087, 16),
  (1082, 19),
  (1413, 19),
  (1422, 16),
  (1410, 17),
  (1417, 18),
  (1078, 17),
  (1075, 18),
  (1081, 17),
  (1084, 18),
  (1411, 17),
  (1416, 18),
  (1160, 2),
  (1155, 2),
  (1340, 2),
  (1337, 2),
  (1331, 3),
  (1334, 3),
  (1161, 3),
  (1154, 3)]

/-- Preferred physical output labels in the actual short catalogue. -/
def generatedFifthOddRootOutputLabel (j : Fin 64) : GriessShortIndex :=
  Sum.inr (Sum.inr (generatedFifthOddRootOutputData j))

/-- The possible overall physical sign, which does not prescribe the preferred-Q phase. -/
def generatedFifthOddRootPhysicalSign : Fin 64 → ℤ :=
  ![-1,
  1,
  -1,
  1,
  -1,
  1,
  -1,
  1,
  -1,
  1,
  -1,
  1,
  -1,
  1,
  -1,
  1,
  1,
  -1,
  1,
  -1,
  1,
  -1,
  1,
  -1,
  -1,
  1,
  -1,
  1,
  -1,
  1,
  -1,
  1,
  -1,
  -1,
  1,
  1,
  -1,
  -1,
  1,
  1,
  1,
  1,
  -1,
  -1,
  1,
  1,
  -1,
  -1,
  1,
  1,
  -1,
  -1,
  1,
  1,
  -1,
  -1,
  1,
  1,
  -1,
  -1,
  1,
  1,
  -1,
  -1]

/-- Computational original preferred physical inputs in integer coordinates. -/
def generatedFifthOddRootInputIntegral (j : Fin 64) : Fin 24 → ℤ :=
  match generatedFifthOddRootInputData j with
  | Sum.inl (s, a, b) => fun i =>
      4 * (if i = a then 1 else 0) + (if s = 0 then -4 else 4) * (if i = b then 1 else 0)
  | Sum.inr e => fun i => if Nat.testBit 0xcccc00 i.val then
      if (generatedFourthRootSignMask e).testBit i.val then -2 else 2
    else 0

/-- A computational ordering check for the recorded physical pairs. -/
def generatedFifthOddRootInputOrdered (j : Fin 64) : Bool :=
  match generatedFifthOddRootInputData j with
  | Sum.inl (_, a, b) => decide (a < b)
  | Sum.inr _ => true

/-- Every recorded pair passes the exact finite ordering check. -/
theorem generatedFifthOddRootInputOrdered_eq : ∀ j : Fin 64,
    generatedFifthOddRootInputOrdered j = true := by
  decide +kernel

/-- The listed coordinate-pair inputs use the actual increasing representative. -/
theorem generatedFifthOddRootInputData_lt (j : Fin 64) :
    match generatedFifthOddRootInputData j with
    | Sum.inl (_, a, b) => a < b
    | Sum.inr _ => True := by
  have ho := generatedFifthOddRootInputOrdered_eq j
  cases h : generatedFifthOddRootInputData j with
  | inl z =>
    rcases z with ⟨s, a, b⟩
    simpa only [generatedFifthOddRootInputOrdered, h, decide_eq_true_eq] using ho
  | inr e => trivial

/-- Distinct listed odd roots are genuinely different catalogue labels. -/
theorem generatedFifthOddRootOutputData_injective :
    Function.Injective generatedFifthOddRootOutputData := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
