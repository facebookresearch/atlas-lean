/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRootInputs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthNumerator

/-! Finite physical certificates for the 56 transformed odd short roots.
These arrays come from exact arithmetic in the original Xi/P0 matrices;
the kernel verifies the asserted physical image before it is used. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators

/-- Original preferred input labels, recorded by physical coordinates or octad sign index. -/
def generatedFourthOddRootInputData : Fin 56 → Sum (Fin 2 × Fin 24 × Fin 24) (Fin 64) :=
  ![Sum.inl (0, 10, 14),
  Sum.inl (1, 10, 14),
  Sum.inl (0, 10, 15),
  Sum.inl (1, 10, 15),
  Sum.inl (0, 10, 18),
  Sum.inl (1, 10, 18),
  Sum.inl (0, 10, 19),
  Sum.inl (1, 10, 19),
  Sum.inl (0, 10, 22),
  Sum.inl (1, 10, 22),
  Sum.inl (0, 10, 23),
  Sum.inl (1, 10, 23),
  Sum.inl (0, 11, 14),
  Sum.inl (1, 11, 14),
  Sum.inl (0, 11, 15),
  Sum.inl (1, 11, 15),
  Sum.inl (0, 11, 18),
  Sum.inl (1, 11, 18),
  Sum.inl (0, 11, 19),
  Sum.inl (1, 11, 19),
  Sum.inl (0, 11, 22),
  Sum.inl (1, 11, 22),
  Sum.inl (0, 11, 23),
  Sum.inl (1, 11, 23),
  Sum.inr 1,
  Sum.inr 2,
  Sum.inr 5,
  Sum.inr 6,
  Sum.inr 9,
  Sum.inr 10,
  Sum.inr 13,
  Sum.inr 14,
  Sum.inr 17,
  Sum.inr 18,
  Sum.inr 21,
  Sum.inr 22,
  Sum.inr 25,
  Sum.inr 26,
  Sum.inr 29,
  Sum.inr 30,
  Sum.inr 33,
  Sum.inr 34,
  Sum.inr 37,
  Sum.inr 38,
  Sum.inr 41,
  Sum.inr 42,
  Sum.inr 45,
  Sum.inr 46,
  Sum.inr 49,
  Sum.inr 50,
  Sum.inr 53,
  Sum.inr 54,
  Sum.inr 57,
  Sum.inr 58,
  Sum.inr 61,
  Sum.inr 62]

/-- Original preferred output odd labels, with genuine Golay code index and coordinate. -/
def generatedFourthOddRootOutputData : Fin 56 → Fin 2048 × Fin 24 :=
  ![(1034, 11),
  (1028, 11),
  (1038, 11),
  (1024, 11),
  (1804, 11),
  (1794, 11),
  (1802, 11),
  (1796, 11),
  (1546, 11),
  (1540, 11),
  (1542, 11),
  (1544, 11),
  (1028, 8),
  (1034, 8),
  (1024, 8),
  (1038, 8),
  (1794, 8),
  (1804, 8),
  (1796, 8),
  (1802, 8),
  (1540, 8),
  (1546, 8),
  (1544, 8),
  (1542, 8),
  (1855, 21),
  (1841, 21),
  (1343, 1),
  (1329, 1),
  (1339, 0),
  (1333, 0),
  (1845, 23),
  (1851, 23),
  (1593, 12),
  (1591, 12),
  (1079, 17),
  (1081, 17),
  (1075, 18),
  (1085, 18),
  (1587, 13),
  (1597, 13),
  (1599, 14),
  (1585, 14),
  (1073, 16),
  (1087, 16),
  (1077, 19),
  (1083, 19),
  (1589, 15),
  (1595, 15),
  (1847, 22),
  (1849, 22),
  (1335, 3),
  (1337, 3),
  (1331, 2),
  (1341, 2),
  (1853, 20),
  (1843, 20)]

/-- Preferred physical output labels in the actual short catalogue. -/
def generatedFourthOddRootOutputLabel (j : Fin 56) : GriessShortIndex :=
  Sum.inr (Sum.inr (generatedFourthOddRootOutputData j))

/-- The possible overall physical sign, which does not prescribe the preferred-Q phase. -/
def generatedFourthOddRootPhysicalSign : Fin 56 → ℤ :=
  ![-1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1,
    1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, 1, 1, 1,
    -1, -1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1,
    -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1]

/-- Computational original preferred physical inputs in integer coordinates. -/
def generatedFourthOddRootInputIntegral (j : Fin 56) : Fin 24 → ℤ :=
  match generatedFourthOddRootInputData j with
  | Sum.inl (s, a, b) => fun i =>
      4 * (if i = a then 1 else 0) + (if s = 0 then -4 else 4) * (if i = b then 1 else 0)
  | Sum.inr e => fun i => if Nat.testBit 0xcccc00 i.val then
      if (generatedFourthRootSignMask e).testBit i.val then -2 else 2
    else 0

/-- A computational ordering check for the recorded physical pairs. -/
def generatedFourthOddRootInputOrdered (j : Fin 56) : Bool :=
  match generatedFourthOddRootInputData j with
  | Sum.inl (_, a, b) => decide (a < b)
  | Sum.inr _ => true

/-- Every recorded pair passes the exact finite ordering check. -/
theorem generatedFourthOddRootInputOrdered_eq : ∀ j : Fin 56,
    generatedFourthOddRootInputOrdered j = true := by
  decide +kernel

/-- The listed coordinate-pair inputs use the actual increasing representative. -/
theorem generatedFourthOddRootInputData_lt (j : Fin 56) :
    match generatedFourthOddRootInputData j with
    | Sum.inl (_, a, b) => a < b
    | Sum.inr _ => True := by
  have ho := generatedFourthOddRootInputOrdered_eq j
  cases h : generatedFourthOddRootInputData j with
  | inl z =>
    rcases z with ⟨s, a, b⟩
    simpa only [generatedFourthOddRootInputOrdered, h, decide_eq_true_eq] using ho
  | inr e => trivial

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
-- Check all 1,344 integer coordinates of the inverse images of the 56 odd roots.
/-- Every listed odd root has exactly the listed physical inverse image. -/
theorem generatedFourth_odd_inverse_integral_certificate : ∀ j : Fin 56, ∀ i : Fin 24,
    (generatedFourthInverseNumerator *ᵥ
      griessShortIntegral (generatedFourthOddRootOutputLabel j)) i =
        4 * generatedFourthOddRootPhysicalSign j * generatedFourthOddRootInputIntegral j i := by
  decide +kernel

/-- Distinct listed odd roots are genuinely different catalogue labels. -/
theorem generatedFourthOddRootOutputData_injective :
    Function.Injective generatedFourthOddRootOutputData := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
