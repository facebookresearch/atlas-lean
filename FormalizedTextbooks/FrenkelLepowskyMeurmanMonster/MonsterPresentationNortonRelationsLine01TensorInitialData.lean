/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer data for the first two actual tensor steps of the line-pair word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQIntegralVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactIntegerBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUIntegralCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual output source labels in the published 64-term Gaussian enumeration. -/
def monsterNortonLine01InitialSpinIndices : Fin 64 → Fin 4096 :=
  ![2281, 1373, 3087, 443, 3155, 487, 2229, 1281,
    1513, 2141, 271, 3259, 339, 3303, 1461, 2049,
    1511, 2131, 257, 3253, 349, 3305, 1467, 2063,
    2279, 1363, 3073, 437, 3165, 489, 2235, 1295,
    2490, 1038, 3420, 232, 3328, 180, 2534, 1106,
    1210, 2318, 92, 3560, 0, 3508, 1254, 2386,
    1204, 2304, 82, 3558, 14, 3514, 1256, 2396,
    2484, 1024, 3410, 230, 3342, 186, 2536, 1116]

/-- Their complete integer signs, including the resolved actual Norton phase. -/
def monsterNortonLine01InitialSpinSigns : Fin 64 → ℤ :=
  ![1, -1, 1, -1, 1, -1, 1, -1,
    -1, 1, -1, 1, -1, 1, -1, 1,
    -1, 1, -1, 1, -1, 1, -1, 1,
    1, -1, 1, -1, 1, -1, 1, -1,
    -1, 1, -1, 1, -1, 1, -1, 1,
    1, -1, 1, -1, 1, -1, 1, -1,
    1, -1, 1, -1, 1, -1, 1, -1,
    -1, 1, -1, 1, -1, 1, -1, 1]

/-- The signed 64-coordinate spin vector reached by the first actual Norton action. -/
def monsterNortonLine01InitialSpin : NortonUIntegerVector :=
  ∑ a : Fin 64, monsterNortonLine01InitialSpinSigns a •
    (Pi.single (monsterNortonLine01InitialSpinIndices a) 1 : NortonUIntegerVector)

/-- Genuine integral Leech coordinates of the same reached rank-one tensor. -/
def monsterNortonLine01InitialLeech : Fin 24 → ℤ :=
  ![-1, 0, 0, 0, 0, -1, 1, 1,
    -1, -1, 1, 1, 1, 1, 0, 0,
    1, 0, 0, -1, -1, 0, -1, 0]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- These 64 checks retain both the twelve-bit output labels and all actual central signs.
/-- Every listed transition agrees with the genuine compact basis action. -/
theorem monsterNortonLine01Initial_transition_certificate (a : Fin 64) :
    nortonUIntegerLabel (monsterNortonUCompactBasisIndex (golayLabelCoefficients 1038)
      (monsterNortonGrayCoefficients a)) = monsterNortonLine01InitialSpinIndices a ∧
    monsterNortonUCompactBasisSign (golayLabelCoefficients 1038)
      (monsterNortonGrayCoefficients a) = monsterNortonLine01InitialSpinSigns a := by
  revert a
  decide +kernel

/-- The entire actual integer spin numerator follows from the proved 64-term basis expansion. -/
theorem monsterNortonLine01InitialSpin_certificate :
    monsterNortonUCompactNumerator (Pi.single 1038 1) = -monsterNortonLine01InitialSpin := by
  rw [monsterNortonUCompactNumerator_basis_fin64, monsterNortonLine01InitialSpin]
  apply congrArg (fun v : NortonUIntegerVector => -v)
  apply Finset.sum_congr rfl
  intro a _
  rw [(monsterNortonLine01Initial_transition_certificate a).1,
    (monsterNortonLine01Initial_transition_certificate a).2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Twenty-four exact integer entries check the original integral basis action.
/-- The full actual Norton Leech matrix gives the stated integral lattice coordinates. -/
theorem monsterNortonLine01InitialLeech_certificate :
    monsterNortonUIntegralAction *ᵥ (Pi.single 0 1) = monsterNortonLine01InitialLeech := by
  rw [monsterNortonUIntegralAction_cache]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
