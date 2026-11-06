/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact cancellation pairing among the actual eighth-state signed-pair outputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthCoefficients

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Swap the two original pair families at equal physical support; retain octad slots. -/
def monsterNortonLine01PairEighthPartner : Fin 240 → Fin 240 :=
  ![
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 163, 17, 18, 160, 167, 21, 22, 164,
    24, 170, 169, 27, 28, 174, 173, 31, 131, 33, 34, 128,
    135, 37, 38, 132, 40, 138, 137, 43, 44, 142, 141, 47,
    147, 49, 50, 144, 151, 53, 54, 148, 56, 154, 153, 59,
    60, 158, 157, 63, 64, 213, 214, 67, 68, 209, 210, 71,
    220, 73, 74, 223, 216, 77, 78, 219, 80, 229, 230, 83,
    84, 225, 226, 87, 236, 89, 90, 239, 232, 93, 94, 235,
    96, 181, 182, 99, 100, 177, 178, 103, 188, 105, 106, 191,
    184, 109, 110, 187, 112, 197, 198, 115, 116, 193, 194, 119,
    204, 121, 122, 207, 200, 125, 126, 203, 35, 129, 130, 32,
    39, 133, 134, 36, 136, 42, 41, 139, 140, 46, 45, 143,
    51, 145, 146, 48, 55, 149, 150, 52, 152, 58, 57, 155,
    156, 62, 61, 159, 19, 161, 162, 16, 23, 165, 166, 20,
    168, 26, 25, 171, 172, 30, 29, 175, 176, 101, 102, 179,
    180, 97, 98, 183, 108, 185, 186, 111, 104, 189, 190, 107,
    192, 117, 118, 195, 196, 113, 114, 199, 124, 201, 202, 127,
    120, 205, 206, 123, 208, 69, 70, 211, 212, 65, 66, 215,
    76, 217, 218, 79, 72, 221, 222, 75, 224, 85, 86, 227,
    228, 81, 82, 231, 92, 233, 234, 95, 88, 237, 238, 91]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check all finite partners and both actual source coefficient signs.
/-- The entire partner table preserves physical pair support and negates its true coefficient. -/
theorem monsterNortonLine01PairEighthPartner_certificate (k : Fin 240) :
    monsterNortonLine01PairEighthPartner (monsterNortonLine01PairEighthPartner k) = k ∧
    monsterNortonLine01PairEighthIsPair (monsterNortonLine01PairEighthPartner k) =
      monsterNortonLine01PairEighthIsPair k ∧
    (monsterNortonLine01PairEighthIsPair k = true →
      monsterNortonLine01PairEighthPairFirst (monsterNortonLine01PairEighthPartner k) =
        monsterNortonLine01PairEighthPairFirst k ∧
      monsterNortonLine01PairEighthPairSecond (monsterNortonLine01PairEighthPartner k) =
        monsterNortonLine01PairEighthPairSecond k ∧
      monsterNortonLine01PairEighthCoefficient (monsterNortonLine01PairEighthPartner k) =
        -monsterNortonLine01PairEighthCoefficient k) := by
  revert k
  decide +kernel

/-- The partner table is a genuine involution of all 240 original source slots. -/
theorem monsterNortonLine01PairEighthPartner_involutive :
    Function.Involutive monsterNortonLine01PairEighthPartner :=
  fun k => (monsterNortonLine01PairEighthPartner_certificate k).1

/-- Original physical pair index of each reached eighth output; unused slots have (0,1). -/
noncomputable def monsterNortonLine01PairEighthPhysicalPair (k : Fin 240) : Fin 276 :=
  griessPairIndex (monsterNortonLine01PairEighthPairFirst k)
    (monsterNortonLine01PairEighthPairSecond k)
    (ne_of_lt (monsterNortonLine01PairEighthPair_increasing k))

/-- Each genuine paired output has precisely the same original physical pair index. -/
theorem monsterNortonLine01PairEighthPartner_physical (k : Fin 240)
    (hk : monsterNortonLine01PairEighthIsPair k = true) :
    monsterNortonLine01PairEighthPhysicalPair (monsterNortonLine01PairEighthPartner k) =
      monsterNortonLine01PairEighthPhysicalPair k := by
  obtain ⟨hf, hs, _⟩ := (monsterNortonLine01PairEighthPartner_certificate k).2.2 hk
  unfold monsterNortonLine01PairEighthPhysicalPair
  simp only [hf, hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
