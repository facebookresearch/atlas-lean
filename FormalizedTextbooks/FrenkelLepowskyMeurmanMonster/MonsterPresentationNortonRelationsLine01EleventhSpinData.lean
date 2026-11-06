/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Proposed finite spin factor for the exact eleventh tensor coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhTensorInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SourceCoordinateSupport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The thirty-two proposed original spin labels. -/
def monsterNortonLine01EleventhSpinLabel : Fin 32 → Fin 4096 :=
  ![257, 271, 339, 349, 437, 443, 487, 489,
    1024, 1038, 1106, 1116, 1204, 1210, 1254, 1256,
    2049, 2063, 2131, 2141, 2229, 2235, 2279, 2281,
    3328, 3342, 3410, 3420, 3508, 3514, 3558, 3560]

/-- The proposed integer signs on those labels. -/
def monsterNortonLine01EleventhSpinCoefficient : Fin 32 → ℤ :=
  ![1, 1, 1, 1, 1, 1, 1, 1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    1, 1, 1, 1, 1, 1, 1, 1]

/-- A direct inverse of the displayed spin labels. -/
def monsterNortonLine01EleventhSpinLookup (n : Fin 4096) : Fin 32 :=
  if n.val < 2049 then
    if n.val < 1024 then
      if n.val < 437 then
        if n.val < 339 then
          if n.val < 271 then
            if n.val = 257 then 0 else 0
          else
            if n.val = 271 then 1 else 0
        else
          if n.val < 349 then
            if n.val = 339 then 2 else 0
          else
            if n.val = 349 then 3 else 0
      else
        if n.val < 487 then
          if n.val < 443 then
            if n.val = 437 then 4 else 0
          else
            if n.val = 443 then 5 else 0
        else
          if n.val < 489 then
            if n.val = 487 then 6 else 0
          else
            if n.val = 489 then 7 else 0
    else
      if n.val < 1204 then
        if n.val < 1106 then
          if n.val < 1038 then
            if n.val = 1024 then 8 else 0
          else
            if n.val = 1038 then 9 else 0
        else
          if n.val < 1116 then
            if n.val = 1106 then 10 else 0
          else
            if n.val = 1116 then 11 else 0
      else
        if n.val < 1254 then
          if n.val < 1210 then
            if n.val = 1204 then 12 else 0
          else
            if n.val = 1210 then 13 else 0
        else
          if n.val < 1256 then
            if n.val = 1254 then 14 else 0
          else
            if n.val = 1256 then 15 else 0
  else
    if n.val < 3328 then
      if n.val < 2229 then
        if n.val < 2131 then
          if n.val < 2063 then
            if n.val = 2049 then 16 else 0
          else
            if n.val = 2063 then 17 else 0
        else
          if n.val < 2141 then
            if n.val = 2131 then 18 else 0
          else
            if n.val = 2141 then 19 else 0
      else
        if n.val < 2279 then
          if n.val < 2235 then
            if n.val = 2229 then 20 else 0
          else
            if n.val = 2235 then 21 else 0
        else
          if n.val < 2281 then
            if n.val = 2279 then 22 else 0
          else
            if n.val = 2281 then 23 else 0
    else
      if n.val < 3508 then
        if n.val < 3410 then
          if n.val < 3342 then
            if n.val = 3328 then 24 else 0
          else
            if n.val = 3342 then 25 else 0
        else
          if n.val < 3420 then
            if n.val = 3410 then 26 else 0
          else
            if n.val = 3420 then 27 else 0
      else
        if n.val < 3558 then
          if n.val < 3514 then
            if n.val = 3508 then 28 else 0
          else
            if n.val = 3514 then 29 else 0
        else
          if n.val < 3560 then
            if n.val = 3558 then 30 else 0
          else
            if n.val = 3560 then 31 else 0

/-- Membership in the proposed finite spin support. -/
def monsterNortonLine01EleventhSpinSupport (n : Fin 4096) : Prop :=
  monsterNortonLine01EleventhSpinLabel (monsterNortonLine01EleventhSpinLookup n) = n

instance (n : Fin 4096) : Decidable (monsterNortonLine01EleventhSpinSupport n) :=
  inferInstanceAs (Decidable (_ = _))

/-- The entire proposed spin factor, including all zero coordinates. -/
def monsterNortonLine01EleventhSpinVector : NortonUIntegerVector :=
  fun n => if monsterNortonLine01EleventhSpinSupport n then
    monsterNortonLine01EleventhSpinCoefficient (monsterNortonLine01EleventhSpinLookup n) else 0

/-- Every displayed spin label belongs to the already proved actual source-code catalogue. -/
theorem monsterNortonLine01EleventhSpinLabel_source (p : Fin 32) :
    monsterNortonLine01SourceCodeSupport
      ⟨(monsterNortonLine01EleventhSpinLabel p).val % 2048, by omega⟩ := by
  revert p
  decide +kernel

/-- The proposed spin factor vanishes outside the exact actual source-code support. -/
theorem monsterNortonLine01EleventhSpinVector_source_zero (n : Fin 4096)
    (hn : ¬ monsterNortonLine01SourceCodeSupport ⟨n.val % 2048, by omega⟩) :
    monsterNortonLine01EleventhSpinVector n = 0 := by
  have hs : ¬ monsterNortonLine01EleventhSpinSupport n := by
    intro hs
    have h := monsterNortonLine01EleventhSpinLabel_source (monsterNortonLine01EleventhSpinLookup n)
    change monsterNortonLine01EleventhSpinLabel (monsterNortonLine01EleventhSpinLookup n) = n at hs
    have he := congrArg (fun m : Fin 4096 =>
      (⟨m.val % 2048, Nat.mod_lt _ (by norm_num)⟩ : Fin 2048)) hs
    exact hn (he ▸ h)
  exact ite_eq_right hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
