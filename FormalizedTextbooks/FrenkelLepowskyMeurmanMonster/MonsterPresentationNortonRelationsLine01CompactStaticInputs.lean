/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Fixed-column specializations of the already bound actual integer input lookup. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactColumnData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Column 0 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient0 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)

/-- The specialized column 0 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient0_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 0 p =
      monsterNortonLine01CompactStaticCoefficient0 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 0. -/
def monsterNortonLine01CompactStaticInput0 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient0 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 0 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput0_actual :
    monsterNortonLine01CompactInputVector 0 = monsterNortonLine01CompactStaticInput0 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput0,
    monsterNortonLine01CompactStaticCoefficient0_actual]

/-- Column 1 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient1 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1

/-- The specialized column 1 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient1_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 1 p =
      monsterNortonLine01CompactStaticCoefficient1 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 1. -/
def monsterNortonLine01CompactStaticInput1 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient1 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 1 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput1_actual :
    monsterNortonLine01CompactInputVector 1 = monsterNortonLine01CompactStaticInput1 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput1,
    monsterNortonLine01CompactStaticCoefficient1_actual]

/-- Column 2 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient2 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)

/-- The specialized column 2 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient2_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 2 p =
      monsterNortonLine01CompactStaticCoefficient2 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 2. -/
def monsterNortonLine01CompactStaticInput2 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient2 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 2 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput2_actual :
    monsterNortonLine01CompactInputVector 2 = monsterNortonLine01CompactStaticInput2 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput2,
    monsterNortonLine01CompactStaticCoefficient2_actual]

/-- Column 3 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient3 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1

/-- The specialized column 3 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient3_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 3 p =
      monsterNortonLine01CompactStaticCoefficient3 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 3. -/
def monsterNortonLine01CompactStaticInput3 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient3 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 3 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput3_actual :
    monsterNortonLine01CompactInputVector 3 = monsterNortonLine01CompactStaticInput3 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput3,
    monsterNortonLine01CompactStaticCoefficient3_actual]

/-- Column 4 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient4 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1

/-- The specialized column 4 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient4_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 4 p =
      monsterNortonLine01CompactStaticCoefficient4 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 4. -/
def monsterNortonLine01CompactStaticInput4 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient4 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 4 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput4_actual :
    monsterNortonLine01CompactInputVector 4 = monsterNortonLine01CompactStaticInput4 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput4,
    monsterNortonLine01CompactStaticCoefficient4_actual]

/-- Column 5 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient5 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1

/-- The specialized column 5 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient5_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 5 p =
      monsterNortonLine01CompactStaticCoefficient5 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 5. -/
def monsterNortonLine01CompactStaticInput5 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient5 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 5 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput5_actual :
    monsterNortonLine01CompactInputVector 5 = monsterNortonLine01CompactStaticInput5 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput5,
    monsterNortonLine01CompactStaticCoefficient5_actual]

/-- Column 6 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient6 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)

/-- The specialized column 6 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient6_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 6 p =
      monsterNortonLine01CompactStaticCoefficient6 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 6. -/
def monsterNortonLine01CompactStaticInput6 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient6 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 6 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput6_actual :
    monsterNortonLine01CompactInputVector 6 = monsterNortonLine01CompactStaticInput6 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput6,
    monsterNortonLine01CompactStaticCoefficient6_actual]

/-- Column 7 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient7 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1

/-- The specialized column 7 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient7_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 7 p =
      monsterNortonLine01CompactStaticCoefficient7 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 7. -/
def monsterNortonLine01CompactStaticInput7 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient7 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 7 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput7_actual :
    monsterNortonLine01CompactInputVector 7 = monsterNortonLine01CompactStaticInput7 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput7,
    monsterNortonLine01CompactStaticCoefficient7_actual]

/-- Column 8 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient8 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1

/-- The specialized column 8 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient8_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 8 p =
      monsterNortonLine01CompactStaticCoefficient8 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 8. -/
def monsterNortonLine01CompactStaticInput8 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient8 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 8 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput8_actual :
    monsterNortonLine01CompactInputVector 8 = monsterNortonLine01CompactStaticInput8 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput8,
    monsterNortonLine01CompactStaticCoefficient8_actual]

/-- Column 9 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient9 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1

/-- The specialized column 9 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient9_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 9 p =
      monsterNortonLine01CompactStaticCoefficient9 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 9. -/
def monsterNortonLine01CompactStaticInput9 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient9 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 9 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput9_actual :
    monsterNortonLine01CompactInputVector 9 = monsterNortonLine01CompactStaticInput9 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput9,
    monsterNortonLine01CompactStaticCoefficient9_actual]

/-- Column 10 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient10 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1

/-- The specialized column 10 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient10_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 10 p =
      monsterNortonLine01CompactStaticCoefficient10 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 10. -/
def monsterNortonLine01CompactStaticInput10 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient10 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 10 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput10_actual :
    monsterNortonLine01CompactInputVector 10 = monsterNortonLine01CompactStaticInput10 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput10,
    monsterNortonLine01CompactStaticCoefficient10_actual]

/-- Column 11 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient11 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)

/-- The specialized column 11 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient11_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 11 p =
      monsterNortonLine01CompactStaticCoefficient11 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 11. -/
def monsterNortonLine01CompactStaticInput11 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient11 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 11 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput11_actual :
    monsterNortonLine01CompactInputVector 11 = monsterNortonLine01CompactStaticInput11 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput11,
    monsterNortonLine01CompactStaticCoefficient11_actual]

/-- Column 12 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient12 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1

/-- The specialized column 12 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient12_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 12 p =
      monsterNortonLine01CompactStaticCoefficient12 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 12. -/
def monsterNortonLine01CompactStaticInput12 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient12 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 12 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput12_actual :
    monsterNortonLine01CompactInputVector 12 = monsterNortonLine01CompactStaticInput12 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput12,
    monsterNortonLine01CompactStaticCoefficient12_actual]

/-- Column 13 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient13 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)

/-- The specialized column 13 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient13_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 13 p =
      monsterNortonLine01CompactStaticCoefficient13 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 13. -/
def monsterNortonLine01CompactStaticInput13 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient13 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 13 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput13_actual :
    monsterNortonLine01CompactInputVector 13 = monsterNortonLine01CompactStaticInput13 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput13,
    monsterNortonLine01CompactStaticCoefficient13_actual]

/-- Column 14 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient14 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1

/-- The specialized column 14 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient14_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 14 p =
      monsterNortonLine01CompactStaticCoefficient14 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 14. -/
def monsterNortonLine01CompactStaticInput14 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient14 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 14 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput14_actual :
    monsterNortonLine01CompactInputVector 14 = monsterNortonLine01CompactStaticInput14 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput14,
    monsterNortonLine01CompactStaticCoefficient14_actual]

/-- Column 15 of the original finite input coefficient table, with its column argument fixed. -/
def monsterNortonLine01CompactStaticCoefficient15 (p : Fin 128) : ℤ :=
  if p.val.testBit 6 then
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
  else
    if p.val.testBit 5 then
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                (-1)
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                1
    else
      if p.val.testBit 4 then
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                1
            else
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
      else
        if p.val.testBit 3 then
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                (-1)
            else
              if p.val.testBit 0 then
                1
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
        else
          if p.val.testBit 2 then
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                (-1)
              else
                (-1)
            else
              if p.val.testBit 0 then
                (-1)
              else
                1
          else
            if p.val.testBit 1 then
              if p.val.testBit 0 then
                1
              else
                1
            else
              if p.val.testBit 0 then
                1
              else
                (-1)

/-- The specialized column 15 agrees with every original input coefficient. -/
theorem monsterNortonLine01CompactStaticCoefficient15_actual (p : Fin 128) :
    monsterNortonLine01CompactInputCoefficient 15 p =
      monsterNortonLine01CompactStaticCoefficient15 p := by
  revert p
  decide +kernel

/-- The entire original input vector in fixed physical column 15. -/
def monsterNortonLine01CompactStaticInput15 : NortonUIntegerVector := fun n =>
  if monsterNortonLine01CompactInputSupport n then
    monsterNortonLine01CompactStaticCoefficient15 (monsterNortonLine01CompactInputLookup n)
  else 0

/-- Specializing column 15 preserves the entire original integer input vector. -/
theorem monsterNortonLine01CompactStaticInput15_actual :
    monsterNortonLine01CompactInputVector 15 = monsterNortonLine01CompactStaticInput15 := by
  funext n
  simp only [monsterNortonLine01CompactInputVector, monsterNortonLine01CompactStaticInput15,
    monsterNortonLine01CompactStaticCoefficient15_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
