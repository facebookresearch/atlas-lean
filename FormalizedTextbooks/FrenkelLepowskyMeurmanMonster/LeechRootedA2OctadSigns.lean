/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2RootLine
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivityOctad

/-! Actual root-line-preserving signs normalize a standard neighboring octad. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The positive standard octad neighbor of4(e0+e1). -/
def leechRootedA2PositiveOctad : Fin 24 → ℤ := fun i => if i.val < 8 then 2 else 0

/-- Equal root signs can be normalized through genuine Golay signs preserving the root line. -/
theorem leechRootedA2_standard_octad_signs (u : leechIntegral)
    (hfirst : ∀ j : Fin 8, u.val (Fin.castAdd 16 j) = -2 ∨
      u.val (Fin.castAdd 16 j) = 2)
    (hzero : ∀ i : Fin 24, 8 ≤ i.val → u.val i = 0)
    (hroot : u.val 0 = u.val 1) :
    ∃ d : golayCode, leechRootedA2PreservesRootLine (golaySignIsometry d) ∧
      (leechIntegralAction (golaySignIsometry d) u).val = leechRootedA2PositiveOctad := by
  classical
  let bits : Fin 8 → ZMod 2 := fun j => if u.val (Fin.castAdd 16 j) = -2 then 1 else 0
  have hb : ∑ j, bits j = 0 := leechShort_standard_octad_even u hfirst hzero
  obtain ⟨d, hd⟩ := golayStandardOctad_even_signs bits hb
  have he : d.val 0 = d.val 1 := by
    have hd0 := hd 0
    have hd1 := hd 1
    change d.val 0 = (if u.val 0 = -2 then 1 else 0) at hd0
    change d.val 1 = (if u.val 1 = -2 then 1 else 0) at hd1
    rw [hd0, hd1, hroot]
  refine ⟨d, leechRootedA2Root_sign d he, ?_⟩
  have hrow (j : Fin 8) :
      (if d.val (Fin.castAdd 16 j) = 0 then u.val (Fin.castAdd 16 j)
        else -u.val (Fin.castAdd 16 j)) = 2 := by
    rw [hd j]
    rcases hfirst j with h | h <;> simp [bits, h]
  rw [leechIntegralAction_golaySign]
  funext i
  by_cases hi : i.val < 8
  · let j : Fin 8 := ⟨i.val, hi⟩
    have hj : Fin.castAdd 16 j = i := Fin.ext rfl
    simpa only [hj, golayIntegerSign, leechRootedA2PositiveOctad, hi, ite_true] using hrow j
  · simp [golayIntegerSign, hzero i (by omega), leechRootedA2PositiveOctad, hi]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
