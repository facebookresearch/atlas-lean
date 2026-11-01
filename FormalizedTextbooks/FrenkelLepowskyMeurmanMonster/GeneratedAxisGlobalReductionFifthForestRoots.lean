/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthShortRoots
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthRoots
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite

/-! Among the twenty-two singular forest roots, exactly the fourteen genuine
norm-eight roots can occur in the actual Ω orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The singular forest has zero, seven short roots, and fourteen genuine norm-eight roots. -/
def generatedAxisGlobalFifthForestRootMask (k : Fin 22) : ℕ :=
  if h : k.val = 0 then 0
  else if h' : k.val < 8 then generatedAxisGlobalFifthShortRootMask ⟨k.val - 1, by omega⟩
  else generatedAxisGlobalFifthRootMask ⟨k.val - 8, by omega⟩

set_option maxHeartbeats 1000000 in
-- Check the exact bounded root list in the actual coordinate-mask encoding.
/-- Every singular forest root is a bounded genuine 24-coordinate mask. -/
theorem generatedAxisGlobalFifthForestRootMask_lt (k : Fin 22) :
    generatedAxisGlobalFifthForestRootMask k < 2 ^ 24 := by
  revert k
  decide +kernel

/-- Exactly the final fourteen forest roots belong to the actual Ω orbit. -/
theorem generatedAxisGlobalFifthForestRoot_mem_iff (k : Fin 22) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalFifthForestRootMask k) ∈
      generatedAxisGlobalBinaryOrbit ↔ 8 ≤ k.val := by
  by_cases h : k.val = 0
  · simp only [generatedAxisGlobalFifthForestRootMask, h, ↓reduceDIte]
    have hn : (0 : Fin 24 → ZMod 2) ∉ generatedAxisGlobalBinaryOrbit := by
      intro hz
      exact generatedAxisGlobalBinary_ne_zero ⟨0, hz⟩ rfl
    simpa only [monsterCo1GeometryBinaryMaskDecode_zero, h, Nat.le_zero_eq,
      show (8 : ℕ) ≠ 0 by decide, iff_false] using hn
  · by_cases h' : k.val < 8
    · simp only [generatedAxisGlobalFifthForestRootMask, h, h', ↓reduceDIte]
      have hn := generatedAxisGlobalFifthShortRoot_not_mem_orbit
        (⟨k.val - 1, by omega⟩ : Fin 7)
      change monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalFifthShortRootMask ⟨k.val - 1, by omega⟩) ∉
          generatedAxisGlobalBinaryOrbit at hn
      simpa [show ¬8 ≤ k.val by omega] using hn
    · simp only [generatedAxisGlobalFifthForestRootMask, h, h', ↓reduceDIte]
      have hm := generatedAxisGlobalFifthRoot_mem_orbit
        (⟨k.val - 8, by omega⟩ : Fin 14)
      change monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalFifthRootMask ⟨k.val - 8, by omega⟩) ∈
          generatedAxisGlobalBinaryOrbit at hm
      exact iff_of_true hm (by omega)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
