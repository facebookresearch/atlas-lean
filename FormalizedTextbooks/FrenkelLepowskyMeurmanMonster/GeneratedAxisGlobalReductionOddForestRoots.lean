/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddShortRoots
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddRoots
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskFinite

/-! Among the sixteen singular forest roots, exactly the nine genuine
norm-eight roots can occur in the actual Ω orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The singular forest has zero, six short roots, and nine genuine norm-eight roots. -/
def generatedAxisGlobalOddForestRootMask (k : Fin 16) : ℕ :=
  if h : k.val = 0 then 0
  else if h' : k.val < 7 then generatedAxisGlobalOddShortRootMask ⟨k.val - 1, by omega⟩
  else generatedAxisGlobalOddRootMask ⟨k.val - 7, by omega⟩

set_option maxHeartbeats 1000000 in
-- Check the exact bounded root list in the actual coordinate-mask encoding.
/-- Every singular forest root is a bounded genuine 24-coordinate mask. -/
theorem generatedAxisGlobalOddForestRootMask_lt (k : Fin 16) :
    generatedAxisGlobalOddForestRootMask k < 2 ^ 24 := by
  revert k
  decide +kernel

/-- Exactly the final nine forest roots belong to the actual Ω orbit. -/
theorem generatedAxisGlobalOddForestRoot_mem_iff (k : Fin 16) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalOddForestRootMask k) ∈
      generatedAxisGlobalBinaryOrbit ↔ 7 ≤ k.val := by
  by_cases h : k.val = 0
  · simp only [generatedAxisGlobalOddForestRootMask, h, ↓reduceDIte]
    have hn : (0 : Fin 24 → ZMod 2) ∉ generatedAxisGlobalBinaryOrbit := by
      intro hz
      exact generatedAxisGlobalBinary_ne_zero ⟨0, hz⟩ rfl
    simpa only [monsterCo1GeometryBinaryMaskDecode_zero, h, Nat.le_zero_eq,
      show (7 : ℕ) ≠ 0 by decide, iff_false] using hn
  · by_cases h' : k.val < 7
    · simp only [generatedAxisGlobalOddForestRootMask, h, h', ↓reduceDIte]
      have hn := generatedAxisGlobalOddShortRoot_not_mem_orbit
        (⟨k.val - 1, by omega⟩ : Fin 6)
      change monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalOddShortRootMask ⟨k.val - 1, by omega⟩) ∉
          generatedAxisGlobalBinaryOrbit at hn
      simpa [show ¬7 ≤ k.val by omega] using hn
    · simp only [generatedAxisGlobalOddForestRootMask, h, h', ↓reduceDIte]
      have hm := generatedAxisGlobalOddRoot_mem_orbit
        (⟨k.val - 7, by omega⟩ : Fin 9)
      change monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalOddRootMask ⟨k.val - 7, by omega⟩) ∈
          generatedAxisGlobalBinaryOrbit at hm
      exact iff_of_true hm (by omega)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
