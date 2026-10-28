/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQSelectedPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks

/-! Exact XOR arithmetic evaluates selected full phases with nonzero central coefficients. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A scalar XOR value is read as its exact characteristic-two parity. -/
def generatedSixthXiMaskParity (n : ℕ) : ZMod 2 := if n.testBit 0 then 1 else 0

/-- Ordinary integer XOR is addition of scalar characteristic-two phases. -/
theorem generatedSixth_xi_mask_parity_xor (a b : ℕ) :
    generatedSixthXiMaskParity (Nat.xor a b) =
      generatedSixthXiMaskParity a + generatedSixthXiMaskParity b :=
  congrFun (monsterCo1GeometryBinaryMaskDecode_xor (n := 1) a b) 0

/-- Full phase of selected factors, keeping their central bits and all ordered cocycle pairs. -/
def generatedSixthXiSelectedMaskPhase (c : ℕ) (p : Fin 24 → ℕ) (n : ℕ) :
    List (Fin 24) → ℕ
  | [] => 0
  | i :: l => Nat.xor (generatedSixthXiSelectedMaskPhase c p n l)
      (if n.testBit i.val then Nat.xor (if c.testBit i.val then 1 else 0)
        (monsterCo1GeometryBinaryMaskSum (l.map (fun j =>
          if n.testBit j.val then if (p i).testBit j.val then 1 else 0 else 0))) else 0)

/-- The complete XOR evaluator equals the genuine selected scalar phase for every input mask. -/
theorem generatedSixth_xi_selected_mask_phase (c : ℕ) (p : Fin 24 → ℕ)
    (n : ℕ) (l : List (Fin 24)) :
    generatedSixthXiMaskParity (generatedSixthXiSelectedMaskPhase c p n l) =
      generatedSixthQSelectedPhase
        (fun i => if c.testBit i.val then 1 else 0)
        (fun i j => if (p i).testBit j.val then 1 else 0)
        (monsterCo1GeometryBinaryMaskDecode n) l := by
  induction l with
  | nil => simp [generatedSixthXiSelectedMaskPhase, generatedSixthQSelectedPhase,
      generatedSixthXiMaskParity]
  | cons i l ih =>
    by_cases hi : n.testBit i.val = true
    · have hs : generatedSixthXiMaskParity (monsterCo1GeometryBinaryMaskSum
          (l.map (fun j => if n.testBit j.val then
            if (p i).testBit j.val then 1 else 0 else 0))) =
          (l.map (fun j => if monsterCo1GeometryBinaryMaskDecode n j = 0 then 0
            else if (p i).testBit j.val then 1 else 0)).sum := by
        rw [generatedSixthXiMaskParity, monsterCo1GeometryBinaryMaskSum_parity, List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro j _
        cases hj : n.testBit j.val <;> cases hp : (p i).testBit j.val <;>
          simp [monsterCo1GeometryBinaryMaskDecode, hj, hp]
      have hc : generatedSixthXiMaskParity (if c.testBit i.val then 1 else 0) =
          if c.testBit i.val then (1 : ZMod 2) else 0 := by
        cases h : c.testBit i.val <;> rfl
      simp only [generatedSixthXiSelectedMaskPhase, hi, ite_true,
        generatedSixth_xi_mask_parity_xor, ih, hc, hs, generatedSixthQSelectedPhase]
      simp only [monsterCo1GeometryBinaryMaskDecode, hi, ite_true, one_ne_zero, ite_false]
    · have hf : n.testBit i.val = false := Bool.eq_false_iff.mpr hi
      simp only [generatedSixthXiSelectedMaskPhase, hf, Bool.false_eq_true, ite_false]
      simp only [generatedSixthQSelectedPhase, monsterCo1GeometryBinaryMaskDecode, hf,
        Bool.false_eq_true, ite_true, ite_false, add_zero]
      rw [generatedSixth_xi_mask_parity_xor, ih]
      simp [generatedSixthXiMaskParity]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
