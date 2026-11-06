/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskColumns

/-! A list evaluator for column-XOR masks, with its genuine matrix meaning
proved propositionally before finite certificate specialization. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Evaluate explicitly indexed integer columns without repeated finite-function lookup. -/
def generatedAxisGlobalMaskRowsAction : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (i, c) :: rows, b =>
      if b.testBit i then Nat.xor c (generatedAxisGlobalMaskRowsAction rows b)
      else generatedAxisGlobalMaskRowsAction rows b

private theorem maskRowsAction_sum (rows : List (ℕ × ℕ)) (b : ℕ) :
    generatedAxisGlobalMaskRowsAction rows b =
      monsterCo1GeometryBinaryMaskSum
        (rows.map (fun p => if b.testBit p.1 then p.2 else 0)) := by
  induction rows with
  | nil => rfl
  | cons p rows ih =>
      rcases p with ⟨i, c⟩
      cases h : b.testBit i <;>
        simp [generatedAxisGlobalMaskRowsAction, h, monsterCo1GeometryBinaryMaskSum, ih]

/-- The direct list evaluator is exactly the previously proved column-matrix evaluator. -/
theorem generatedAxisGlobalMaskRowsAction_ofFn {n : ℕ} (a : Fin n → ℕ) (b : ℕ) :
    generatedAxisGlobalMaskRowsAction (List.ofFn (fun j : Fin n => (j.val, a j))) b =
      generatedAxisGlobalMaskColumnAction a b := by
  rw [maskRowsAction_sum, List.map_ofFn]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
