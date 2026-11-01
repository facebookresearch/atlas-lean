/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact boundary bindings for the original-source longest-word square and commutator proofs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431E7Words

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel compares all thirty-eight pairs of literal words of length at most126.
/-- Every square row has exactly its declared adjacent original-source boundary words. -/
theorem y431E7Square_boundaries (i : Fin 38) :
    (y431E7ProofData ⟨i.val, by omega⟩).1.left = y431E7SquareSignedWord i.castSucc ∧
      (y431E7ProofData ⟨i.val, by omega⟩).1.right = y431E7SquareSignedWord i.succ := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- The kernel checks all147 pairs of literal commutator boundary words.
/-- Every commutator row has exactly its declared adjacent original-source boundary words. -/
theorem y431E7Central_boundaries (g : Fin 7) (i : Fin 21) :
    (y431E7ProofData ⟨38 + 21 * g.val + i.val, by omega⟩).1.left =
      y431E7CentralSignedWord g i.castSucc ∧
    (y431E7ProofData ⟨38 + 21 * g.val + i.val, by omega⟩).1.right =
      y431E7CentralSignedWord g i.succ := by
  fin_cases g <;> fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
/-- The literal square start is exactly two copies of the original positive longest word. -/
theorem y431E7Square_start : y431E7SquareSignedWord 0 =
    (y431E7Positive21 ++ y431E7Positive21).map (fun i => (i, true)) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The last literal square boundary word is empty. -/
theorem y431E7Square_end : y431E7SquareSignedWord (Fin.last 38) = [] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- These seven comparisons bind full128-letter original-source commutators.
/-- The commutator starts are exactly the specified generator/longest-word commutators. -/
theorem y431E7Central_start (g : Fin 7) : y431E7CentralSignedWord g 0 =
    ([y431E7Vertex g] ++ y431E7Positive21 ++ [y431E7Vertex g] ++
      y431E7Positive21.reverse).map (fun i => (i, true)) := by
  fin_cases g <;> decide +kernel

set_option maxRecDepth 100000 in
/-- All seven final literal commutator boundary words are empty. -/
theorem y431E7Central_end (g : Fin 7) :
    y431E7CentralSignedWord g (Fin.last 21) = [] := by fin_cases g <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
