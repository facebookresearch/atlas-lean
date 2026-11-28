/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.NeuralNetworks.GraphMessagePassing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Regressions for graph message passing and 1-WL -/

set_option autoImplicit false

namespace CSLibExtTest.MachineLearning.NeuralNetworks.GraphMessagePassing

open CSLibExt.MachineLearning.NeuralNetworks.GraphMessagePassing

private def fork : SimpleGraph (Fin 3) where
  Adj v w := (v = 0 ∧ w ≠ 0) ∨ (w = 0 ∧ v ≠ 0)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (fun h => h.2 h.1) (fun h => h.2 h.1)⟩

private instance : DecidableRel fork.Adj := fun v w => by
  change Decidable ((v = 0 ∧ w ≠ 0) ∨ (w = 0 ∧ v ≠ 0))
  infer_instance

private theorem fork_neighbors_zero : fork.neighborFinset 0 = {1, 2} := by
  rw [SimpleGraph.neighborFinset_eq_filter]
  decide

private theorem fork_neighbors_one : fork.neighborFinset 1 = {0} := by
  rw [SimpleGraph.neighborFinset_eq_filter]
  decide

private theorem fork_neighbors_two : fork.neighborFinset 2 = {0} := by
  rw [SimpleGraph.neighborFinset_eq_filter]
  decide

-- Both neighbors of the center carry the same feature. Neither entry is discarded.
example : neighborFeatures fork (fun _ => 7 : Fin 3 → ℕ) 0 = ([7, 7] : Multiset ℕ) := by
  rw [neighborFeatures, fork_neighbors_zero]
  decide

private def sumLayer : Layer ℕ ℕ where
  Message := ℕ
  aggregate := Multiset.sum
  combine := (· + ·)

private def layers (_ : ℕ) : Layer ℕ ℕ := sumLayer

-- After one layer the center is 3 and both leaves are 2. The second layer uses those
-- previous-round features simultaneously; its center is 7 and its leaves are 5.
example : nodeFeatures (F := fun _ => ℕ) fork layers (fun _ => 1) 2 0 = 7 ∧
    nodeFeatures (F := fun _ => ℕ) fork layers (fun _ => 1) 2 1 = 5 := by
  simp only [nodeFeatures, layers, Layer.step, sumLayer, neighborFeatures,
    fork_neighbors_zero, fork_neighbors_one]
  decide

example : graphEmbedding (F := fun _ => ℕ) fork layers (fun _ => 1) 2 Multiset.sum = 17 := by
  unfold graphEmbedding
  have h (v : Fin 3) : nodeFeatures (F := fun _ => ℕ) fork layers (fun _ => 1) 2 v =
      if v = 0 then 7 else 5 := by
    fin_cases v <;> decide
  simp_rw [h]
  decide

private def edge : SimpleGraph (Fin 2) := ⊤
private def empty : SimpleGraph (Fin 2) := ⊥

private instance : DecidableRel edge.Adj := fun v w => decidable_of_iff (v ≠ w) (by rfl)
private instance : DecidableRel empty.Adj := fun v w => decidable_of_iff False (by rfl)

-- Round 0 is just the common initial multiset. At round 1, an edge endpoint has one
-- neighbor of the initial color, whereas both isolated vertices have none.
example : ¬ wlDistinguishesAt edge empty (fun _ => 0 : Fin 2 → ℕ) (fun _ => 0) 0 := by
  intro h
  exact h rfl

example : wlDistinguishesAt edge empty (fun _ => 0 : Fin 2 → ℕ) (fun _ => 0) 1 := by
  have he₀ : edge.neighborFinset 0 = {1} := by rw [SimpleGraph.neighborFinset_eq_filter]; decide
  have he₁ : edge.neighborFinset 1 = {0} := by rw [SimpleGraph.neighborFinset_eq_filter]; decide
  have hb (v : Fin 2) : empty.neighborFinset v = ∅ := SimpleGraph.neighborFinset_bot v
  have hE (v : Fin 2) : wlColor edge (fun _ => (0 : ℕ)) 1 v =
      ((0 : ℕ), ([0] : Multiset ℕ)) := by
    fin_cases v <;> simp [wlColor, nodeFeatures, Layer.step, neighborFeatures, he₀, he₁] <;> rfl
  have hB (v : Fin 2) : wlColor empty (fun _ => (0 : ℕ)) 1 v =
      ((0 : ℕ), (0 : Multiset ℕ)) := by
    simp [wlColor, nodeFeatures, Layer.step, neighborFeatures, hb]
    rfl
  have hne :
      (Finset.univ : Finset (Fin 2)).val.map (fun _ => ((0 : ℕ), ([0] : Multiset ℕ))) ≠
        (Finset.univ : Finset (Fin 2)).val.map (fun _ => ((0 : ℕ), (0 : Multiset ℕ))) := by
    decide
  simp only [wlDistinguishesAt, wlColors, hE, hB]
  exact hne

end CSLibExtTest.MachineLearning.NeuralNetworks.GraphMessagePassing
