/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Graph.CycleContinuousAntichain

namespace MathlibExt.GraphTheory.CycleContinuousAntichainWanted.Test

private def loop : FGraph := ⟨Unit, Unit, fun _ => ((), ())⟩

private def parallel (n : ℕ) : FGraph := ⟨Bool, Fin n, fun _ => (false, true)⟩

private theorem parallel_univ_iff (n : ℕ) :
    (Set.univ : Set (parallel n).E) ∈ cycleSpace (parallel n) ↔ Even n := by
  change (Set.Finite (Set.univ : Set (Fin n)) ∧ ∀ v : Bool,
    Even (Set.ncard {e : Fin n | e ∈ Set.univ ∧
      ((false = v ∧ true ≠ v) ∨ (false ≠ v ∧ true = v))})) ↔ Even n
  have allEdges (v : Bool) :
      {e : Fin n | e ∈ Set.univ ∧
        ((false = v ∧ true ≠ v) ∨ (false ≠ v ∧ true = v))} = Set.univ := by
    cases v <;> ext e <;> simp
  simp only [allEdges, Set.toFinite, true_and, Set.ncard_univ, Nat.card_fin]
  exact ⟨fun h => h false, fun h _ => h⟩

private theorem loop_cycle : (Set.univ : Set loop.E) ∈ cycleSpace loop := by
  change Set.Finite (Set.univ : Set Unit) ∧ ∀ v : Unit,
    Even (Set.ncard {e : Unit | e ∈ Set.univ ∧
      (((() : Unit) = v ∧ () ≠ v) ∨ (() ≠ v ∧ () = v))})
  refine ⟨Set.toFinite _, fun v => ?_⟩
  cases v
  simp

example : (Set.univ : Set (parallel 2).E) ∈ cycleSpace (parallel 2) :=
  (parallel_univ_iff 2).mpr ⟨1, rfl⟩

example : ¬IsCycleContinuous (parallel 1) loop (fun _ => ()) := by
  intro h
  have hp := h Set.univ loop_cycle
  change (Set.univ : Set (parallel 1).E) ∈ cycleSpace (parallel 1) at hp
  exact (by decide : ¬Even 1) ((parallel_univ_iff 1).mp hp)

example :
    ∃ G : ℕ → FGraph, (∀ n, IsFiniteNontrivial (G n)) ∧ Function.Injective G ∧
      ∀ i j, i ≠ j → ¬∃ f : (G i).E → (G j).E, IsCycleContinuous (G i) (G j) f :=
  conjecture_holds

end MathlibExt.GraphTheory.CycleContinuousAntichainWanted.Test
