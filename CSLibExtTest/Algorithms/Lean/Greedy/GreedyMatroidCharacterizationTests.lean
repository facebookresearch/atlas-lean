/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.GreedyMatroidCharacterization
public meta import CSLibExt.Algorithms.Lean.Greedy.GreedyMatroidCharacterization

/-!
# Greedy-characterization tests

On `Fin 3`, the independence system `{∅, {0}, {1}, {2}, {1, 2}}` is not a matroid (`{0}` cannot
be augmented from `{1, 2}`). An executed run shows greedy failing on it with the weights from the
proof of `augment_of_greedyOptimal` (`3, 2, 2`), and a closed example derives
`¬ GreedyOptimal` from the theorem. The uniform matroid of rank two on `Fin 3` is greedy-optimal
by `greedyOptimal_iff_exists_matroid`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

/-- Independent sets `∅, {0}, {1}, {2}, {1, 2}` on `Fin 3`. -/
private def bad (S : Finset (Fin 3)) : Bool :=
  decide (S ∈ ({∅, {0}, {1}, {2}, {1, 2}} : Finset (Finset (Fin 3))))

private theorem bad_sys : IsIndepSystem bad where
  empty := by decide
  subset := by decide

-- Weights 3, 2, 2 (the proof's |I| + 2 and |I| + 1 with I = {0}): greedy keeps {0}, weight 3,
-- while {1, 2} weighs 4.
#eval
  let w : Fin 3 → ℕ := fun i => if i = 0 then 3 else 2
  let g := (matroidGreedy bad [0, 1, 2]).ret
  ((List.finRange 3).filter (· ∈ g), ∑ x ∈ g, w x, ∑ x ∈ ({1, 2} : Finset (Fin 3)), w x)

example : (matroidGreedy bad [0, 1, 2]).ret = {0} := by decide

/-- The system is not greedy-optimal, by the augmentation theorem. -/
example : ¬ GreedyOptimal bad := fun h => by
  obtain ⟨e, he, heI, hins⟩ := augment_of_greedyOptimal bad_sys h (I := {0}) (J := {1, 2})
    (by decide) (by decide) (by decide)
  have hno : ∀ e ∈ ({1, 2} : Finset (Fin 3)), e ∉ ({0} : Finset (Fin 3)) →
      bad (insert e {0}) = false := by decide
  simp [hno e he heI] at hins

/-- The uniform matroid of rank two on `Fin 3`. -/
private def uniform23 : Matroid (Fin 3) :=
  (IndepMatroid.ofFinset Set.univ (fun I : Finset (Fin 3) => I.card ≤ 2) (by simp)
    (fun _ _ hJ hIJ => (Finset.card_le_card hIJ).trans hJ)
    (fun I J hI hJ hlt => by
      obtain ⟨e, heJ, heI⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      exact ⟨e, heJ, heI, by rw [Finset.card_insert_of_notMem heI]; omega⟩)
    (fun _ _ => Set.subset_univ _)).matroid

private def atMostTwo (S : Finset (Fin 3)) : Bool := decide (S.card ≤ 2)

example : GreedyOptimal atMostTwo :=
  (greedyOptimal_iff_exists_matroid ⟨by decide, by decide⟩).2 ⟨uniform23, rfl, fun S => by
    simp only [uniform23, IndepMatroid.matroid_Indep, atMostTwo, decide_eq_true_eq]
    exact IndepMatroid.ofFinset_indep (α := Fin 3) Set.univ (fun I : Finset (Fin 3) => I.card ≤ 2)
      _ _ _ _ (I := S)⟩

#print axioms augment_of_greedyOptimal
#print axioms exists_matroid_of_greedyOptimal
#print axioms greedyOptimal_iff_exists_matroid

end Cslib.Algorithms.Lean.TimeM
