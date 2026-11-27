/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.PairSetMappingIndependenceErdosProblem1025

/-!
# Small cases of independence for pair set mappings

At two vertices the guarantee is unbounded. At three vertices its maximum is two.
-/

namespace MathlibExt.Combinatorics.PairSetMappingIndependenceErdosProblem1025Wanted

-- No output can avoid both endpoints, so every size satisfies the universal guarantee.
example : setMappingIndependence 2 = 0 := by
  unfold setMappingIndependence
  have h (f : Sym2 (Fin 2) → Fin 2) : ¬ (f s(0, 1) ≠ 0 ∧ f s(0, 1) ≠ 1) := by
    omega
  have hall : {k : ℕ | ∀ f : Sym2 (Fin 2) → Fin 2,
      (∀ x y, x ≠ y → f s(x, y) ≠ x ∧ f s(x, y) ≠ y) →
        ∃ X : Finset (Fin 2), IsIndependentFor f X ∧ k ≤ X.card} = Set.univ := by
    exact Set.eq_univ_of_forall fun _ f hf ↦ (h f (hf 0 1 (by decide))).elim
  rw [hall, csSup_of_not_bddAbove (not_bddAbove_univ : ¬BddAbove (Set.univ : Set ℕ))]
  exact csSup_empty

-- Addition modulo three supplies the third point of each distinct pair.
private def thirdPoint : Sym2 (Fin 3) → Fin 3 :=
  Sym2.lift ⟨fun x y ↦ -(x + y), fun x y ↦ congrArg Neg.neg (add_comm x y)⟩

example : setMappingIndependence 3 = 2 := by
  have hadm : ∀ x y, x ≠ y → thirdPoint s(x, y) ≠ x ∧ thirdPoint s(x, y) ≠ y := by decide
  have hcard : ∀ X, IsIndependentFor thirdPoint X → X.card ≤ 2 := by
    unfold IsIndependentFor
    decide
  have hub : ∀ k ∈ {k : ℕ | ∀ f : Sym2 (Fin 3) → Fin 3,
      (∀ x y, x ≠ y → f s(x, y) ≠ x ∧ f s(x, y) ≠ y) →
        ∃ X : Finset (Fin 3), IsIndependentFor f X ∧ k ≤ X.card}, k ≤ 2 := by
    intro k hk
    obtain ⟨X, hX, hkX⟩ := hk thirdPoint hadm
    exact hkX.trans (hcard X hX)
  refine le_antisymm (csSup_le' hub) (le_csSup ⟨2, hub⟩ ?_)
  intro f hf
  refine ⟨{0, 1}, ?_, by decide⟩
  intro x hx y hy hxy
  have := hf x y hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at *
  grind

end MathlibExt.Combinatorics.PairSetMappingIndependenceErdosProblem1025Wanted
