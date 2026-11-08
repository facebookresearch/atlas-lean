/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rook graphs

The rook graph on an `n × m` board has the cells as vertices, with
distinct cells adjacent when they share a row or a column.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Domination

@[expose] public section

namespace SimpleGraph

/-- The rook graph on `Fin n × Fin m`: distinct cells are adjacent
when they share a row or a column. -/
def rookGraph (n m : ℕ) : SimpleGraph (Fin n × Fin m) where
  Adj x y := x ≠ y ∧ (x.1 = y.1 ∨ x.2 = y.2)
  symm := ⟨by
    rintro x y ⟨hxy, h | h⟩
    · exact ⟨hxy.symm, Or.inl h.symm⟩
    · exact ⟨hxy.symm, Or.inr h.symm⟩⟩
  loopless := ⟨by
    intro x hx
    exact hx.1 rfl⟩

@[simp]
theorem rookGraph_adj {n m : ℕ} {x y : Fin n × Fin m} :
    (rookGraph n m).Adj x y ↔ x ≠ y ∧ (x.1 = y.1 ∨ x.2 = y.2) :=
  Iff.rfl

/-- A finset of cells dominates the rook graph exactly when every
cell shares its row or its column with a cell of the finset. -/
theorem rookGraph_isDominating_iff {n m : ℕ}
    {s : Finset (Fin n × Fin m)} :
    (rookGraph n m).IsDominating ↑s ↔
      ∀ i : Fin n, ∀ j : Fin m,
        (∃ j' : Fin m, (i, j') ∈ s) ∨ ∃ i' : Fin n, (i', j) ∈ s := by
  constructor
  · intro h i j
    rcases h (i, j) with hmem | ⟨u, hu, hadj⟩
    · exact Or.inl ⟨j, Finset.mem_coe.mp hmem⟩
    · rcases hadj.2 with hrow | hcol
      · refine Or.inl ⟨u.2, ?_⟩
        have hu' : u ∈ s := Finset.mem_coe.mp hu
        have : (i, u.2) = u := Prod.ext hrow.symm rfl
        rwa [this]
      · refine Or.inr ⟨u.1, ?_⟩
        have hu' : u ∈ s := Finset.mem_coe.mp hu
        have : (u.1, j) = u := Prod.ext rfl hcol.symm
        rwa [this]
  · intro h v
    obtain ⟨i, j⟩ := v
    rcases h i j with ⟨j', hj'⟩ | ⟨i', hi'⟩
    · by_cases hEq : j' = j
      · subst hEq
        exact Or.inl (Finset.mem_coe.mpr hj')
      · exact Or.inr ⟨(i, j'), Finset.mem_coe.mpr hj',
          ⟨by simp [hEq], Or.inl rfl⟩⟩
    · by_cases hEq : i' = i
      · subst hEq
        exact Or.inl (Finset.mem_coe.mpr hi')
      · exact Or.inr ⟨(i', j), Finset.mem_coe.mpr hi',
          ⟨by simp [hEq], Or.inr rfl⟩⟩

instance rookGraph_decidableIsDominating {n m : ℕ}
    (s : Finset (Fin n × Fin m)) :
    Decidable ((rookGraph n m).IsDominating ↑s) :=
  decidable_of_iff' _ rookGraph_isDominating_iff

end SimpleGraph
