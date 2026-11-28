/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.BackboneExists

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.BackboneExists`

On the triangle `Fin 3` with edge set `E = {s(0, 1), s(0, 2)}` and the all-ones current:
* the sites `1` and `2` are joined to `0` through odd edges (the hypotheses are satisfiable);
* `bbe_backbone_exists` then produces a set of odd edges with boundary `{1, 2}`;
* `bbe_backbone_exists_toggle` applies to the same data on the graph `⊤`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.BackboneExists

open _root_.StatMech _root_.StatMech.Ising

/-- The two-edge star centred at `0` in `Fin 3`. -/
def E3 : Finset (Sym2 (Fin 3)) := {s(0, 1), s(0, 2)}

/-- The all-ones current. -/
def m1 : Current (Fin 3) := fun _ => 1

/-- `0` is joined to `1` through odd edges of `m1`. -/
theorem conn01 : connP (oddEdges E3 m1) 0 1 :=
  Relation.ReflTransGen.single ⟨s(0, 1), by simp [oddEdges, E3, m1], by simp, by simp, by decide⟩

/-- `0` is joined to `2` through odd edges of `m1`. -/
theorem conn02 : connP (oddEdges E3 m1) 0 2 :=
  Relation.ReflTransGen.single ⟨s(0, 2), by simp [oddEdges, E3, m1], by simp, by simp, by decide⟩

-- A backbone between `1` and `2` exists inside the odd edges.
example : ∃ P ⊆ oddEdges E3 m1, srcP P = {1, 2} ∧ ∀ e ∈ P, Odd (m1 e) :=
  bbe_backbone_exists E3 m1 (by decide) (by decide) (by decide) conn01 conn02

-- The toggle form on the complete graph: the backbone also shifts sources by `{1, 2}`.
example : ∃ P ⊆ oddEdges (⊤ : SimpleGraph (Fin 3)).edgeFinset m1, srcP P = {1, 2} := by
  obtain ⟨P, hP, hsrc, -⟩ := bbe_backbone_exists_toggle (⊤ : SimpleGraph (Fin 3)) 1 (fun _ => 1)
    m1 (o := 0) (x := 1) (y := 2) (by decide) (by decide) (by decide)
    (Relation.ReflTransGen.single ⟨s(0, 1), by simp [oddEdges, m1], by simp, by simp, by decide⟩)
    (Relation.ReflTransGen.single ⟨s(0, 2), by simp [oddEdges, m1], by simp, by simp, by decide⟩)
  exact ⟨P, hP, hsrc⟩

-- The odd edges of `m1` in `E3` are all of `E3`.
example : oddEdges E3 m1 = E3 := by
  simp [oddEdges, m1]

end PhyslibExtTest.CondensedMatter.IsingModel.BackboneExists
