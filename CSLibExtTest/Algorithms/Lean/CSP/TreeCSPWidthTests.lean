/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.CSP.TreeCSPWidth
public import CSLibExtTest.Algorithms.Lean.CSP.TreeCSPTests
public import Mathlib.Data.Fintype.Perm

/-!
# Tests for tree CSPs on forest constraint graphs

Closed checks, by `decide`, reusing the tree-CSP fixtures:

* the path `0 - 1 - 2 - 3` in index order: width one, the derived parent map is the path's, and
  the forest theorem certifies a solution; the acyclic route gives the same;
* the star rooted at a leaf, and a forest with an isolated variable (two roots);
* the triangle with two colors has width two in every ordering, so its constraint graph is not
  a forest; along the index ordering greedy returns an assignment that is no solution (every arc
  is consistent, as the tree-CSP tests check), and no ordering makes every arc a parent edge;
* countermodels: a self-arc (acyclic, width zero, unsolvable, yet the algorithm succeeds), an
  asymmetric relation (for the prescribed index order the child-to-parent arc is never checked;
  with both directions listed and opposite relations, neither rooting detects the conflict), and,
  for `0 → 1 ← 2`, no parent map both covers every listed arc and has every parent edge listed
  parent first;
* both phases charged on the path.
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.Lean.CSP.TreeCSPWidth

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.ArcConsistency
open CSLibExtTest.Algorithms.Lean.CSP.TreeCSP

/-- The index orderings. -/
def ord4 : Fin 4 ≃ Fin (Fintype.card (Fin 4)) := finCongr (Fintype.card_fin 4).symm
def ord3 : Fin 3 ≃ Fin (Fintype.card (Fin 3)) := finCongr (Fintype.card_fin 3).symm
def ord2 : Fin 2 ≃ Fin (Fintype.card (Fin 2)) := finCongr (Fintype.card_fin 2).symm
def ord1 : Fin 1 ≃ Fin (Fintype.card (Fin 1)) := finCongr (Fintype.card_fin 1).symm

/-! ## Forests -/

example : pathCSP.orderWidth ord4 ≤ 1 := by
  decide
example : pathCSP.orderParent ord4 = pathParent := by
  decide
example : List.ofFn ord4.symm = [0, 1, 2, 3] := by
  decide
example : treeSolve pathCSP (pathCSP.orderParent ord4) (List.ofFn ord4.symm) minSel
    (fun _ => Finset.univ) = some ![0, 1, 2, 3] := by
  decide
example : ∃ σ, IsSolution pathCSP (fun _ => Finset.univ) σ := by
  have hdist : ∀ e ∈ pathCSP.arcs, e.1 ≠ e.2 := by decide
  have hw : pathCSP.orderWidth ord4 ≤ 1 := by decide
  have hne : treeSolve pathCSP (pathCSP.orderParent ord4) (List.ofFn ord4.symm) minSel
      (fun _ => Finset.univ) ≠ none := by decide
  exact (BinaryCSP.treeSolve_orderParent_ne_none_iff pathCSP
    (isSelector_minSel 4) pathSym hdist hw (fun _ => Finset.univ)).mp hne

theorem pathCSP_isAcyclic : pathCSP.constraintGraph.IsAcyclic := by
  have heq : pathCSP.constraintGraph = SimpleGraph.hasse (Fin 4) := by
    apply SimpleGraph.ext
    have h : ∀ a b : Fin 4, pathCSP.constraintGraph.Adj a b ↔
        (SimpleGraph.hasse (Fin 4)).Adj a b := by decide
    exact funext fun a => funext fun b => propext (h a b)
  rw [heq]
  exact SimpleGraph.isAcyclic_hasse_of_linearOrder (Fin 4)

example : ∃ (parent : Fin 4 → Option (Fin 4)) (order : List (Fin 4)), RootedOrder parent order ∧
    IsTreeArcs pathCSP parent ∧
    ∀ dom, treeSolve pathCSP parent order minSel dom ≠ none ↔ ∃ σ, IsSolution pathCSP dom σ := by
  have hdist : ∀ e ∈ pathCSP.arcs, e.1 ≠ e.2 := by decide
  exact BinaryCSP.exists_treeSolve_ne_none_iff_of_isAcyclic pathCSP
    (isSelector_minSel 4) pathSym hdist pathCSP_isAcyclic

/-- The star rooted at the leaf `1`: order `1, 0, 2, 3`. -/
def leafFirst : Fin 4 ≃ Fin (Fintype.card (Fin 4)) := (Equiv.swap 0 1).trans ord4

example : List.ofFn leafFirst.symm = [1, 0, 2, 3] := by
  decide
example : starCSP.orderParent leafFirst = ![some 1, none, some 0, some 0] := by
  decide
example : starCSP.orderWidth leafFirst ≤ 1 := by
  decide
example : ∃ σ, IsSolution starCSP starDom σ := by
  have hdist : ∀ e ∈ starCSP.arcs, e.1 ≠ e.2 := by decide
  have hw : starCSP.orderWidth leafFirst ≤ 1 := by decide
  have hne : treeSolve starCSP (starCSP.orderParent leafFirst)
      (List.ofFn leafFirst.symm) minSel starDom ≠ none := by decide
  exact (BinaryCSP.treeSolve_orderParent_ne_none_iff starCSP
    (isSelector_minSel 4) starSym hdist hw starDom).mp hne

/-- One edge and an isolated variable: two roots. -/
def edgeAndIsolate : BinaryCSP (Fin 3) (Fin 2) := edgeCSP [(0, 1)] fun a b => a ≠ b

example : edgeAndIsolate.orderParent ord3 = ![none, some 0, none] := by
  decide
example : edgeAndIsolate.orderWidth ord3 ≤ 1 := by
  decide

/-! ## The cycle counterexample has width two -/

theorem triangle_orderWidth (d : Fin 3 ≃ Fin (Fintype.card (Fin 3))) :
    triangle.orderWidth d = 2 := by
  have h : ∀ e : Fin 3 ≃ Fin (Fintype.card (Fin 3)), triangle.orderWidth e = 2 := by
    decide
  exact h d

theorem triangle_constraintWidth : triangle.constraintWidth = 2 := by
  obtain ⟨d, hd⟩ := BinaryCSP.exists_orderWidth_eq_constraintWidth triangle
  rw [← hd]
  exact triangle_orderWidth d

example : ¬triangle.constraintGraph.IsAcyclic := by
  intro h
  have hc := h.cliqueFree_three
  have hclique : triangle.constraintGraph.IsNClique 3 {0, 1, 2} := by
    refine ⟨?_, by decide⟩
    intro x hx y hy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> decide
  exact hc {0, 1, 2} hclique

example : triangle.orderParent ord3 = ![none, some 0, some 0] := by
  decide
example : greedy triangle (triangle.orderParent ord3) (List.ofFn ord3.symm) minSel
    (fun _ => Finset.univ) = some ![0, 1, 1] := by
  decide
example : ¬IsSolution triangle (fun _ => Finset.univ) ![0, 1, 1] := by
  unfold IsSolution
  decide
example : ∀ d : Fin 3 ≃ Fin (Fintype.card (Fin 3)),
    ¬IsTreeArcs triangle (triangle.orderParent d) := by
  unfold IsTreeArcs
  decide

/-! ## Countermodels for the hypotheses -/

/-- A self-arc that allows nothing. -/
def loopCSP : BinaryCSP (Fin 1) (Fin 2) := ⟨[(0, 0)], fun _ _ _ _ => false⟩

example : loopCSP.constraintGraph.IsAcyclic := by
  exact SimpleGraph.IsAcyclic.of_subsingleton
example : loopCSP.orderWidth ord1 ≤ 1 := by
  decide
example : ArcConsistency.Symmetric loopCSP := by
  unfold ArcConsistency.Symmetric
  decide
/-- Without `hdist` the forest theorem fails. -/
example : ¬(treeSolve loopCSP (loopCSP.orderParent ord1) (List.ofFn ord1.symm) minSel
    (fun _ => Finset.univ) ≠ none ↔ ∃ σ, IsSolution loopCSP (fun _ => Finset.univ) σ) := by
  have htree : treeSolve loopCSP (loopCSP.orderParent ord1) (List.ofFn ord1.symm) minSel
      (fun _ => Finset.univ) = some ![0] := by decide
  have hnosol : ¬∃ σ, IsSolution loopCSP (fun _ => Finset.univ) σ := by
    unfold IsSolution
    decide
  intro h
  rw [htree] at h
  exact hnosol (h.mp (by decide))

/-- The listed arc `(1, 0)` allows nothing; its reverse allows everything. -/
def asymCSP : BinaryCSP (Fin 2) (Fin 2) := ⟨[(1, 0)], fun x y _ _ => !(x == 1 && y == 0)⟩

example : ¬ArcConsistency.Symmetric asymCSP := by
  unfold ArcConsistency.Symmetric
  decide
example : asymCSP.orderWidth ord2 ≤ 1 := by
  decide
/-- Without `hsym` the prescribed-order result fails for the index order: the listed arc is
checked only parent-to-child. The existential form is refuted by `eqNeCSP` below. -/
example : ¬(treeSolve asymCSP (asymCSP.orderParent ord2) (List.ofFn ord2.symm) minSel
    (fun _ => Finset.univ) ≠ none ↔ ∃ σ, IsSolution asymCSP (fun _ => Finset.univ) σ) := by
  have htree : treeSolve asymCSP (asymCSP.orderParent ord2) (List.ofFn ord2.symm) minSel
      (fun _ => Finset.univ) = some ![0, 0] := by decide
  have hnosol : ¬∃ σ, IsSolution asymCSP (fun _ => Finset.univ) σ := by
    unfold IsSolution
    decide
  intro h
  rw [htree] at h
  exact hnosol (h.mp (by decide))

/-- Both directions listed: equality from `0` to `1`, disequality from `1` to `0`. -/
def eqNeCSP : BinaryCSP (Fin 2) (Fin 2) where
  arcs := [(0, 1), (1, 0)]
  allowed x y a b := if x = 0 ∧ y = 1 then decide (a = b) else decide (a ≠ b)

example : ¬ ArcConsistency.Symmetric eqNeCSP := by
  unfold ArcConsistency.Symmetric
  decide
example : ¬ ∃ σ, IsSolution eqNeCSP (fun _ => Finset.univ) σ := by
  unfold IsSolution
  decide
/-- Rooted at `0`, the algorithm succeeds although there is no solution. -/
example : treeSolve eqNeCSP ![none, some 0] [(0 : Fin 2), 1] minSel
    (fun _ => Finset.univ) ≠ none := by
  decide
/-- Rooted at `1`, the algorithm also succeeds: neither rooting detects the conflict, so
symmetry is necessary for the existential forest theorem, not only for a prescribed order. -/
example : treeSolve eqNeCSP ![some 1, none] [(1 : Fin 2), 0] minSel
    (fun _ => Finset.univ) ≠ none := by
  decide

/-- The path `0 - 1 - 2` listed as `(0, 1)`, `(2, 1)`. -/
def oneWay : BinaryCSP (Fin 3) (Fin 2) := ⟨[(0, 1), (2, 1)], fun _ _ _ _ => true⟩

example : oneWay.orderWidth ord3 ≤ 1 := by
  decide
/-- For `0 → 1 ← 2`, no parent map both covers every listed arc and has every parent edge
listed parent first. -/
example : ¬∃ parent : Fin 3 → Option (Fin 3), IsTreeArcs oneWay parent ∧
    ∀ x p, parent x = some p → (p, x) ∈ oneWay.arcs := by
  unfold IsTreeArcs
  intro h
  obtain ⟨parent, htree, hfirst⟩ := h
  have e1 : (0, 1) ∈ oneWay.arcs := by decide
  have e2 : (2, 1) ∈ oneWay.arcs := by decide
  have h01 : parent 1 = some 0 ∨ parent 0 = some 1 := htree (0, 1) e1
  have h21 : parent 1 = some 2 ∨ parent 2 = some 1 := htree (2, 1) e2
  rcases h01 with h1 | h1
  · rcases h21 with h2 | h2
    · rw [h1] at h2
      revert h2
      decide
    · exact absurd (hfirst 2 1 h2) (by decide)
  · exact absurd (hfirst 0 1 h1) (by decide)

/-! ## Both phases charged -/

example : (treeSolveT pathCSP pathParent [0, 1, 2, 3] minSel fun _ => Finset.univ).time = 45 := by
  decide
example : (treeSolveT pathCSP pathParent [0, 1, 2, 3] minSel fun _ => Finset.univ).time ≤
    4 * (4 * 4) + 4 * 4 := by
  have hd : ∀ v : Fin 4, (Finset.univ : Finset (Fin 4)).card ≤ 4 := by decide
  have h := treeSolveT_time_le pathCSP pathOrder (minSel (k := 4)) 4
    (fun _ : Fin 4 => Finset.univ) hd
  exact h
example : (treeSolveT pathCSP pathParent [0, 1, 2, 3] minSel fun _ => Finset.univ).ret =
    some ![0, 1, 2, 3] := by
  rw [treeSolveT_ret]
  decide

#print axioms BinaryCSP.orderParent_eq_some_iff
#print axioms BinaryCSP.rootedOrder_orderParent
#print axioms BinaryCSP.isTreeArcs_orderParent
#print axioms BinaryCSP.exists_orderWidth_le_one_of_isAcyclic
#print axioms BinaryCSP.exists_rootedOrder_of_isAcyclic
#print axioms BinaryCSP.treeSolve_orderParent_ne_none_iff
#print axioms BinaryCSP.exists_treeSolve_ne_none_iff_of_isAcyclic
#print axioms treeSolveT_ret
#print axioms treeSolveT_time_le
#print axioms triangle_constraintWidth

end CSLibExtTest.Algorithms.Lean.CSP.TreeCSPWidth
