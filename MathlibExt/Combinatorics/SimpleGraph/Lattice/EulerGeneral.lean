/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CycleRank

/-!
# Euler's formula for finite graphs with several components

For every finite graph `G` with `c` connected components, `|V| - |E| + faceCount G = 1 + c`. The
face count is the cycle rank plus one (`StatMech.Lattice.faceCount`), so this is the combinatorial
form of Euler's formula. The file also records how deleting one edge changes the face count and the
number of components, according to whether the edge is a bridge.

## Main results

* `StatMech.Lattice.faceCount_deleteEdges_of_not_isBridge`: deleting a non-bridge lowers the face
  count by one and keeps the components.
* `StatMech.Lattice.faceCount_deleteEdges_of_isBridge`: deleting a bridge keeps the face count and
  adds a component.
* `StatMech.Lattice.euler_general`: Euler's formula `V - E + F = 1 + c`.

## References

* L. Euler, *Elementa doctrinae solidorum*, Novi Commentarii Academiae Scientiarum Petropolitanae 4
  (1758).
-/

@[expose] public section

open SimpleGraph Set

set_option linter.unusedSectionVars false

namespace StatMech.Lattice

variable {V : Type*} [Finite V] [DecidableEq V]

omit [DecidableEq V] in
theorem faceCount_deleteEdges_of_not_isBridge (G : SimpleGraph V) {a b : V}
    (he : s(a, b) ∈ G.edgeSet) (hr : (G.deleteEdges {s(a, b)}).Reachable a b) :
    faceCount (G.deleteEdges {s(a, b)}) + 1 = faceCount G ∧
      Nat.card (G.deleteEdges {s(a, b)}).ConnectedComponent
        = Nat.card G.ConnectedComponent := by
  classical
  set G' := G.deleteEdges {s(a, b)} with hG'
  have hGeq : G = G' ⊔ edge a b := deleteEdges_sup_edge_eq G a b he
  have hadjG : G.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at he
  have hne_ab : a ≠ b := G.ne_of_adj hadjG
  have hadj' : ¬ G'.Adj a b := by simp [hG', deleteEdges_adj]
  refine ⟨?_, ?_⟩
  · rw [hGeq]; exact (faceCount_sup_edge_of_reachable G' hne_ab hadj' hr).symm
  · rw [hGeq]; exact (card_components_sup_edge_of_reachable G' a b hr).symm

omit [DecidableEq V] in
theorem faceCount_deleteEdges_of_isBridge (G : SimpleGraph V) {a b : V}
    (he : s(a, b) ∈ G.edgeSet) (hr : ¬ (G.deleteEdges {s(a, b)}).Reachable a b) :
    faceCount (G.deleteEdges {s(a, b)}) = faceCount G ∧
      Nat.card (G.deleteEdges {s(a, b)}).ConnectedComponent
        = Nat.card G.ConnectedComponent + 1 := by
  classical
  set G' := G.deleteEdges {s(a, b)} with hG'
  have hGeq : G = G' ⊔ edge a b := deleteEdges_sup_edge_eq G a b he
  have hadjG : G.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at he
  have hne_ab : a ≠ b := G.ne_of_adj hadjG
  have hadj' : ¬ G'.Adj a b := by simp [hG', deleteEdges_adj]
  refine ⟨?_, ?_⟩
  · rw [hGeq]; exact (faceCount_sup_edge_of_not_reachable G' hne_ab hadj' hr).symm
  · have h := card_components_sup_edge_of_not_reachable G' a b hr
    rw [hGeq]; omega

omit [DecidableEq V] in
/-- **Euler's formula** for a finite graph with `c` connected components: `|V| - |E| + F = 1 + c`,
where `F = faceCount G`.

Here `F` is defined as the cycle rank plus one, so the statement is the combinatorial Euler
relation; it agrees with `StatMech.Lattice.euler_relation_sub` up to the order of the summands. That
`F` counts the faces of a plane embedding is a separate statement; for finite subgraphs of the
square lattice the bounded faces are counted in `StatMech.Lattice.jed_faithfulDiscreteJordan`.
Reference: L. Euler, *Elementa doctrinae solidorum* (1758). -/
theorem euler_general (G : SimpleGraph V) :
    (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G
      = 1 + Nat.card G.ConnectedComponent := by
  classical
  generalize hn : G.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · subst hz
      have hempty : G.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite G.edgeSet)).mp hn
      have hbot : G = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot
      have hfc : faceCount (⊥ : SimpleGraph V) = 1 := by
        unfold faceCount nullity; rw [card_components_bot]; simp [edgeSet_bot]
      rw [hfc, card_components_bot]; push_cast; ring
    · have hnonempty : G.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      obtain ⟨e, he⟩ := hnonempty
      obtain ⟨a, b⟩ := e
      set G' := G.deleteEdges {s(a, b)} with hG'
      have hdrop : G'.edgeSet.ncard + 1 = G.edgeSet.ncard :=
        card_edgeSet_deleteEdges_add_one G a b he
      have hn' : G'.edgeSet.ncard = n - 1 := by omega
      have ihG' : (Nat.card V : ℤ) - G'.edgeSet.ncard + faceCount G'
          = 1 + Nat.card G'.ConnectedComponent := by
        have := ih (n - 1) (by omega) G' hn'; rwa [hn']
      have hncast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      rw [hn', hncast] at ihG'
      by_cases hr : G'.Reachable a b
      · obtain ⟨hface, hcomp⟩ := faceCount_deleteEdges_of_not_isBridge G he hr
        have hface' : (faceCount G' : ℤ) + 1 = faceCount G := by exact_mod_cast hface
        have hcomp' : (Nat.card G'.ConnectedComponent : ℤ)
            = Nat.card G.ConnectedComponent := by exact_mod_cast hcomp
        linarith
      · obtain ⟨hface, hcomp⟩ := faceCount_deleteEdges_of_isBridge G he hr
        have hface' : (faceCount G' : ℤ) = faceCount G := by exact_mod_cast hface
        have hcomp' : (Nat.card G'.ConnectedComponent : ℤ)
            = Nat.card G.ConnectedComponent + 1 := by exact_mod_cast hcomp
        linarith

omit [DecidableEq V] in
/-- Euler's formula solved for the number of components: `c = |V| - |E| + F - 1`. -/
theorem euler_general_disconnected_components (G : SimpleGraph V) :
    (Nat.card G.ConnectedComponent : ℤ)
      = (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G - 1 := by
  have h := euler_general G; linarith

end StatMech.Lattice
