/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.FrameChangeIso
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.FrameChangeIso`

* `fci_faceDualConfig_measurePreserving`: self-duality of critical bond percolation with the face
  dual.
* `fci_faceOpenDual_eq_openSubgraph`, and the face-open dual graph of the all-closed configuration
  contains the edge between faces `(0, 0)` and `(1, 0)`.
* `fci_faceEdgeEquiv_mk_of_adj` at a concrete edge; the refutations `fci_no_frameChangeIso`,
  `fci_no_open_dual_relabel`.
* `fci_cluster_faceOpenDual_circuit` for the all-closed configuration (cluster `{0}`).
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW.Box StatMech.Universality SimpleGraph
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.FrameChangeIso

example : MeasureTheory.MeasurePreserving fci_faceDualConfig
    (bernoulliProductMeasure (2⁻¹ : NNReal) half_le_one)
    (bernoulliProductMeasure (2⁻¹ : NNReal) half_le_one) :=
  fci_faceDualConfig_measurePreserving

theorem adj10 : (hypercubicLattice 2).Adj ![0, 0] ![1, 0] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide

example : (fci_faceOpenDual (fun _ => false)).Adj ![0, 0] ![1, 0] := ⟨adj10, rfl⟩

example (w : ConfigSpace (Sym2 (Site 2))) :
    fci_faceOpenDual w = openSubgraph 2 (fci_faceDualConfig w) := fci_faceOpenDual_eq_openSubgraph w

example : fci_faceEdgeEquiv s(![0, 0], ![1, 0]) = sharedPrimalEdge ![0, 0] ![1, 0] :=
  fci_faceEdgeEquiv_mk_of_adj adj10

example : ¬ ∃ Φ : Site 2 → Site 2, fci_FrameCompat Φ := fci_no_frameChangeIso

example : ¬ ∃ Φ : Site 2 → Site 2, ∀ (f g : Site 2), (hypercubicLattice 2).Adj f g →
    sharedPrimalEdge f g = s(rot90Inv (Φ f), rot90Inv (Φ g)) := fci_no_open_dual_relabel

/-- In the all-closed configuration the cluster of `o` is `{o}`. -/
theorem cluster_closed (o : Site 2) : cluster 2 (fun _ => false) o = {o} := by
  ext y
  simp only [mem_cluster, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w⟩
    cases w with
    | nil => rfl
    | cons h _ => simp [openSubgraph_adj] at h
  · rintro rfl
    exact connected_refl _ _

example : ∃ (u : Site 2) (c : (fci_faceOpenDual (fun _ => false)).Walk u u), c.IsCycle :=
  fci_cluster_faceOpenDual_circuit (ω := fun _ => false) ![0, 0]
    (by rw [cluster_closed]; exact Set.finite_singleton _) adj10.toWalk
    (by rw [cluster_closed]; intro h; have := congrFun h 0; simp at this)

end MathlibExtTest.StatMech.Probability.Percolation.Universality.FrameChangeIso
