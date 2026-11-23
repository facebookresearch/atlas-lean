/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ContourAnchor

/-!
# Dual cycles reaching the left half-plane are long

A closed walk in `ℤ²` through sites `u` and `b` has length at least twice their `ℓ¹` distance. A
dual cycle based at the upper exit face `(j, 0)` that also visits a face with nonpositive first
coordinate therefore has length greater than `j`, which is the anchoring condition of the Peierls
bound.

## Main definitions

* `StatMech.Lattice.CycleHasLeftFace ω hfin`: some dual cycle based at the upper exit face visits a
  face with nonpositive first coordinate.

## Main results

* `StatMech.Lattice.closedWalk_length_ge_two_l1dist`: a closed walk is at least twice as long as the
  distance from its base point to any of its vertices.
* `StatMech.Lattice.anchoredCycleExists_of_leftFace`: `CycleHasLeftFace` implies
  `AnchoredCycleExists`.
* `StatMech.Lattice.pcAnchoredEnclosure_of_cycleHasLeftFace`: if `CycleHasLeftFace` holds for every
  finite origin cluster, `StatMech.Percolation.PcAnchoredEnclosure` holds.
-/

@[expose] public section

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Percolation (anchorFinset origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}

theorem closedWalk_length_ge_two_l1dist
    {G : SimpleGraph (Site 2)} (hle : G ≤ hypercubicLattice 2)
    {u : Site 2} (c : G.Walk u u) {b : Site 2} (hb : b ∈ c.support) :
    2 * l1dist 2 u b ≤ c.length := by
  classical
  have hsplit : (c.takeUntil b hb).length + (c.dropUntil b hb).length = c.length := by
    rw [← Walk.length_append, Walk.take_spec]
  have hT : l1dist 2 u b ≤ (c.takeUntil b hb).length := by
    have h := l1dist_le_walk_length 2 ((c.takeUntil b hb).map (Hom.ofLE hle))
    rw [Walk.length_map] at h
    exact h
  have hD : l1dist 2 b u ≤ (c.dropUntil b hb).length := by
    have h := l1dist_le_walk_length 2 ((c.dropUntil b hb).map (Hom.ofLE hle))
    rw [Walk.length_map] at h
    exact h
  rw [l1dist_comm 2 b u] at hD
  omega

@[simp] theorem enclExitFaceUp_coord0 (hfin : (cluster 2 ω (origin 2)).Finite) :
    (exitFaceUp (ω := ω) hfin) 0 = (exitIndex (ω := ω) hfin : ℤ) := rfl

theorem exitIndex_le_l1dist_of_leftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    {w : Site 2} (hw : w 0 ≤ 0) :
    (exitIndex (ω := ω) hfin : ℕ) ≤ l1dist 2 (exitFaceUp (ω := ω) hfin) w := by
  classical
  unfold l1dist
  rw [Fin.sum_univ_two, enclExitFaceUp_coord0 (ω := ω) hfin]
  omega

/-- Some cycle of the face-boundary graph of the origin cluster, based at the upper exit face,
visits a face whose first coordinate is at most zero. -/
def CycleHasLeftFace (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  ∃ c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
      (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin),
    c.IsCycle ∧ ∃ w ∈ c.support, w 0 ≤ 0

theorem anchoredCycleExists_of_leftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    (hlf : CycleHasLeftFace ω hfin) : AnchoredCycleExists ω hfin := by
  obtain ⟨c, hcyc, w, hwsup, hw0⟩ := hlf
  refine ⟨c, hcyc, ?_⟩
  rcases Nat.eq_zero_or_pos (exitIndex (ω := ω) hfin) with hj | hj
  · rw [hj]
    exact lt_of_lt_of_le (by norm_num) hcyc.three_le_length
  · have hge : 2 * l1dist 2 (exitFaceUp (ω := ω) hfin) w ≤ c.length :=
      closedWalk_length_ge_two_l1dist (faceBoundaryGraph_le _) c hwsup
    have hdist : (exitIndex (ω := ω) hfin : ℕ) ≤ l1dist 2 (exitFaceUp (ω := ω) hfin) w :=
      exitIndex_le_l1dist_of_leftFace (ω := ω) hfin hw0
    omega

theorem anchoredEnclosure_of_cycleHasLeftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    (hlf : CycleHasLeftFace ω hfin) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u),
      c.IsCycle ∧ u ∈ anchorFinset c.length :=
  anchoredEnclosure_of_anchoredCycle (ω := ω) hfin
    (anchoredCycleExists_of_leftFace (ω := ω) hfin hlf)

theorem pcAnchoredEnclosure_of_cycleHasLeftFace
    (hlf : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        CycleHasLeftFace ω hfin) :
    StatMech.Percolation.PcAnchoredEnclosure := by
  intro ω hω
  exact anchoredEnclosure_of_cycleHasLeftFace (ω := ω) hω (hlf ω hω)

end Lattice

end StatMech
