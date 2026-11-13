/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.CrossingParity
import Code.Lattice.ContourAnchor
import Code.Lattice.EnclosingLength
import Code.Lattice.LeftFace
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.BoundaryConnected
import Code.Lattice.ContourLinksExits
import Code.Percolation.PcUpperUncond
import Code.Percolation.PcNontrivial

open Finset Set SimpleGraph Function

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}





























def DiscreteJordanSeparation : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → ∀ {a b : Site 2},
    (faceBoundaryGraph K).Reachable a b →
      ∃ c : (faceBoundaryGraph K).Walk a a, c.IsCycle ∧ b ∈ c.support


















theorem enclosingContourLinksExits_of_jordan (hJordan : DiscreteJordanSeparation)
    (hfin : (cluster 2 ω (origin 2)).Finite) (hsame : ExitDartsSameOrbit ω hfin) :
    EnclosingContourLinksExits ω hfin := by
  
  have hreach :
      (faceBoundaryGraph (cluster 2 ω (origin 2))).Reachable
        (exitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) :=
    exitFaces_reachable_of_sameOrbit (ω := ω) hfin hsame
  
  
  have hadjLeft :
      (faceBoundaryGraph (cluster 2 ω (origin 2))).Reachable
        (leftExitFaceDown (ω := ω) hfin) (leftExitFaceUp (ω := ω) hfin) :=
    ((leftExitFaces_faceBoundaryGraph_adj (ω := ω) hfin).symm).reachable
  have hreachUp :
      (faceBoundaryGraph (cluster 2 ω (origin 2))).Reachable
        (exitFaceUp (ω := ω) hfin) (leftExitFaceUp (ω := ω) hfin) :=
    hreach.trans hadjLeft
  
  obtain ⟨c, hcyc, hmem⟩ :=
    hJordan (cluster 2 ω (origin 2)) hfin hreachUp
  exact ⟨c, hcyc, hmem⟩

















theorem finite_cluster_dual_circuit (hJordan : DiscreteJordanSeparation)
    (hfin : (cluster 2 ω (origin 2)).Finite) (hsame : ExitDartsSameOrbit ω hfin) :
    ∃ c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
        (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin),
      c.IsCycle ∧ ∃ w ∈ c.support, w 0 ≤ 0 :=
  cycleHasLeftFace_of_enclosingContourLinksExits (ω := ω) hfin
    (enclosingContourLinksExits_of_jordan (ω := ω) hJordan hfin hsame)









theorem finite_cluster_dual_circuit_separates (hJordan : DiscreteJordanSeparation)
    (hfin : (cluster 2 ω (origin 2)).Finite) (hsame : ExitDartsSameOrbit ω hfin) :
    (∃ c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
        (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin),
      c.IsCycle ∧ ∃ w ∈ c.support, w 0 ≤ 0) ∧
    (∀ {z : Site 2}, z ∉ cluster 2 ω (origin 2) →
      ¬ (latticeMinusBarrier (cluster 2 ω (origin 2))).Reachable (origin 2) z) ∧
    (∀ {z : Site 2}, z ∉ cluster 2 ω (origin 2) →
      ∀ w : (hypercubicLattice 2).Walk (origin 2) z,
        ¬ Even (crossCount (cluster 2 ω (origin 2)) w)) := by
  refine ⟨finite_cluster_dual_circuit (ω := ω) hJordan hfin hsame, ?_, ?_⟩
  · intro z hz
    exact cluster_separated_from_exterior (origin 2) hz
  · intro z hz w
    exact origin_crossCount_odd (origin 2) hz w












theorem pcAnchoredEnclosure_of_jordan (hJordan : DiscreteJordanSeparation)
    (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        ExitDartsSameOrbit ω hfin) :
    PcAnchoredEnclosure :=
  StatMech.Lattice.pcAnchoredEnclosure_of_enclosingContourLinksExits
    (fun ω hfin => enclosingContourLinksExits_of_jordan (ω := ω) hJordan hfin (hsame ω hfin))













theorem pc_lt_one_of_jordan (hJordan : DiscreteJordanSeparation)
    (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        ExitDartsSameOrbit ω hfin) :
    pc 2 < 1 :=
  pc_lt_one_of_enclosure (pcAnchoredEnclosure_of_jordan hJordan hsame)







theorem pc_pos_and_lt_one_of_jordan (hJordan : DiscreteJordanSeparation)
    (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        ExitDartsSameOrbit ω hfin) :
    0 < pc 2 ∧ pc 2 < 1 :=
  ⟨pc_pos (by norm_num), pc_lt_one_of_jordan hJordan hsame⟩

end Percolation

end StatMech
