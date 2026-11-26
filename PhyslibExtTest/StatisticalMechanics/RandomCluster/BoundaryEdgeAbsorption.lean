/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BoundaryEdgeAbsorption

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BoundaryEdgeAbsorption`

On `Fin 2` with the whole vertex set as boundary, the single edge of `⊤` joins two boundary
vertices, so `⊥ ≤ ⊤ ≤ ⊥ ⊔ K_∂`:
* `activeBCMean_eq_of_le_sup_boundaryClique` identifies the wired expectations on `⊤` and on `⊥`;
* `activeBCZ_eq_of_le_sup_boundaryClique` identifies the partition functions;
* `boundaryReachable_iff_of_le_sup_boundaryClique` with boundary `{1}` and interior root `0`
  (for `G = H = ⊤`);
* `finiteRootBoundaryEvent_isIncreasing` and `outerRootBoundaryEvent_subset_innerRestrict` for the
  identity embedding of the empty graph on `Fin 2` with empty outer boundary.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BoundaryEdgeAbsorption

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

/-- The single edge of `⊤` on `Fin 2` is absorbed by the all-boundary clique. -/
theorem top_le_bot_sup : (⊤ : SimpleGraph (Fin 2)) ≤
    ⊥ ⊔ boundaryCliqueGraph (fun _ : Fin 2 => True) := by
  intro x y h
  right
  simpa [boundaryCliqueGraph, Lattice.wireRel] using h

-- The wired expectations on `⊤` and on `⊥` agree.
example (p q : ℝ) (f : ConfigSpace (⊥ : SimpleGraph (Fin 2)).edgeSet → ℝ) :
    activeBCMean ⊤ (boundaryCliqueGraph fun _ : Fin 2 => True) (fun _ => p) q
        (fun η => f (activeGraphRestrict ⊥ ⊤ bot_le η)) =
      activeBCMean ⊥ (boundaryCliqueGraph fun _ : Fin 2 => True) (fun _ => p) q f :=
  activeBCMean_eq_of_le_sup_boundaryClique _ _ _ bot_le top_le_bot_sup p q f

-- The partition functions on `⊤` and on `⊥` agree.
example (p q : ℝ) :
    activeBCZ ⊤ (boundaryCliqueGraph fun _ : Fin 2 => True) (fun _ => p) q =
      activeBCZ ⊥ (boundaryCliqueGraph fun _ : Fin 2 => True) (fun _ => p) q :=
  activeBCZ_eq_of_le_sup_boundaryClique _ _ _ bot_le top_le_bot_sup p q

-- Boundary reachability from an interior root is the same in `G = H = ⊤`.
example (η : ConfigSpace (⊤ : SimpleGraph (Fin 2)).edgeSet) :
    (∃ y : Fin 2, y = 1 ∧ (openSub ⊤ (extendActive ⊤ η)).Reachable 0 y) ↔
      ∃ y : Fin 2, y = 1 ∧
        (openSub ⊤ (extendActive ⊤ (activeGraphRestrict ⊤ ⊤ le_rfl η))).Reachable 0 y :=
  boundaryReachable_iff_of_le_sup_boundaryClique _ _ (· = 1) le_rfl le_sup_left
    (by decide) η

-- The root-to-boundary event is increasing, and nests along the identity embedding.
example : IsIncreasing (finiteRootBoundaryEvent (⊤ : SimpleGraph (Fin 2)) (· = 1) 0) ∧
    finiteRootBoundaryEvent (⊥ : SimpleGraph (Fin 2)) (fun _ => False) (id 0) ⊆
      ocd_innerRestrict id ⁻¹' finiteRootBoundaryEvent (⊥ : SimpleGraph (Fin 2))
        (fun _ => True) 0 :=
  ⟨finiteRootBoundaryEvent_isIncreasing _ _ _,
   outerRootBoundaryEvent_subset_innerRestrict ⊥ ⊥ id (fun _ => True) (fun _ => False)
    (fun _ _ => Iff.rfl) (fun _ h => h) (fun _ _ h => absurd h (by simp)) 0⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BoundaryEdgeAbsorption
