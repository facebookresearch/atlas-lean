/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.ClusterAdaptiveProjection

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.ClusterAdaptiveProjection`

On the one-edge graph `⊤` on `Fin 2` with root set `{0}`:
* `clusterAdaptiveProjection_le` and `clusterAdaptiveProjection_idem` for every configuration;
* `clusterAdaptiveProjection_filter_eq_condFibre` at a projected configuration (fixed point by
  idempotence);
* `not_mem_clusterAdaptiveInsideEdges_of_explored_left` at the root, which reaches itself: no
  edge at the root is an inside edge.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.ClusterAdaptiveProjection

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- The projection lies below the configuration and is idempotent.
example (ρ : ConfigSpace (Sym2 (Fin 2))) :
    clusterAdaptiveProjection G2 {0} ρ ≤ ρ ∧
      clusterAdaptiveProjection G2 {0} (clusterAdaptiveProjection G2 {0} ρ) =
        clusterAdaptiveProjection G2 {0} ρ :=
  ⟨clusterAdaptiveProjection_le G2 _ ρ, clusterAdaptiveProjection_idem G2 _ ρ⟩

-- The fibre of the projection over a projected configuration is a conditioning fibre.
example (ρ : ConfigSpace (Sym2 (Fin 2))) :
    Finset.univ.filter (fun σ => clusterAdaptiveProjection G2 {0} σ =
        clusterAdaptiveProjection G2 {0} ρ) =
      condFibre (clusterAdaptiveInsideEdges G2 {0} (clusterAdaptiveProjection G2 {0} ρ))
        (clusterAdaptiveProjection G2 {0} ρ) :=
  clusterAdaptiveProjection_filter_eq_condFibre G2 _ _ (clusterAdaptiveProjection_idem G2 _ ρ)

-- A root is explored, so no edge at the root is an inside edge.
example (ρ : ConfigSpace (Sym2 (Fin 2))) (y : Fin 2) :
    s(0, y) ∉ clusterAdaptiveInsideEdges G2 {0} ρ :=
  not_mem_clusterAdaptiveInsideEdges_of_explored_left G2 _ ρ
    ⟨0, Finset.mem_singleton_self 0, SimpleGraph.Reachable.refl 0⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.ClusterAdaptiveProjection
