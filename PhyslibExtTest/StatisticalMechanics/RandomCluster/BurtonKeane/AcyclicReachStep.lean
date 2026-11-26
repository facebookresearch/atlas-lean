/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicReachStep

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicReachStep`

* `bgf_step3_witness`: the three-edge star on `Fin 4` is acyclic;
* `bgf_acyclic_of_reachSep` applied to the empty graph on `Fin 3` (both hypotheses vacuous);
* `bgf_acyclic_of_edgeLift` applied to the empty graph on `Fin 3`;
* `bgf_bc67_acyclic` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicReachStep

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The star with three edges is acyclic.
example : (SimpleGraph.fromEdgeSet {s((0 : Fin 4), 1), s((0 : Fin 4), 2),
    s((0 : Fin 4), 3)}).IsAcyclic :=
  bgf_step3_witness

-- The reach-separation criterion on the empty graph: the walk hypothesis is discharged by
-- `bgf_walkReach` with the empty graph lifted to itself.
example : (⊥ : SimpleGraph (Fin 3)).IsAcyclic :=
  bgf_acyclic_of_reachSep ⊥ (fun _ => ⊥) (fun _ _ _ h => h.elim)
    (fun t => bgf_walkReach ⊥ (fun _ => ⊥) t fun _ _ h => h.elim)

-- The edge-lift criterion on the empty graph.
example : (⊥ : SimpleGraph (Fin 3)).IsAcyclic :=
  bgf_acyclic_of_edgeLift ⊥ (fun _ => ⊥) (fun _ _ _ h => h.elim) (fun _ _ _ h => h.elim)

-- Cut and lift hypotheses in the contracted lattice give acyclicity.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {V : Type*} (G : SimpleGraph V)
    (embed : V → Site d)
    (Hcut : ∀ t a b, G.Adj t a → G.Adj t b → a ≠ b →
      ¬ (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b))
    (Hlift : ∀ t a b, G.Adj a b → t ≠ a → t ≠ b →
      (bc67_contractedLattice ω L (embed t)).Reachable (embed a) (embed b)) :
    G.IsAcyclic :=
  bgf_bc67_acyclic ω L G embed Hcut Hlift

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicReachStep
