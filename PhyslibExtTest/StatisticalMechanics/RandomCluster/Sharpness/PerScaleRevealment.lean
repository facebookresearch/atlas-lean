/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.PerScaleRevealment

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.PerScaleRevealment`

* `psr_frontierConn_first_false_concrete` at the identity order on the 4-vertex witness;
* non-vacuity of `psr_FamilyFrontierConn`: it holds for the frontier `Set.univ`
  (`psr_familyFrontierConn_univ`) on the 4-vertex witness graph;
* `psr_reachOpen_allClosed` on the all-closed configuration of the witness graph;
* `psr_frontierConn_first_iff` applied to the identity order.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.PerScaleRevealment

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.PerScaleRevealmentClose
open _root_.StatMech.OSSS.ReachBoxCrossing _root_.StatMech.OSSS.ReachDomination
open _root_.StatMech.OSSS.RevealmentConstruction

-- The first-edge frontier connection fails for the identity order on the witness graph.
example :
    ¬ FrontierConn (Equiv.refl (Fin 3))
        (indicatorConn psr_witnessEndU psr_witnessEndV ({0} : Set (Fin 4)) ({3} : Set (Fin 4)))
        psr_witnessEndU psr_witnessEndV ({0} : Set (Fin 4)) (0 : Fin 3) :=
  psr_frontierConn_first_false_concrete (Equiv.refl (Fin 3)) rfl

-- The family frontier connection is satisfiable: frontier `univ` on the witness graph.
example (f : ConfigSpace (Fin 3) → ℝ) :
    psr_FamilyFrontierConn (fun _ : Unit => Equiv.refl (Fin 3)) f psr_witnessEndU
      psr_witnessEndV (fun _ => (Set.univ : Set (Fin 4))) :=
  psr_familyFrontierConn_univ _ f _ _

-- With every edge closed, only trivial open paths exist.
example {x y : Fin 4}
    (h : ReachOpen psr_witnessEndU psr_witnessEndV (fun _ => false) x y) : x = y :=
  psr_reachOpen_allClosed h

-- The first-edge characterization, for the identity order on three edges.
example (f : ConfigSpace (Fin 3) → ℝ) (B : Set (Fin 4)) :
    FrontierConn (Equiv.refl (Fin 3)) f psr_witnessEndU psr_witnessEndV B 0 ↔
      ∀ X : ConfigSpace (Fin 3), (∃ w, f w ≠ f X) →
        ConnOpenSet psr_witnessEndU psr_witnessEndV X (psr_witnessEndU 0) B ∨
          ConnOpenSet psr_witnessEndU psr_witnessEndV X (psr_witnessEndV 0) B :=
  psr_frontierConn_first_iff _ f _ _ B rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.PerScaleRevealment
