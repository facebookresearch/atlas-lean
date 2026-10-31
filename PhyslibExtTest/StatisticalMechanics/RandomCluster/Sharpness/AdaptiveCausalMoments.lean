/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalMoments

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalMoments`

Both checks use the random-cluster mass on the complete graph on `Fin 2` at `p = 1/2`, `q = 2`,
and the one-query decision tree on `s(0, 1)`.

* `flipTripleProb_left_marginal_extendDecisionTreeTriple` with the frozen set `{s(0, 1)}` and
  `R` its complement;
* `flipCrossTripleProb_right_marginal_extendDecisionTreeTriple` with no frozen coordinates.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalMoments

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveCausalKernel
open _root_.StatMech.OSSS.MonotonicFK _root_.StatMech.OSSS.Monotonic

-- Left marginal of the flipped triple coupling, with `s(0, 1)` frozen.
example (driver leftSeed right known : ConfigSpace (Sym2 (Fin 2))) (z : Sym2 (Fin 2)) (t : ℕ) :
    baseSum {s(0, 1)} leftSeed (fun left =>
      flipTripleProb (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) {s(0, 1)} driver left right z
        (extendDecisionTreeTriple (some t) (.node s(0, 1) (.leaf true) (.leaf false)) known
          (Finset.univ \ {s(0, 1)}))) =
      condMass (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) {s(0, 1)} right right *
        flipBaseProb (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) {s(0, 1)} driver z
          (extendDecisionTreeTriple (some t) (.node s(0, 1) (.leaf true) (.leaf false)) known
            (Finset.univ \ {s(0, 1)})) :=
  flipTripleProb_left_marginal_extendDecisionTreeTriple _
    (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num)) _ driver leftSeed right z t _
    known _ rfl

-- Right marginal of the flipped cross coupling, with no frozen coordinates.
example (driver left rightSeed known : ConfigSpace (Sym2 (Fin 2))) (z : Sym2 (Fin 2)) (t : ℕ) :
    baseSum ∅ rightSeed (fun right =>
      flipCrossTripleProb (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ∅ driver left right z
        (extendDecisionTreeTriple (some t) (.node s(0, 1) (.leaf true) (.leaf false)) known
          Finset.univ)) =
      condMass (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ∅ left left *
        flipBaseProb (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ∅ driver z
          (extendDecisionTreeTriple (some t) (.node s(0, 1) (.leaf true) (.leaf false)) known
            Finset.univ) :=
  flipCrossTripleProb_right_marginal_extendDecisionTreeTriple _
    (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num)) _ driver left rightSeed z t _
    known _ (Finset.sdiff_empty).symm

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalMoments
