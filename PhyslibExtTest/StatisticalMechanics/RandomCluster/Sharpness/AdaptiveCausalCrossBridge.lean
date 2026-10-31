/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalCrossBridge

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalCrossBridge`

All checks use the one-query decision tree on `s(0, 1)` over the edges of the complete graph on
`Fin 2`.

* `realizedList_extendDecisionTreeTriple`: the left order of the triple extension realizes the
  same schedule as the plain extension;
* `realizedEquiv_extendDecisionTreeTriple`: the same for the realized equivalence;
* `cross_flip_atom_sum_eq_flipCrossTripleProb_sum` for the random-cluster mass at `p = 1/2`,
  `q = 2`, with the open-edge test function.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalCrossBridge

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveCausalKernel
open _root_.StatMech.OSSS.MonotonicFK

-- The left order of the triple extension realizes the plain extension's schedule.
example (phase : Option ℕ) (known base : ConfigSpace (Sym2 (Fin 2))) :
    realizedList (extendDecisionTreeTriple phase (.node s(0, 1) (.leaf true) (.leaf false)) known
        Finset.univ).leftOrder base =
      realizedList (extendDecisionTree (.node s(0, 1) (.leaf true) (.leaf false)) known
        Finset.univ) base :=
  realizedList_extendDecisionTreeTriple phase _ known base _

-- The same for the realized equivalence.
example (phase : Option ℕ) (known base : ConfigSpace (Sym2 (Fin 2))) :
    realizedEquiv (extendDecisionTreeTriple phase (.node s(0, 1) (.leaf true) (.leaf false))
        known Finset.univ).leftOrder base =
      realizedEquiv (extendDecisionTree (.node s(0, 1) (.leaf true) (.leaf false)) known
        Finset.univ) base :=
  realizedEquiv_extendDecisionTreeTriple phase _ known base

-- Atom sums equal flipped cross triple-probability sums, for the FK mass on `K₂`.
example (seed known : ConfigSpace (Sym2 (Fin 2))) :
    (∑ base,
      (if tripleModeAt (extendDecisionTreeTriple (some 0)
          (.node s(0, 1) (.leaf true) (.leaf false)) known Finset.univ) base s(0, 1) = .flip
        then 1 else 0) *
        (∑ left, ∑ right,
          (if left s(0, 1) then 1 else 0) * (if right s(0, 1) then 1 else 0) *
            crossTripleJointProb (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ∅ base left right
              (extendDecisionTreeTriple (some 0) (.node s(0, 1) (.leaf true) (.leaf false)) known
                Finset.univ))) =
      ∑ left, ∑ right,
        (if left s(0, 1) then 1 else 0) * (if right s(0, 1) then 1 else 0) *
          flipCrossTripleProb (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) ∅ seed left right
            s(0, 1) (extendDecisionTreeTriple (some 0) (.node s(0, 1) (.leaf true) (.leaf false))
              known Finset.univ) :=
  cross_flip_atom_sum_eq_flipCrossTripleProb_sum _ seed s(0, 1) _
    (fun left right => (if left s(0, 1) then 1 else 0) * (if right s(0, 1) then 1 else 0))

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalCrossBridge
