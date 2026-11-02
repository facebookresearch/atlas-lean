/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.EdgeConfigEventLaw

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.EdgeConfigEventLaw`

On the one-edge graph `⊤` on `Fin 2` (every other `Sym2` element is a non-edge):
* `ecz_closeOff_val` as a `simp` lemma;
* `ecz_eventWeight_factorization` and `fkProb_closeOff_preimage_eq` for the sure event at
  `p = 1/2`, `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.EdgeConfigEventLaw

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- Closing off a closed-off configuration does nothing.
example (ω : ecz_ClosedOff G2) : ecz_closeOff G2 ω.1 = ω := by simp

-- The weight of the sure event factorizes over the non-edges.
example : (∑ ω : ConfigSpace (Sym2 (Fin 2)),
      (ecz_closeOff G2 ⁻¹' Set.univ).indicator (fun ω => fkWeight G2 (1 / 2) 2 ω) ω) =
    2 ^ ecz_NE G2 * ecz_eventWeight G2 (1 / 2) 2 Set.univ :=
  ecz_eventWeight_factorization G2 _ _ _

-- The probability of the sure event through closed-off configurations.
example : (∑ ω : ConfigSpace (Sym2 (Fin 2)),
      (ecz_closeOff G2 ⁻¹' Set.univ).indicator (fun _ => (1 : ℝ)) ω * fkProb G2 (1 / 2) 2 ω) =
    ecz_eventWeight G2 (1 / 2) 2 Set.univ / ecz_fkZEdge G2 (1 / 2) 2 :=
  fkProb_closeOff_preimage_eq G2 _ _ _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.EdgeConfigEventLaw
