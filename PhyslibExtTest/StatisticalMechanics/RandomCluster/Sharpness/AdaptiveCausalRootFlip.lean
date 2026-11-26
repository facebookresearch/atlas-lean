/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalRootFlip

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalRootFlip`

Both checks use the random-cluster mass on the complete graph on `Fin 2` at `p = 1/2`, `q = 2`,
no frozen coordinates, and a triple order whose root flips the edge `s(0, 1)` (subtrees arbitrary).

* `baseSum_coord_mul_crossTripleProb_right_rootFlip_eq_cExp_mul_condMass`;
* `baseSum_coord_mul_crossTripleProb_left_rootFlip_eq_cExp_mul_condMass`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalRootFlip

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveCausalKernel
open _root_.StatMech.OSSS.MonotonicFK _root_.StatMech.OSSS.Monotonic

/-- The random-cluster mass on `K₂` at `p = 1/2`, `q = 2`. -/
local notation "μ₂" => fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2

/-- Positivity of `μ₂`. -/
theorem mu2_pos (ω : ConfigSpace (Sym2 (Fin 2))) : 0 < μ₂ ω :=
  fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num) ω

/-- `μ₂` is a probability mass. -/
theorem mu2_sum : ∑ ω, μ₂ ω = 1 :=
  fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)

-- Right root-flip identity on `K₂`.
example (driver left rightSeed : ConfigSpace (Sym2 (Fin 2)))
    (closed opened : TripleOrder ((Finset.univ : Finset (Sym2 (Fin 2))).erase s(0, 1))) :
    baseSum ∅ rightSeed (fun right =>
        Lindeberg.coord s(0, 1) right *
          crossTripleProb μ₂ ∅ driver left right
            (.node s(0, 1) (Finset.mem_univ _) .flip closed opened)) =
      Lindeberg.cExp μ₂ ∅ (Lindeberg.coord s(0, 1)) rightSeed *
        condMass μ₂ ∅ left left :=
  baseSum_coord_mul_crossTripleProb_right_rootFlip_eq_cExp_mul_condMass _
    mu2_pos ∅ driver left rightSeed s(0, 1) _ closed opened
    Finset.sdiff_empty.symm

-- Left root-flip identity on `K₂`.
example (driver right leftSeed : ConfigSpace (Sym2 (Fin 2)))
    (closed opened : TripleOrder ((Finset.univ : Finset (Sym2 (Fin 2))).erase s(0, 1))) :
    baseSum ∅ leftSeed (fun left =>
        Lindeberg.coord s(0, 1) left *
          crossTripleProb μ₂ ∅ driver left right
            (.node s(0, 1) (Finset.mem_univ _) .flip closed opened)) =
      Lindeberg.cExp μ₂ ∅ (Lindeberg.coord s(0, 1)) leftSeed *
        condMass μ₂ ∅ right right :=
  baseSum_coord_mul_crossTripleProb_left_rootFlip_eq_cExp_mul_condMass _
    mu2_pos ∅ driver right leftSeed s(0, 1) _ closed opened
    Finset.sdiff_empty.symm

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalRootFlip
