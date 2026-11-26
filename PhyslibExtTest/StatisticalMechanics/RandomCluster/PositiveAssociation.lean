/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PositiveAssociation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PositiveAssociation`

On the one-edge graph `⊤` on `Fin 2` at `p = 1/2`, `q = 2`:
* `fkWeightNN_coe` (the `ℝ≥0` weight coerces to `fkWeight`);
* `fk_fkgCondition`: the FKG lattice condition;
* `fkProb_fkgLattice` at the all-closed and all-open configurations.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PositiveAssociation

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- The nonnegative weight is the FK weight.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    (fkWeightNN G2 (1 / 2) 2 (by norm_num) (by norm_num) two_pos ω : ℝ) =
      fkWeight G2 (1 / 2) 2 ω :=
  fkWeightNN_coe G2 _ _ _ ω

-- The FKG lattice condition for `q = 2`.
example := fk_fkgCondition G2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) one_le_two

-- The lattice inequality at the extreme configurations.
example : fkProb G2 (1 / 2) 2 (fun _ => false) * fkProb G2 (1 / 2) 2 (fun _ => true) ≤
    fkProb G2 (1 / 2) 2 ((fun _ => false) ⊓ fun _ => true) *
      fkProb G2 (1 / 2) 2 ((fun _ => false) ⊔ fun _ => true) :=
  fkProb_fkgLattice G2 (by norm_num) (by norm_num) one_le_two _ _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PositiveAssociation
