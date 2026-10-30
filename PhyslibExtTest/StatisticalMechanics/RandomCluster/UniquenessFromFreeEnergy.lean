/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.UniquenessFromFreeEnergy

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FKUniquenessSkeleton`

On `ℤ²`, box `Λ_1`, at `t = 0` (`p = logistic 0 = 1/2`), `q = 2`:
* `fuc_freeMass` and `fuc_wiredMass` (box restrictions of the infinite-volume measures) are
  nonnegative mass functions;
* `fuc_dominated`: the free restriction is stochastically dominated by the wired one, and its
  consequence for the increasing event `Set.univ`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKUniquenessSkeleton

open MeasureTheory _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

-- At `t = 0` the logistic parameter is `1/2`.
example : fsc_logistic 0 = 1 / 2 := by norm_num [fsc_logistic]

-- The box mass functions are nonnegative.
example (ω : ConfigSpace (Sym2 (boxVerts 2 1))) :
    0 ≤ fuc_freeMass 2 1 0 ω ∧ 0 ≤ fuc_wiredMass 2 1 0 ω :=
  ⟨measureReal_nonneg, measureReal_nonneg⟩

-- Free `≼` wired on `Λ_1` at `t = 0`.
example : measOfMass (fuc_freeMass 2 1 0) ≼ measOfMass (fuc_wiredMass 2 1 0) :=
  fuc_dominated 2 1 0

-- Consequence for an increasing event.
example : (measOfMass (fuc_freeMass 2 1 0)).real Set.univ
    ≤ (measOfMass (fuc_wiredMass 2 1 0)).real Set.univ :=
  fuc_dominated 2 1 0 _ MeasurableSet.univ fun _ _ _ _ => trivial

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKUniquenessSkeleton
