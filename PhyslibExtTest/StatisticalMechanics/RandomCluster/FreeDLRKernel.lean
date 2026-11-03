/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeDLRKernel

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FreeDLRKernel`

* `freeNestedWiringWeight_nonneg` and `freeNestedWiringWeight_sum_eq_one` for the identity
  embedding of the one-edge graph `⊤` on `Fin 2`, at `p = 1/2`, `q = 2`;
* `freeFiniteBox_marginal_specification` for boxes `1 < 2` in `ℤ²`;
* `freeInfiniteVolume_isFKDLR` in `ℤ²` at `p = 1/2`, `q = 1` and `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FreeDLRKernel

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

-- The nested wiring weights form a probability vector.
example : (∀ C, 0 ≤ freeNestedWiringWeight (⊤ : SimpleGraph (Fin 2)) id (1 / 2) 2 C) ∧
    ∑ C : SimpleGraph (Fin 2), freeNestedWiringWeight (⊤ : SimpleGraph (Fin 2)) id (1 / 2) 2 C
      = 1 :=
  ⟨freeNestedWiringWeight_nonneg _ _ (by norm_num) (by norm_num) (by norm_num),
   freeNestedWiringWeight_sum_eq_one _ _ Function.injective_id (by norm_num) (by norm_num)
    (by norm_num)⟩

-- The box marginal of the free measure on `Λ_2` is a wiring mixture on `Λ_1`.
example := freeFiniteBox_marginal_specification (d := 2) (N := 1) (m := 2) (by norm_num)
  (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) one_le_two

-- The free infinite-volume measure is FK-DLR (Bernoulli percolation and FK-Ising).
example := freeInfiniteVolume_isFKDLR (d := 2) (p := 1 / 2) (q := 1) (by norm_num)
  (by norm_num) le_rfl

-- The `q = 2` case.
example := freeInfiniteVolume_isFKDLR (d := 2) (p := 1 / 2) (q := 2) (by norm_num)
  (by norm_num) one_le_two

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FreeDLRKernel
