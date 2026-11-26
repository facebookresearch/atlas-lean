/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.ParameterMonotonicity

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.ParameterMonotonicity`

On the square lattice at `q = 1`, `p₁ = 1 / 4 ≤ p₂ = 1 / 2`:
* `wiredBufferedInfiniteVolume_real_cylinder_monotone_in_p` for the increasing "all edges open"
  event of the buffered box of radius `0`;
* the same in finite volume (`wiredBufferedMeasure_real_cylinder_monotone_in_p`, `N = 0 ≤ m = 3`);
* `wiredPercolationProbability_monotoneOn_of_cylinderApproximation` compares `θ(1/4)` and
  `θ(1/2)` under an assumed cylinder approximation.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.ParameterMonotonicity

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory Set

-- Infinite-volume monotonicity of the "all open" cylinder.
example :
    (square.wiredBufferedInfiniteVolume (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
        (zero_lt_one.trans_le le_rfl) : Measure (ConfigSpace (Sym2 _))).real
        (square.bufferedCylinder 0 (Ici fun _ => true)) ≤
      (square.wiredBufferedInfiniteVolume (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
        (zero_lt_one.trans_le le_rfl) : Measure (ConfigSpace (Sym2 _))).real
        (square.bufferedCylinder 0 (Ici fun _ => true)) :=
  square.wiredBufferedInfiniteVolume_real_cylinder_monotone_in_p 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (isUpperSet_Ici _)

-- Finite-volume monotonicity of the same cylinder, in the box of radius `3`.
example :
    (square.wiredBufferedMeasure 3 (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
        (zero_lt_one.trans_le le_rfl) : Measure (ConfigSpace (Sym2 _))).real
        (square.bufferedCylinder 0 (Ici fun _ => true)) ≤
      (square.wiredBufferedMeasure 3 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
        (zero_lt_one.trans_le le_rfl) : Measure (ConfigSpace (Sym2 _))).real
        (square.bufferedCylinder 0 (Ici fun _ => true)) :=
  square.wiredBufferedMeasure_real_cylinder_monotone_in_p (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl (isUpperSet_Ici _)

-- Monotonicity of `θ` under a cylinder approximation.
example (happrox : square.HasPercolationCylinderApproximation 1) :
    square.wiredPercolationProbability (1 / 4) 1 ≤ square.wiredPercolationProbability (1 / 2) 1 :=
  square.wiredPercolationProbability_monotoneOn_of_cylinderApproximation le_rfl happrox
    (by norm_num) (by norm_num) (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.ParameterMonotonicity
