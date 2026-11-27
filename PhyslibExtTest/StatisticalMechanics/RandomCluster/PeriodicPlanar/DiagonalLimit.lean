/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.DiagonalLimit

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.DiagonalLimit`

On the square lattice at `p = 1 / 2`, `q = 1`:
* the diagonal root-to-boundary probabilities are antitone;
* they converge to `θ(1/2, 1)` (`wiredBufferedRootBoundary_diag_tendsto`);
* `wiredBufferedSetBoundary_diag_tendsto` for the empty set (`S = ∅ ⊆` any box).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.DiagonalLimit

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

-- Antitonicity of the diagonal root-to-boundary probabilities.
example : Antitone (fun n =>
    (square.wiredBufferedMeasure n (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      (zero_lt_one.trans_le le_rfl) : Measure (ConfigSpace (Sym2 _))).real
      (square.bufferedCylinder n (square.bufferedRootBoundaryEvent n))) :=
  square.wiredBufferedRootBoundary_diag_antitone (by norm_num) (by norm_num) le_rfl

-- Convergence of the diagonal probabilities to `θ(1/2, 1)`.
example : Tendsto (fun n =>
    (square.wiredBufferedMeasure n (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      (zero_lt_one.trans_le le_rfl) : Measure (ConfigSpace (Sym2 _))).real
      (square.bufferedCylinder n (square.bufferedRootBoundaryEvent n)))
    atTop (nhds (square.wiredPercolationProbability (1 / 2) 1)) :=
  square.wiredBufferedRootBoundary_diag_tendsto (by norm_num) (by norm_num) le_rfl

-- The set-to-boundary limit for the empty set.
example : Tendsto (fun n =>
    (square.wiredBufferedMeasure (0 + n) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      (zero_lt_one.trans_le le_rfl) : Measure (ConfigSpace (Sym2 _))).real
      (square.bufferedCylinder (0 + n) (square.bufferedSetBoundaryEvent ∅ (0 + n))))
    atTop (nhds ((square.wiredBufferedInfiniteVolume (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num) (zero_lt_one.trans_le le_rfl) : Measure (ConfigSpace (Sym2 _))).real
      (square.setHitsInfinite ∅))) :=
  square.wiredBufferedSetBoundary_diag_tendsto ∅ Set.finite_empty 0 (Set.empty_subset _)
    (by norm_num) (by norm_num) le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.DiagonalLimit
