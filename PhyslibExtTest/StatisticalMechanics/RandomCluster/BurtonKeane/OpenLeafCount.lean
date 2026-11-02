/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OpenLeafCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OpenLeafCount`

* `bel_leafOpenCount` evaluates to `0` in the all-closed and to `|F|` in the all-open
  configuration (instance).
* `bel_expLeaf_le` for the point mass at the all-open configuration (instance), and the first
  conjunct of `bel_status` for a constant family.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OpenLeafCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open MeasureTheory
open scoped ENNReal

-- No open edge in the all-closed configuration.
example (F : Finset (Sym2 (Site 2))) : bel_leafOpenCount F (fun _ => false) = 0 := by
  simp [bel_leafOpenCount]

-- Every edge open in the all-open configuration.
example (F : Finset (Sym2 (Site 2))) : bel_leafOpenCount F (fun _ => true) = F.card := by
  simp [bel_leafOpenCount]

-- The expected open count under a point mass is at most `|F|`.
example (F : Finset (Sym2 (Site 2))) :
    ∫⁻ ω, (bel_leafOpenCount F ω : ℝ≥0∞) ∂(Measure.dirac fun _ => true) ≤ (F.card : ℝ≥0∞) :=
  bel_expLeaf_le _ F

-- The summary's first conjunct for a constant family.
example (F : Finset (Sym2 (Site 2))) (R : ℕ) :
    ∫⁻ ω, (bel_leafOpenCount F ω : ℝ≥0∞) ∂(Measure.dirac fun _ => false) ≤ (F.card : ℝ≥0∞) :=
  (bel_status _ fun _ => F).1 R

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OpenLeafCount
