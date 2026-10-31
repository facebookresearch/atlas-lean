/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleBoxCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleBoxCount`

* `bc82_coarseTcount_le_volume` applied to the all-closed configuration;
* instance: `bc82_borelCantelli_route_fails` at `L = 3` (the origin of `bc60_upperLines` is a
  contracted-lattice trifurcation);
* `bc82_coarseTcount_eq_volume_of_all_trif` and `bc82_expected_needs_upper_bound` in conditional
  form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SingleBoxCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory

variable {d : ℕ}

-- The coarse count never exceeds the volume.
example (L R : ℕ) :
    bc61_coarseTcount (d := d) (fun _ => false) L R ≤ (boxFinsetBK d R).card :=
  bc82_coarseTcount_le_volume _ L R

-- The origin of the upper-lines configuration is a contracted-lattice trifurcation at `L = 3`.
example : bc67_IsGnTrifurcation bc60_upperLines 3 (0 : Site 2) :=
  (bc82_borelCantelli_route_fails le_rfl).1

-- If every site is a coarse trifurcation, the count is the volume.
example (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hall : ∀ y ∈ boxFinsetBK d R, bc61_IsCoarseTrifurcation ω L y) :
    bc61_coarseTcount ω L R = (boxFinsetBK d R).card :=
  bc82_coarseTcount_eq_volume_of_all_trif ω L R hall

-- A configuration-wide `o(|B_R|)` bound forces zero coarse-trifurcation probability.
example (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (L : ℕ)
    (bdry : ℕ → ℕ) (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R)
    (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
    (hdens : Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop
      (nhds 0)) :
    μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 :=
  bc82_expected_needs_upper_bound μ L bdry hinv hbound hvol hdens

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SingleBoxCount
