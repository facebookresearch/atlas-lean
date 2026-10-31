/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrecursorDecoupling

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrecursorDecoupling`

* instance: at `p = 1/2`, the cylinder event "a given edge is open" has positive Bernoulli
  probability (`bdec_cylinder_singleton_pos`);
* `bdec_forceOpen_empty_preimage`: opening no edges changes no event;
* `bdec_posRouting_of_precursorPos` and `bdec_bk_atLeastTwo_of_precursorPos` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.PrecursorDecoupling

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open MeasureTheory _root_.StatMech.ConfigSpace
open scoped NNReal

variable {d : ℕ}

/-- One open edge, as a configuration on the singleton index set. -/
def η₁ (e : Sym2 (Site d)) : ConfigSpace (↥({e} : Finset (Sym2 (Site d)))) := fun _ => true

-- At `p = 1/2` a single-edge cylinder has positive probability.
example (e : Sym2 (Site d)) :
    0 < bernoulliProductMeasure (E := Sym2 (Site d)) (1 / 2) (by norm_num)
      (cylinder ({e} : Finset (Sym2 (Site d))) {η₁ e}) :=
  bdec_cylinder_singleton_pos _ _ (by norm_num) (by norm_num) _ _

-- Opening the empty edge set is the identity on events.
example (A : Set (ConfigSpace (Sym2 (Site d)))) :
    (fun ω => forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω) ⁻¹' A = A :=
  bdec_forceOpen_empty_preimage A

-- A positive-probability precursor gives positive routing.
example (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ) (a₁ a₂ a₃ : Site d)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    brt2_PosRouting (d := d) p hp1 n :=
  bdec_posRouting_of_precursorPos p hp1 n a₁ a₂ a₃ hpos

-- Positive precursors exclude two infinite clusters.
example (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hpre : ∀ _n : ℕ, ∃ a₁ a₂ a₃ : Site d,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 :=
  bdec_bk_atLeastTwo_of_precursorPos hd p hp1 hp0 hpre

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.PrecursorDecoupling
