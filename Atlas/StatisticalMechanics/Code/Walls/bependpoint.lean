/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Mathlib
import Code.Walls.bfxtrifexist

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech.Walls

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000







theorem bep_threeMeetBox_subset_top (n : ℕ) :
    threeMeetBox 2 n ⊆ {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} :=
  fun _ hω => hω.1













def bep_encounter (p : ℝ≥0) (hp1 : p ≤ 1) : Prop :=
  0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} →
    ∃ a₁ a₂ a₃ : Site 2,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        (NeighborTrifPrecursor 2 a₁ a₂ a₃)











theorem bep_hroute_of_encounter (p : ℝ≥0) (hp1 : p ≤ 1) (henc : bep_encounter p hp1) :
    ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) →
        ∃ a₁ a₂ a₃ : Site 2,
          0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
            (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
  intro n hn
  exact henc (lt_of_lt_of_le hn (measure_mono (bep_threeMeetBox_subset_top n)))



theorem bep_encounter_of_hroute (p : ℝ≥0) (hp1 : p ≤ 1)
    (hroute : ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) →
        ∃ a₁ a₂ a₃ : Site 2,
          0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
            (NeighborTrifPrecursor 2 a₁ a₂ a₃)) :
    bep_encounter p hp1 := by
  intro htop
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1) htop
  exact hroute n hn





theorem bep_encounter_iff_hroute (p : ℝ≥0) (hp1 : p ≤ 1) :
    bep_encounter p hp1 ↔
      (∀ n : ℕ,
        0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) →
          ∃ a₁ a₂ a₃ : Site 2,
            0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
              (NeighborTrifPrecursor 2 a₁ a₂ a₃)) :=
  ⟨bep_hroute_of_encounter p hp1, bep_encounter_of_hroute p hp1⟩













theorem bep_bk_of_encounter (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (henc : bep_encounter p hp1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          {ω | numInfiniteClusters 2 ω ≤ 1} = 1 :=
  bfx_bk_of_route (by norm_num) p hp1 hp0 (bep_hroute_of_encounter p hp1 henc)



theorem bep_bk_atLeastTwo_of_encounter (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (henc : bep_encounter p hp1) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  (bep_bk_of_encounter p hp1 hp0 henc).2.1

end StatMech.Walls
