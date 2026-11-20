/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Mathlib
import Code.Walls.bclclose

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech.Walls

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000









theorem bcl2_threeMeetBox_subset_top (n : ℕ) :
    threeMeetBox 2 n ⊆ {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} := by
  intro ω hω
  exact hω.1





theorem bcl2_tripleEvent_pos_of_threeMeetBox (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n)) :
    ∃ (m : ℕ) (x y z : Site 2),
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bxp_tripleEvent 2 m x y z) := by
  have htop : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = ⊤} :=
    lt_of_lt_of_le hpos (measure_mono (bcl2_threeMeetBox_subset_top n))
  exact bxp_exists_triple_pos (d := 2) p hp1 htop

















def bcl2_Bridge (p : ℝ≥0) (hp1 : p ≤ 1) : Prop :=
  ∀ (m : ℕ) (x y z : Site 2),
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bxp_tripleEvent 2 m x y z) →
      ∃ (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ : Site 2) (η₀ : ConfigSpace ↥I),
        (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
        ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
          (hypercubicLattice 2).Adj 0 a₃) ∧
        (∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)),
          Connected 2 (removeSite 0 ω) a₁ x ∧ Connected 2 (removeSite 0 ω) a₂ y ∧
            Connected 2 (removeSite 0 ω) a₃ z) ∧
        MeasurableSet (bpt2_Ext I a₁ a₂ a₃ x y z) ∧
        0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (bpt2_Ext I a₁ a₂ a₃ x y z)









theorem bcl2_hroute_of_bridge (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hbridge : bcl2_Bridge p hp1) :
    ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (threeMeetBox 2 n) →
        ∃ a₁ a₂ a₃ : Site 2,
          0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
            (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
  intro n hpos
  obtain ⟨m, x, y, z, htriple⟩ := bcl2_tripleEvent_pos_of_threeMeetBox p hp1 n hpos
  obtain ⟨I, a₁, a₂, a₃, η₀, hne, hadj, hcorr, hExtMeas, hXpos⟩ := hbridge m x y z htriple
  exact ⟨a₁, a₂, a₃,
    bcl_precursorPos p hp1 hp0 hplt I a₁ a₂ a₃ x y z η₀ hne hadj hcorr hExtMeas hXpos⟩





theorem bcl2_bk_of_bridge (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hbridge : bcl2_Bridge p hp1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          {ω | numInfiniteClusters 2 ω ≤ 1} = 1 :=
  bfx_bk_of_route (by norm_num) p hp1 hp0 (bcl2_hroute_of_bridge p hp1 hp0 hplt hbridge)



theorem bcl2_bk_atLeastTwo_of_bridge (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hbridge : bcl2_Bridge p hp1) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  (bcl2_bk_of_bridge p hp1 hp0 hplt hbridge).2.1

end StatMech.Walls
