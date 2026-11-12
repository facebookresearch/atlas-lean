/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Walls.brt2routing
import Code.Foundations.CylinderDeriv
import Code.FK.Ergodicity

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}




theorem bdec_forceOpen_empty (ω : ConfigSpace (Sym2 (Site d))) :
    forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
  funext e; simp [forceOpenFinset]


theorem bdec_forceOpen_empty_preimage (A : Set (ConfigSpace (Sym2 (Site d)))) :
    (fun ω => forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω) ⁻¹' A = A := by
  ext ω; simp only [Set.mem_preimage, bdec_forceOpen_empty]






theorem bdec_posRouting_of_precursorPos (p : ℝ≥0) (hp1 : p ≤ 1) (n : ℕ)
    (a₁ a₂ a₃ : Site d)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
             (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    brt2_PosRouting (d := d) p hp1 n := by
  intro _htop
  refine ⟨∅, a₁, a₂, a₃, ?_⟩
  rw [bdec_forceOpen_empty_preimage]
  exact hpos








theorem bdec_cylinder_singleton_pos (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (I : Finset (Sym2 (Site d))) (η₀ : ConfigSpace ↥I) :
    0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (cylinder I {η₀}) := by
  rw [bernoulliProductMeasure_cylinder p hp1 I {η₀},
    bernoulliProductMeasure.apply_singleton (p := p) (hp := hp1) η₀]
  rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro e _
  by_cases h : η₀ e = true
  · rw [h, bernoulliMeasure_apply_true, ne_eq, ENNReal.coe_eq_zero]
    exact ne_of_gt hp0
  · rw [Bool.not_eq_true] at h
    rw [h, bernoulliMeasure_apply_false, ne_eq, ENNReal.coe_eq_zero]
    exact ne_of_gt (tsub_pos_iff_lt.mpr hplt)











theorem bdec_factor_finite_pos (p : ℝ≥0) (hp1 : p ≤ 1)
    {s t : Finset (Sym2 (Site d))} {S : Set (∀ i : s, Bool)} {T : Set (∀ i : t, Bool)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hdisj : Disjoint s t)
    (hSpos : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (cylinder s S))
    (hTpos : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (cylinder t T)) :
    0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (cylinder s S ∩ cylinder t T) := by
  rw [StatMech.FK.bernoulli_cylinder_factor p hp1 hS hT hdisj]
  exact ENNReal.mul_pos (ne_of_gt hSpos) (ne_of_gt hTpos)



















theorem bdec_precursorPos_of_decoupled (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (a₁ a₂ a₃ : Site d)
    (I : Finset (Sym2 (Site d))) (η₀ : ConfigSpace ↥I)
    (X : Set (ConfigSpace (Sym2 (Site d))))
    (hindep : bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          (cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ X)
        = bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (cylinder I ({η₀} : Set (ConfigSpace ↥I)))
          * bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 X)
    (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 X)
    (hgeo : cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ X ⊆ NeighborTrifPrecursor d a₁ a₂ a₃) :
    0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
      (NeighborTrifPrecursor d a₁ a₂ a₃) := by
  have hCpos := bdec_cylinder_singleton_pos p hp1 hp0 hplt I η₀
  have hInter : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (cylinder I {η₀} ∩ X) := by
    rw [hindep]; exact ENNReal.mul_pos (ne_of_gt hCpos) (ne_of_gt hXpos)
  exact lt_of_lt_of_le hInter (measure_mono hgeo)








theorem bdec_bk_of_precursorPos (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hpre : ∀ n : ℕ, ∃ a₁ a₂ a₃ : Site d,
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  brt2_bk_of_posRouting hd p hp1 hp0 (fun n => by
    obtain ⟨a₁, a₂, a₃, h⟩ := hpre n
    exact bdec_posRouting_of_precursorPos p hp1 n a₁ a₂ a₃ h)



theorem bdec_bk_atLeastTwo_of_precursorPos (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hpre : ∀ n : ℕ, ∃ a₁ a₂ a₃ : Site d,
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 :=
  (bdec_bk_of_precursorPos hd p hp1 hp0 hpre).2.1

end StatMech.Walls
