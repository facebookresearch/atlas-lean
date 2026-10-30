/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TwoDimensional.ZhangFourSides
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.TwoDimensional.ZhangFourSides`

* `zhg_complUnion_fkg_four` and `zhg_sqrt_trick_four` for a Dirac measure (positively associated)
  and four increasing events.
* `zhg_side_tendsto_one`, `zhg_inter_tendsto_one`, `zhg_union_tendsto_one_of_merge` for constant
  families.
* `zhg_union_of_geometricData` from `zhg_geometricData_satisfiable` under a Dirac measure.
* The refutation `zhg_corLowerBound_hypotheses_false`, restated: the hypotheses of the vacuous
  `zhg_corLowerBound` are contradictory. `zhg_corLowerBound` itself is not instantiated.
-/

@[expose] public section

open Filter MeasureTheory
open scoped NNReal Topology
open StatMech StatMech.Lattice StatMech.Universality StatMech.TwoDim

namespace MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.ZhangFourSides

/-- A Dirac measure on bond configurations is positively associated. -/
theorem dirac_positivelyAssociated (ω₀ : ConfigSpace (Sym2 (Site 2))) :
    PositivelyAssociated (Measure.dirac ω₀) := by
  intro A B _ _
  simp only [Measure.real, Measure.dirac_apply, Set.indicator]
  by_cases ha : ω₀ ∈ A <;> by_cases hb : ω₀ ∈ B <;> simp [ha, hb]

/-- All-open configuration. -/
def ωT : ConfigSpace (Sym2 (Site 2)) := fun _ => true

/-- The increasing event that a given pair is open. -/
def openAt (e : Sym2 (Site 2)) : Set (ConfigSpace (Sym2 (Site 2))) := {ω | ω e = true}

theorem openAt_inc (e : Sym2 (Site 2)) : IsIncreasing (openAt e) := by
  intro ω ω' h hω
  have := h e
  simp only [openAt, Set.mem_ofPred_eq] at hω ⊢
  rw [hω] at this
  exact le_antisymm le_top this

theorem openAt_meas (e : Sym2 (Site 2)) : MeasurableSet (openAt e) :=
  measurableSet_eq_fun (measurable_pi_apply e) measurable_const

example (a b c d : Sym2 (Site 2)) :
    (1 - (Measure.dirac ωT).real (openAt a)) * (1 - (Measure.dirac ωT).real (openAt b)) *
        (1 - (Measure.dirac ωT).real (openAt c)) * (1 - (Measure.dirac ωT).real (openAt d))
      ≤ 1 - (Measure.dirac ωT).real (openAt a ∪ openAt b ∪ openAt c ∪ openAt d) :=
  zhg_complUnion_fkg_four _ (dirac_positivelyAssociated ωT) (openAt_inc a) (openAt_inc b)
    (openAt_inc c) (openAt_inc d) (openAt_meas a) (openAt_meas b) (openAt_meas c) (openAt_meas d)

example (a : Sym2 (Site 2)) :
    1 - (1 - (Measure.dirac ωT).real (openAt a ∪ openAt a ∪ openAt a ∪ openAt a)) ^ ((1 : ℝ) / 4)
      ≤ (Measure.dirac ωT).real (openAt a) :=
  zhg_sqrt_trick_four _ (dirac_positivelyAssociated ωT) (openAt_inc a) (openAt_inc a)
    (openAt_inc a) (openAt_inc a) (openAt_meas a) (openAt_meas a) (openAt_meas a) (openAt_meas a)
    rfl rfl rfl

example : Tendsto (fun _ : ℕ => (Measure.dirac ωT).real (Set.univ : Set _)) atTop (𝓝 1) :=
  zhg_side_tendsto_one _ (dirac_positivelyAssociated ωT) (S₁ := fun _ => Set.univ)
    (S₂ := fun _ => Set.univ) (S₃ := fun _ => Set.univ) (fun _ => isUpperSet_univ)
    (fun _ => isUpperSet_univ) (fun _ => isUpperSet_univ) (fun _ => isUpperSet_univ)
    (fun _ => MeasurableSet.univ) (fun _ => MeasurableSet.univ) (fun _ => MeasurableSet.univ)
    (fun _ => MeasurableSet.univ) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (by simp only [Set.union_self, probReal_univ]; exact tendsto_const_nhds)

example : Tendsto (fun _ : ℕ => (Measure.dirac ωT).real (Set.univ ∩ Set.univ : Set _))
    atTop (𝓝 1) :=
  zhg_inter_tendsto_one _ (dirac_positivelyAssociated ωT) (fun _ => isUpperSet_univ)
    (fun _ => isUpperSet_univ) (by simp) (by simp)

example : Tendsto (fun n : ℕ => (Measure.dirac ωT).real
    ((fun _ : ℕ => (Set.univ : Set (ConfigSpace (Sym2 (Site 2))))) n ∪ Set.univ)) atTop (𝓝 1) :=
  zhg_union_of_geometricData _ (dirac_positivelyAssociated ωT)
    (zhg_geometricData_satisfiable (Measure.dirac ωT))

example {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hpa : PositivelyAssociated halfMeasure)
    (hAinc : ∀ n, IsIncreasing (A n)) (hBinc : ∀ n, IsIncreasing (B n))
    (hBm : ∀ n, MeasurableSet (B n)) (hHm : ∀ n, MeasurableSet (A n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (A n)ᶜ = (R ∘ dualConfig) ⁻¹' (A n))
    (heq : ∀ n, halfMeasure.real (A n) = halfMeasure.real (B n))
    (hgeo : ZhangGeometricData halfMeasure A B) : False :=
  zhg_corLowerBound_hypotheses_false hpa hAinc hBinc hBm hHm hRmeas hRpres hdich heq hgeo

end MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.ZhangFourSides
