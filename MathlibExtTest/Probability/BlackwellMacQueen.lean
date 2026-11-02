/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BlackwellMacQueen
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-!
# Tests for the Blackwell–MacQueen urn
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
open MathlibExt.Biology.PopulationGenetics.ChineseRestaurant

namespace MathlibExtTest.Probability.BlackwellMacQueen

variable {X : Type*} [MeasurableSpace X]

/-- One draw has the base law: `P(X₀ ∈ A) = H(A)`. -/
example {α : ℝ} (hα : 0 < α) (H : Measure X) [IsProbabilityMeasure H] {A : Set X}
    (hA : MeasurableSet A) : blackwellMacQueen α H 1 (Set.univ.pi fun _ ↦ A) = H A := by
  rw [← lintegral_dirichletProcess_prod_of_le_two α hα H (by norm_num) _ fun _ ↦ hA]
  simpa using lintegral_dirichletProcess_apply α hα H hA

/-- Exchangeability for two draws: `P(X₀ ∈ A, X₁ ∈ B) = P(X₀ ∈ B, X₁ ∈ A)`. -/
example {α : ℝ} (hα : 0 < α) (H : Measure X) [IsProbabilityMeasure H] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    blackwellMacQueen α H 2 (Set.univ.pi ![A, B]) =
      blackwellMacQueen α H 2 (Set.univ.pi ![B, A]) := by
  have hpi : MeasurableSet (Set.univ.pi ![A, B]) :=
    MeasurableSet.univ_pi fun i ↦ by fin_cases i <;> simpa
  conv_lhs => rw [← map_perm_blackwellMacQueen α hα H (Equiv.swap 0 1)]
  rw [Measure.map_apply (f := fun xs : Fin 2 → X ↦ xs ∘ ⇑(Equiv.swap (0 : Fin 2) 1))
    (measurable_pi_iff.2 fun i ↦ measurable_pi_apply _) hpi]
  congr 1
  ext xs
  simp [Fin.forall_fin_two, and_comm]

/-- The predictive rule for the second draw. -/
example (α : ℝ) (H : Measure X) [IsProbabilityMeasure H] (A : Fin 2 → Set X)
    (hA : ∀ i, MeasurableSet (A i)) :
    blackwellMacQueen α H 2 (Set.univ.pi A) =
      ∫⁻ xs in Set.univ.pi fun i : Fin 1 ↦ A i.castSucc,
        polyaUrnPredictive α H xs (A 1) ∂blackwellMacQueen α H 1 :=
  blackwellMacQueen_succ_pi α H A hA

/-- Non-vacuity: the urn law is a probability measure for every `α > 0`. -/
example : IsProbabilityMeasure (blackwellMacQueen 1 (Measure.dirac true) 3) :=
  isProbabilityMeasure_blackwellMacQueen one_pos _ 3

/-- Junk value outside the domain: for `α = 0` the first predictive law is
`(0 + 0)⁻¹ • (0 • H) = ∞ • 0 = 0`, so the "urn law" of one draw is the zero measure. -/
example (H : Measure X) : blackwellMacQueen 0 H 1 = 0 := by
  simp [blackwellMacQueen, polyaUrnPredictive]

/-- An atomless base law: the uniform law on `[0, 1]`. -/
noncomputable def unif : Measure ℝ :=
  volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure unif :=
  ⟨by simp [unif, Real.volume_Icc]⟩

/-- The uniform law on `[0, 1]` has no atoms. -/
theorem unif_singleton (x : ℝ) : unif {x} = 0 := by
  rw [unif, Measure.restrict_apply (measurableSet_singleton x)]
  exact measure_mono_null Set.inter_subset_left (measure_singleton x)

/-- The partition of `Fin 2` with a single block. -/
def oneBlock : Finpartition (univ : Finset (Fin 2)) :=
  Finpartition.indiscrete univ_nonempty.ne_empty

/-- Two draws from an atomless base law coincide with probability `1 / (α + 1)`: the second
customer of the Chinese restaurant joins the first one's table. -/
example {α : ℝ} (hα : 0 < α) :
    blackwellMacQueen α unif 2 {xs | tiePartition xs = oneBlock} =
      ENNReal.ofReal (1 / (α + 1)) := by
  rw [blackwellMacQueen_tiePartition α hα unif unif_singleton]
  congr 1
  have hparts : oneBlock.parts = {univ} := rfl
  simp only [crpProb, Finpartition.cardProd, hparts, card_singleton, prod_singleton, card_univ,
    Fintype.card_fin]
  rw [show (2 : ℕ) = 1 + 1 from rfl, ascPochhammer_succ_eval]
  simp
  field_simp

#print axioms map_perm_blackwellMacQueen
#print axioms blackwellMacQueen_tiePartition
#print axioms lintegral_dirichletProcess_prod_of_le_two
#print axioms blackwellMacQueen_succ_pi

end MathlibExtTest.Probability.BlackwellMacQueen
