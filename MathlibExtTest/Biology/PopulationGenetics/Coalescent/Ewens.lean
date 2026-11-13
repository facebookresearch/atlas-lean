/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Ewens
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Tests for the Ewens sampling formula in allele-count form and the coalescent with killing

Samples of three genes: the configurations `(3, 0, 0)`, `(1, 1, 0)` and `(0, 0, 1)` have
probabilities `θ² / ((θ + 1)(θ + 2))`, `3θ / ((θ + 1)(θ + 2))` and `2 / ((θ + 1)(θ + 2))`,
computed from the definition, which sum to one; the configuration of the partition `{2, 1}`;
a configuration with `∑ j a_j ≠ n`; the coalescent with killing for `n = 1` (always one allele)
and `n = 2` (two alleles iff the mutation clock rings first); the clock rates; and the concrete
model, with `E[K_3] = 1 + θ/(θ + 1) + θ/(θ + 2)`.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.Ewens

open MathlibExt.Biology.PopulationGenetics.Ewens
open MathlibExt.Biology.PopulationGenetics.Coalescent

/-- Three singletons: `P(3, 0, 0) = θ² / ((θ + 1)(θ + 2))`, from the definition. -/
example {θ : ℝ} (hθ : 0 < θ) :
    ewensConfigProb θ 3 (fun j ↦ if j = 1 then 3 else 0) = θ ^ 2 / ((θ + 1) * (θ + 2)) := by
  simp [ewensConfigProb, ascPochhammer_succ_eval, Finset.prod_Icc_succ_top, Nat.factorial]
  field_simp

/-- One singleton and one doubleton: `P(1, 1, 0) = 3θ / ((θ + 1)(θ + 2))`. -/
example {θ : ℝ} (hθ : 0 < θ) :
    ewensConfigProb θ 3 (fun j ↦ if j = 1 ∨ j = 2 then 1 else 0) =
      3 * θ / ((θ + 1) * (θ + 2)) := by
  simp [ewensConfigProb, ascPochhammer_succ_eval, Finset.prod_Icc_succ_top, Nat.factorial]
  field_simp
  ring

/-- One allele carried by all three genes: `P(0, 0, 1) = 2 / ((θ + 1)(θ + 2))`. -/
example {θ : ℝ} (hθ : 0 < θ) :
    ewensConfigProb θ 3 (fun j ↦ if j = 3 then 1 else 0) = 2 / ((θ + 1) * (θ + 2)) := by
  simp [ewensConfigProb, ascPochhammer_succ_eval, Finset.prod_Icc_succ_top, Nat.factorial]
  field_simp
  ring

/-- The three configurations of a sample of three genes have probabilities summing to one
(each computed from the definition, not from a normalization theorem). -/
example {θ : ℝ} (hθ : 0 < θ) :
    θ ^ 2 / ((θ + 1) * (θ + 2)) + 3 * θ / ((θ + 1) * (θ + 2)) + 2 / ((θ + 1) * (θ + 2)) = 1 := by
  field_simp
  ring

/-- The allelic partition `{2, 1}` of three genes. -/
def twoOne : Nat.Partition 3 where
  parts := {2, 1}
  parts_pos := by simp
  parts_sum := by simp

/-- Its configuration is `(1, 1, 0)`. -/
example : alleleCount twoOne 1 = 1 ∧ alleleCount twoOne 2 = 1 ∧ alleleCount twoOne 3 = 0 := by
  decide

/-- Its configuration accounts for the three genes, `1·1 + 2·1 + 3·0 = 3`, computed directly. -/
example : ∑ j ∈ Icc 1 3, j * alleleCount twoOne j = 3 := by decide

/-- The partition formula at `{2, 1}` is the configuration formula at `(1, 1, 0)`. -/
example (θ : ℝ) : ewensProb θ twoOne = ewensConfigProb θ 3 (alleleCount twoOne) :=
  ewensProb_eq_ewensConfigProb θ twoOne

open scoped Classical in
/-- The vector `(1, 0, 0)` is not the configuration of a sample of three genes. -/
example (θ : ℝ) :
    ∑ π : Nat.Partition 3 with
      ∀ j ∈ Icc 1 3, alleleCount π j = (fun j ↦ if j = 1 then 1 else 0) j, ewensProb θ π = 0 :=
  sum_ewensProb_alleleCount_eq_zero θ (by decide)

/-- The clock rates, from the definition: the mutation clock at level `2` has rate `θ`, the
coalescence clock at level `3` has rate `3`. -/
example (θ : ℝ) : killingRate 3 θ (.inl ⟨2, by simp⟩) = θ ∧
    killingRate 3 θ (.inr ⟨3, by simp⟩) = 3 := by
  refine ⟨?_, ?_⟩ <;> simp [killingRate, Nat.choose]

section Killing

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {θ : ℝ}

/-- Boundary `n = 1`: a single gene carries exactly one allele, from the definition. -/
example (K : KillingCoalescent μ 1 θ) (ω : Ω) : K.numAlleles ω = 1 := by
  simp [KillingCoalescent.numAlleles]

/-- `n = 2`: the two genes carry two alleles exactly when the mutation clock rings first. -/
example (K : KillingCoalescent μ 2 θ) (ω : Ω) :
    K.numAlleles ω = if K.M 2 ω < K.C 2 ω then 2 else 1 := by
  classical
  unfold KillingCoalescent.numAlleles
  rw [show Icc 2 2 = {2} from rfl, filter_singleton]
  split_ifs <;> simp

end Killing

/-- The concrete model is a probability space. -/
example {θ : ℝ} (hθ : 0 < θ) : IsProbabilityMeasure (killingMeasure 3 θ) :=
  isProbabilityMeasure_killingMeasure 3 hθ

/-- Non-vacuity: in the concrete model, `E[K_3] = 1 + θ/(θ + 1) + θ/(θ + 2)`. -/
example {θ : ℝ} (hθ : 0 < θ) :
    have := isProbabilityMeasure_killingMeasure 3 hθ
    ∫ ω, ((KillingCoalescent.ofPi 3 hθ).numAlleles ω : ℝ) ∂killingMeasure 3 θ =
      1 + θ / (θ + 1) + θ / (θ + 2) := by
  have := isProbabilityMeasure_killingMeasure 3 hθ
  rw [KillingCoalescent.integral_numAlleles _ hθ (by norm_num)]
  simp [sum_range_succ, hθ.ne']

/-- Competing clocks of equal rate ring first with probability `1/2`. -/
example : ((expMeasure 1).prod (expMeasure 1)).real {p : ℝ × ℝ | p.1 < p.2} = 1 / 2 := by
  rw [prod_expMeasure_real_lt one_pos one_pos]
  norm_num

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.Ewens
