/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.MutualInformationDPI

@[expose] public section

/-!
# Tests for the data-processing inequality for mutual information

* Non-vacuity: the Markov-kernel hypothesis is met by a deterministic channel (`Bool.not`), a
  constant channel and a genuinely random channel (a binary symmetric channel).
* `I(X; g(Y)) ≤ I(X; Y)` instantiated with a non-injective `g`.
* The constant channel destroys all information: `I(X; Z) = 0`.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MathlibExtTest.InformationTheory.MutualInformationDPI

/-- Two copies of a fair bit, as a probability measure on `Bool × Bool`. -/
noncomputable def copy : ProbabilityMeasure (Bool × Bool) :=
  ⟨(1 / 2 : ℝ≥0∞) • Measure.dirac (true, true) + (1 / 2 : ℝ≥0∞) • Measure.dirac (false, false),
    ⟨by simp [ENNReal.inv_two_add_inv_two]⟩⟩

/-- A binary symmetric channel that flips its input with probability `1/4`. -/
noncomputable def bsc : Kernel Bool Bool where
  toFun b := (3 / 4 : ℝ≥0∞) • Measure.dirac b + (1 / 4 : ℝ≥0∞) • Measure.dirac (!b)
  measurable' := measurable_of_countable _

instance : IsMarkovKernel bsc := ⟨fun b ↦ ⟨by
  simp only [bsc, Kernel.coe_mk, Measure.coe_add, Measure.coe_smul, Pi.add_apply,
    Pi.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.div_add_div_same, show (3 : ℝ≥0∞) + 1 = 4 by norm_num,
    ENNReal.div_self (by norm_num) (by norm_num)]⟩⟩

/-- Passing `Y` through a noisy channel cannot increase information about `X`. -/
example :
    measureMutualInformation
        (⟨(Kernel.id ∥ₖ bsc) ∘ₘ (copy : Measure (Bool × Bool)), inferInstance⟩ :
          ProbabilityMeasure (Bool × Bool)) ≤ measureMutualInformation copy :=
  measureMutualInformation_comp_le copy bsc

/-- A deterministic channel is a Markov kernel too. -/
example :
    measureMutualInformation
        (⟨(Kernel.id ∥ₖ Kernel.deterministic (fun b : Bool ↦ !b) (measurable_of_countable _)) ∘ₘ
          (copy : Measure (Bool × Bool)), inferInstance⟩ :
          ProbabilityMeasure (Bool × Bool)) ≤ measureMutualInformation copy :=
  measureMutualInformation_comp_le copy _

/-- A non-injective post-processing `g = fun _ ↦ ()`. -/
example : measureMutualInformation (copy.map (Prod.map id fun _ : Bool ↦ ())) ≤
    measureMutualInformation copy :=
  measureMutualInformation_map_le copy measurable_const

/-- Symmetry, instantiated. -/
example : measureMutualInformation (copy.map Prod.swap) = measureMutualInformation copy :=
  measureMutualInformation_map_swap copy

/-- A one-point output carries no information. -/
theorem measureMutualInformation_unit (μ : ProbabilityMeasure (Bool × Unit)) :
    measureMutualInformation μ = 0 := by
  unfold measureMutualInformation
  set m : Measure (Bool × Unit) := (μ : Measure (Bool × Unit))
  have h : (m.map Prod.fst).prod (m.map Prod.snd) = m := by
    refine Measure.prod_eq fun s t hs ht ↦ ?_
    rcases Set.eq_empty_or_nonempty t with rfl | ⟨u, hu⟩
    · simp
    · have : t = Set.univ := Set.eq_univ_of_forall fun v ↦ Subsingleton.elim u v ▸ hu
      subst this
      rw [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ, measure_univ,
        mul_one, Measure.map_apply measurable_fst hs, Set.prod_univ]
  rw [h, klDiv_self, ENNReal.zero_div]

/-- A constant channel leaves no information about `X`. -/
example : measureMutualInformation
    (⟨(Kernel.id ∥ₖ Kernel.const Bool (Measure.dirac ())) ∘ₘ (copy : Measure (Bool × Bool)),
      inferInstance⟩ : ProbabilityMeasure (Bool × Unit)) = 0 :=
  measureMutualInformation_unit _

end MathlibExtTest.InformationTheory.MutualInformationDPI
