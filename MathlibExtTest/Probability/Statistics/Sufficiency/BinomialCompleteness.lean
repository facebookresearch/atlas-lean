/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.BinomialCompleteness
public import MathlibExt.Probability.Statistics.Sufficiency.Complete

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Sufficiency.BinomialCompleteness

open MeasureTheory

/-- Fixture A (through the main theorem): the `n = 1` case recovers uniqueness for the

Bernoulli family. -/

example {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)

    (g h : ℕ → ℝ) (hg : Measurable g) (hh : Measurable h)

    (P : Set.Ioo a b → ProbabilityMeasure ℕ)

    (hP : ∀ p, (P p : Measure ℕ) = ProbabilityTheory.binomial 1 ⟨p.val, by

      constructor

      · exact le_trans ha.le p.property.1.le

      · exact le_trans p.property.2.le hb.le⟩)

    (hgi : ∀ p, Integrable (fun ω => g ((id : ℕ → ℕ) ω)) ((P p) : Measure ℕ))

    (hhi : ∀ p, Integrable (fun ω => h ((id : ℕ → ℕ) ω)) ((P p) : Measure ℕ))

    (hgh : ∀ p, ∫ ω, g ((id : ℕ → ℕ) ω) ∂((P p) : Measure ℕ) =

      ∫ ω, h ((id : ℕ → ℕ) ω) ∂((P p) : Measure ℕ)) :

    ∀ p, (fun ω => g ((id : ℕ → ℕ) ω)) =ᵐ[((P p) : Measure ℕ)]

      fun ω => h ((id : ℕ → ℕ) ω) := by

  have hC := MathlibExt.Probability.Statistics.Sufficiency.isCompleteStatistic_binomial_count

    1 le_rfl ha hab hb

  have hFeq : P = fun p : Set.Ioo a b =>

      (⟨ProbabilityTheory.binomial 1 ⟨p.val, by

        constructor

        · exact le_trans ha.le p.property.1.le

        · exact le_trans p.property.2.le hb.le⟩,

      by infer_instance⟩ : ProbabilityMeasure ℕ) := by

    funext p

    apply Subtype.ext

    exact hP p

  subst hFeq

  exact hC.ae_eq_of_integral_eq hg hh hgi hhi hgh

/-- Fixture B witness: `(1, -1, 1)` on `{0, 1, 2}` (the `![1, -1, 1]` values on the

support), zero elsewhere. -/

private def fixtureBfun : ℕ → ℝ := fun k =>

  if k = 0 then 1 else if k = 1 then -1 else if k = 2 then 1 else 0

/-- Fixture B (boundary): a singleton parameter set does not determine the coefficients —

for `Bin(2, 1/2)` the nonzero `u = ![1, -1, 1]` has mean zero, so the one-point family is

not complete. -/

example :

    ¬ MathlibExt.Probability.Statistics.Sufficiency.IsCompleteStatistic

      (fun _ : Unit => ⟨ProbabilityTheory.binomial 2 ⟨(1 / 2 : ℝ), by norm_num⟩,

        by infer_instance⟩)

      (id : ℕ → ℕ) := by

  rintro ⟨-, hcomp⟩

  have hu0 : fixtureBfun 0 = 1 := by simp [fixtureBfun]

  have hu1 : fixtureBfun 1 = -1 := by simp [fixtureBfun, show (1:ℕ) ≠ 0 from one_ne_zero]

  have hu2 : fixtureBfun 2 = 1 := by

    simp [fixtureBfun, show (2:ℕ) ≠ 0 from ne_of_beq_false rfl,

      show (2:ℕ) ≠ 1 from ne_of_beq_false rfl]

  have hIic : Finset.Iic 2 = ({0, 1, 2} : Finset ℕ) := by

    ext k

    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_singleton]

    omega

  have hzero : ∀ θ : Unit, ∫ ω, fixtureBfun ((id : ℕ → ℕ) ω)

      ∂(((fun _ : Unit => (⟨ProbabilityTheory.binomial 2 ⟨(1 / 2 : ℝ), by norm_num⟩,

        by infer_instance⟩ : ProbabilityMeasure ℕ)) θ) : Measure ℕ) = 0 := by

    intro θ

    change ∫ ω, fixtureBfun (id ω) ∂(ProbabilityTheory.binomial 2 ⟨(1/2:ℝ), _⟩) = 0

    rw [ProbabilityTheory.integral_binomial, hIic,

      Finset.sum_insert (by decide : (0:ℕ) ∉ ({1, 2} : Finset ℕ)),

      Finset.sum_insert (by decide : (1:ℕ) ∉ ({2} : Finset ℕ)),

      Finset.sum_singleton]

    show ((Nat.choose 2 0 : ℝ) * (1/2:ℝ)^0 * (1-1/2)^2) * fixtureBfun 0

      + (((Nat.choose 2 1 : ℝ) * (1/2:ℝ)^1 * (1-1/2)^1) * fixtureBfun 1

      + ((Nat.choose 2 2 : ℝ) * (1/2:ℝ)^2 * (1-1/2)^0) * fixtureBfun 2) = 0

    rw [hu0, hu1, hu2, Nat.choose_zero_right, Nat.choose_self,

      show Nat.choose 2 1 = 2 from rfl]

    norm_num

  have hae := hcomp fixtureBfun Measurable.of_discrete

    (fun _ => ProbabilityTheory.integrable_binomial _) hzero ()

  have hmem : ∀ᵐ k ∂(ProbabilityTheory.binomial 2 ⟨(1/2:ℝ), by norm_num⟩),

      fixtureBfun k = 0 := hae

  have hnull : (ProbabilityTheory.binomial 2 ⟨(1/2:ℝ), by norm_num⟩)

      {k | fixtureBfun k ≠ 0} = 0 :=

    mem_ae_iff.mp hmem

  have hsub : ({0} : Set ℕ) ⊆ {k | fixtureBfun k ≠ 0} := by

    intro k hk

    simp only [Set.mem_singleton_iff] at hk

    subst hk

    simp only [Set.mem_ofPred_eq]

    rw [hu0]

    exact one_ne_zero

  have hmass : (ProbabilityTheory.binomial 2 ⟨(1/2:ℝ), by norm_num⟩) {0} ≠ 0 := by

    have hcoe : ((⟨(1/2:ℝ), by norm_num⟩ : ↥unitInterval) : ℝ) = 1/2 := rfl

    rw [ProbabilityTheory.binomial_singleton, hcoe, Nat.choose_zero_right,

      ne_eq, ENNReal.ofReal_eq_zero]

    norm_num

  exact hmass (measure_mono_null hsub hnull)

/-- Fixture C (a.e. subtlety): a function vanishing on `{0, …, n}` is a.e. zero under

every `Bin(n,p)` law (values above `n` are arbitrary) — this is consistent with

completeness, not a counterexample. The stated hypothesis is exact: only vanishing on

`{k | k ≤ n}` is required. -/

example (n : ℕ) (p : ↥unitInterval)

    (u : ℕ → ℝ) (hu : ∀ k, k ≤ n → u k = 0) :

    u =ᵐ[ProbabilityTheory.binomial n p] 0 := by

  exact MathlibExt.Probability.Statistics.Sufficiency.binomial_ae_eq_zero_of_eq_zero_on_Iic

    n p u hu

end MathlibExtTest.Probability.Statistics.Sufficiency.BinomialCompleteness
