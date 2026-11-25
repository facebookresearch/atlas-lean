/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Conditional expectation of a function of a finite-valued random variable

On a finite measure space, let `m` be a sub-σ-algebra and `Y` a random variable with finitely
many values and measurable level sets. If, for every value `a`, `g a` is a bounded strongly
`m`-measurable function, then the conditional expectation of `ω ↦ g (Y ω) ω` given `m` is
`∑ₐ g a · μ[1_{Y = a} | m]`: the coefficients `g a`, known given `m`, come out of the conditional
expectation, and only the conditional probabilities of the values of `Y` remain.

## Main results

* `condExp_comp_eq_sum`: `μ[g Y | m] = ∑ₐ g a · μ[1_{Y = a} | m]` almost everywhere.

A typical use is a process whose next value has a known conditional law given its past: the
conditional expectation of any bounded function of the next value and of the past is then a
finite sum against that law.
-/

@[expose] public section

namespace MeasureTheory

variable {Ω α : Type*} [Fintype α] {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ]

/-- **Conditional expectation of a function of a finite-valued random variable.** Let `μ` be a
finite measure on `Ω`, `m ≤ mΩ` a sub-σ-algebra, `Y : Ω → α` a random variable with values in a
finite type and measurable level sets `{Y = a}`, and, for every value `a`, `g a : Ω → ℝ` a
strongly `m`-measurable function bounded by `K`. Then almost everywhere
`μ[ω ↦ g (Y ω) ω | m] = ∑ₐ g a · μ[1_{Y = a} | m]`; for a probability measure `μ[1_{Y = a} | m]`
is the conditional probability `P(Y = a | m)`. -/
theorem condExp_comp_eq_sum (hm : m ≤ mΩ) {Y : Ω → α}
    (hY : ∀ a, MeasurableSet {ω | Y ω = a}) {g : α → Ω → ℝ} {K : ℝ}
    (hg : ∀ a, StronglyMeasurable[m] (g a)) (hgK : ∀ a ω, |g a ω| ≤ K) :
    μ[fun ω => g (Y ω) ω | m] =ᵐ[μ]
      fun ω => ∑ a, g a ω * μ[{ω | Y ω = a}.indicator (fun _ => (1 : ℝ)) | m] ω := by
  classical
  set I : α → Ω → ℝ := fun a => {ω | Y ω = a}.indicator (fun _ => (1 : ℝ)) with hIdef
  have hI : ∀ a, Integrable (I a) μ := fun a => (integrable_const (1 : ℝ)).indicator (hY a)
  have hI1 : ∀ a ω, |I a ω| ≤ 1 := fun a ω => by
    simp only [hIdef, Set.indicator_apply]
    split_ifs <;> simp
  have hsum : (fun ω => g (Y ω) ω) = ∑ a, g a * I a := by
    ext ω
    simp only [Finset.sum_apply, Pi.mul_apply, hIdef, Set.indicator_apply, Set.mem_ofPred_eq,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hint : ∀ a ∈ (Finset.univ : Finset α), Integrable (g a * I a) μ := fun a _ =>
    Integrable.of_bound (((hg a).mono hm).aestronglyMeasurable.mul (hI a).aestronglyMeasurable) K
      (ae_of_all _ fun ω => by
        rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact (mul_le_of_le_one_right (abs_nonneg _) (hI1 a ω)).trans (hgK a ω))
  have h2 : ∀ᵐ ω ∂μ, ∀ a, μ[g a * I a | m] ω = g a ω * μ[I a | m] ω :=
    ae_all_iff.2 fun a => (condExp_stronglyMeasurable_mul_of_bound hm (hg a) (hI a) K
      (ae_of_all _ fun ω => (Real.norm_eq_abs _).le.trans (hgK a ω))).mono fun ω h => by
        simpa using h
  rw [hsum]
  filter_upwards [condExp_finsetSum hint m, h2] with ω h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => h2 a

end MeasureTheory
