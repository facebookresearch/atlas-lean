/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Finite sums of independent Poisson variables

Mathlib proves that the sum of two independent Poisson random variables is Poisson
(`ProbabilityTheory.IndepFun.hasLaw_add_poissonMeasure`). This file extends it to finitely many
summands: if `K_i`, `i ∈ s`, are mutually independent with `K_i ~ Poisson(λ_i)`, then
`∑_{i ∈ s} K_i ~ Poisson(∑_{i ∈ s} λ_i)`, the fact Griffiths and Ghahramani (*The Indian buffet
process: an introduction and review*, JMLR 12 (2011), Section 4.6) use to show that the number of
features of the Indian buffet process is Poisson.
`MathlibExt.Probability.Distributions.PoissonKernel` proves it under a probability measure with
every summand Poisson
(`ProbabilityTheory.iIndepFun.hasLaw_sum_poissonMeasure`); this variant asks for the laws only on a
nonempty `s`, and no normalisation.

Main result:

* `ProbabilityTheory.iIndepFun.hasLaw_sum_poissonMeasure_of_nonempty`.
-/

@[expose] public section

set_option autoImplicit false

namespace ProbabilityTheory

open MeasureTheory Finset
open scoped NNReal

/-- **Finite sums of independent Poisson variables are Poisson.** If the random variables `K_i`
are mutually independent and `K_i ~ Poisson(λ_i)` for `i ∈ s`, then
`∑_{i ∈ s} K_i ~ Poisson(∑_{i ∈ s} λ_i)` for every nonempty finite set `s` (stated in Griffiths
and Ghahramani 2011, Section 4.6); this extends Mathlib's two-variable
`IndepFun.hasLaw_add_poissonMeasure` by induction on `s`. -/
theorem iIndepFun.hasLaw_sum_poissonMeasure_of_nonempty {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {K : ι → Ω → ℕ} (hind : iIndepFun K P) (hmeas : ∀ i, Measurable (K i))
    {rate : ι → ℝ≥0} {s : Finset ι} (hlaw : ∀ i ∈ s, HasLaw (K i) Po(rate i) P)
    (hs : s.Nonempty) :
    HasLaw (∑ i ∈ s, K i) Po(∑ i ∈ s, rate i) P := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hlaw a (mem_singleton_self a)
  | cons a s ha hs ih =>
    rw [sum_cons, sum_cons]
    exact (hind.indepFun_finsetSum_of_notMem hmeas ha).symm.hasLaw_add_poissonMeasure
      (hlaw a (mem_cons_self a s)) (ih fun i hi => hlaw i (mem_cons_of_mem hi))

end ProbabilityTheory
