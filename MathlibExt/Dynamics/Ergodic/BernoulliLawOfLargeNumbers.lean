/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.BernoulliShift
public import MathlibExt.Dynamics.Ergodic.Birkhoff

/-!
# The ergodic theorem as a law of large numbers

For the Bernoulli shift, Birkhoff averages of a function of the first coordinate are the
empirical means of an i.i.d. sequence. Since Bernoulli shifts are ergodic, the Birkhoff
pointwise ergodic theorem yields the strong law of large numbers for i.i.d. sequences: this is
the sense in which the ergodic theorem is a law of large numbers for stationary processes.
Pinned Mathlib proves the strong law directly (`ProbabilityTheory.strong_law_ae`, Etemadi's
theorem); this module records the dynamical route.

## Main results

* `tendsto_average_coordinates_ae`: for `p^ℕ`-almost every sequence `x`,
  `(1/n) ∑_{k<n} g (x k) → ∫ g dp` for every `p`-integrable `g : S → ℝ`.

## References

* S. Lalley, *Birkhoff's ergodic theorem*, lecture notes for Statistics 381, University of
  Chicago, https://galton.uchicago.edu/~lalley/Courses/381/Birkhoff.pdf, introduction: the
  ergodic theorems of Birkhoff and Kingman "extend the validity of the strong law to stationary
  sequences".
* O. Sarig, *Lecture Notes on Ergodic Theory*, Proposition 1.7 (Bernoulli schemes are mixing,
  whence ergodic).
* The point of view is that of L. B. Koralov and Ya. G. Sinai, *Theory of Probability and Random
  Processes*, 2nd ed., Springer (2007), Chapter 16 (stationary processes, the Birkhoff ergodic
  theorem, ergodicity and mixing), cited from its table of contents.
-/

@[expose] public section

namespace MathlibExt.Dynamics.Ergodic.BernoulliLawOfLargeNumbers

open MeasureTheory Filter Topology
open MathlibExt.Dynamics.Ergodic.BernoulliShift

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
/-- **Birkhoff averages along the Bernoulli shift are empirical means.** For `g : S → ℝ`, the
Birkhoff average of `g ∘ (x ↦ x 0)` along the shift at a sequence `x` is
`(1/n) ∑_{k<n} g (x k)`. -/
theorem birkhoffAverage_shift_eval_zero (g : S → ℝ) (n : ℕ) (x : ℕ → S) :
    birkhoffAverage ℝ shift (fun y : ℕ → S => g (y 0)) n x =
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (x k) := by
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, shift_iterate_apply, zero_add]

/-- **Strong law of large numbers from the ergodic theorem.** Let `(S, p)` be a probability
space and `g : S → ℝ` be `p`-integrable. For `p^ℕ`-almost every sequence `x = (x 0, x 1, …)`,
the empirical means `(1/n) ∑_{k<n} g (x k)` converge to `∫ g dp`. The proof applies the Birkhoff
pointwise ergodic theorem to `g ∘ (x ↦ x 0)` and the Bernoulli shift, which is ergodic because
it is mixing (O. Sarig, *Lecture Notes on Ergodic Theory*, Proposition 1.7). That the ergodic
theorem extends the strong law to stationary sequences is the remark opening S. Lalley's notes
*Birkhoff's ergodic theorem* (University of Chicago, Statistics 381). -/
theorem tendsto_average_coordinates_ae (p : Measure S) [IsProbabilityMeasure p] {g : S → ℝ}
    (hg : Integrable g p) :
    ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => p),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (x k)) atTop
        (𝓝 (∫ s, g s ∂p)) := by
  have he := measurePreserving_eval_infinitePi (μ := fun _ : ℕ => p) 0
  have hG : Integrable (fun y : ℕ → S => g (y 0)) (Measure.infinitePi fun _ : ℕ => p) :=
    (he.integrable_comp hg.aestronglyMeasurable).2 hg
  have hint : ∫ y, g (y 0) ∂(Measure.infinitePi fun _ : ℕ => p) = ∫ s, g s ∂p := by
    have hm : AEStronglyMeasurable g
        (Measure.map (Function.eval 0) (Measure.infinitePi fun _ : ℕ => p)) := by
      rw [he.map_eq]; exact hg.aestronglyMeasurable
    have h := integral_map he.measurable.aemeasurable hm
    rw [he.map_eq] at h
    exact h.symm
  filter_upwards [BirkhoffWanted.birkhoff_pointwise_ergodic (ergodic_shift p) hG] with x hx
  rw [← hint]
  refine hx.congr fun n => ?_
  exact birkhoffAverage_shift_eval_zero g n x

end MathlibExt.Dynamics.Ergodic.BernoulliLawOfLargeNumbers
