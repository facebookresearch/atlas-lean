/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Poisson count splitting

First sample a Poisson total, then a binomial count conditional on that total, and take the
remainder. The two resulting counts have independent Poisson laws. For a finite array,
independent sampling of the entrywise pairs gives independent arrays of first and second counts.

Source: Neufeld et al., *Inference after latent variable estimation for single-cell RNA
sequencing data*, §4.1, Algorithm 1 and Proposition 1. This file proves only the forward sampling
law, not the converse characterization or calibration of a downstream test.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory unitInterval

namespace ProbabilityTheory

/-- The joint law from sampling a Poisson total, drawing a binomial first part conditional on
it, and returning the first part and the difference. The binomial law is supported within the
total, so natural subtraction does not truncate a positive-mass outcome. -/
noncomputable def poissonBinomialSplit (rate : ℝ≥0) (p : I) : Measure (ℕ × ℕ) :=
  ((poissonMeasure rate).compProd (Kernel.ofFunOfCountable (fun n => binomial n p))).map
    (fun nk : ℕ × ℕ => (nk.2, nk.1 - nk.2))

private theorem split_section (p : I) (a b n : ℕ) :
    binomial n p ((fun k : ℕ => (k, n - k)) ⁻¹' {(a, b)}) =
      if n = a + b then binomial n p {a} else 0 := by
  by_cases hn : n = a + b
  · subst n
    have he : (fun k : ℕ => (k, a + b - k)) ⁻¹' {(a, b)} = {a} := by
      ext k
      simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, and_iff_left_iff_imp]
      rintro rfl
      omega
    rw [he, ite_eq_left rfl]
  · rw [ite_eq_right hn]
    by_cases ha : a ≤ n
    · have he : (fun k : ℕ => (k, n - k)) ⁻¹' {(a, b)} = ∅ := by
        ext k
        simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, mem_empty_iff_false, iff_false]
        rintro ⟨rfl, hb⟩
        omega
      rw [he, measure_empty]
    · apply nonpos_iff_eq_zero.mp
      refine (measure_mono (show (fun k : ℕ => (k, n - k)) ⁻¹' {(a, b)} ⊆ {a} from ?_)).trans ?_
      · intro k hk
        exact congrArg Prod.fst (mem_singleton_iff.mp hk)
      · simp [binomial_singleton, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha)]

/-- The split law at `(a,b)` is the Poisson mass at `a+b` times the binomial mass at `a`. -/
theorem poissonBinomialSplit_singleton (rate : ℝ≥0) (p : I) (a b : ℕ) :
    poissonBinomialSplit rate p {(a, b)} =
      poissonMeasure rate {a + b} * binomial (a + b) p {a} := by
  let κ := Kernel.ofFunOfCountable (fun n => binomial n p)
  let _ : IsMarkovKernel κ := ⟨fun n => inferInstanceAs (IsProbabilityMeasure (binomial n p))⟩
  let f : ℕ × ℕ → ℕ × ℕ := fun nk => (nk.2, nk.1 - nk.2)
  have hf : Measurable f := measurable_of_countable f
  change ((poissonMeasure rate).compProd κ).map f {(a, b)} = _
  rw [Measure.map_apply hf (measurableSet_singleton _),
    Measure.compProd_apply (hf (measurableSet_singleton _)), lintegral_countable']
  have h (n : ℕ) : κ n (Prod.mk n ⁻¹' (f ⁻¹' {(a, b)})) =
      if n = a + b then binomial n p {a} else 0 := split_section p a b n
  simp_rw [h]
  rw [tsum_eq_single (a + b)]
  · simp [mul_comm]
  · intro n hn
    simp [hn]

/-- Multiplying the mass of a Poisson total `j + k` by the conditional binomial mass at `k`
gives the product of the Poisson masses at `k` and `j` with the two split rates. -/
theorem poissonMeasure_mul_binomial_singleton (rate : ℝ≥0) (p : I) (j k : ℕ) :
    poissonMeasure rate {j + k} * binomial (j + k) p {k} =
      poissonMeasure (unitInterval.toNNReal p * rate) {k} *
        poissonMeasure (unitInterval.toNNReal (unitInterval.symm p) * rate) {j} := by
  rw [poissonMeasure_singleton, binomial_singleton,
    poissonMeasure_singleton, poissonMeasure_singleton,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_mul, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq,
    Nat.add_sub_cancel_right, pow_add, mul_pow]
  rw [show ((j + k).choose k : ℝ) =
      ((j + k).factorial : ℝ) / ((j.factorial : ℝ) * (k.factorial : ℝ)) by
    apply (eq_div_iff (by positivity : ((j.factorial : ℝ) * (k.factorial : ℝ)) ≠ 0)).2
    exact_mod_cast (by simpa [mul_assoc] using
      Nat.add_choose_mul_factorial_mul_factorial j k)]
  have he : Real.exp (-((p : ℝ) * (rate : ℝ))) *
      Real.exp (-((1 - (p : ℝ)) * (rate : ℝ))) = Real.exp (-(rate : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he]
  field_simp

/-- **Poisson count splitting.** A Poisson count split by binomial sampling has the product law
of two Poisson counts with rates `p * rate` and `(1 - p) * rate`. This includes the endpoint
probabilities and rate zero. -/
theorem poissonBinomialSplit_eq_prod (rate : ℝ≥0) (p : I) :
    poissonBinomialSplit rate p =
      (poissonMeasure (unitInterval.toNNReal p * rate)).prod
        (poissonMeasure (unitInterval.toNNReal (unitInterval.symm p) * rate)) := by
  apply Measure.ext_of_singleton
  intro ⟨a, b⟩
  rw [poissonBinomialSplit_singleton, ← singleton_prod_singleton, Measure.prod_prod]
  simpa only [Nat.add_comm b a] using poissonMeasure_mul_binomial_singleton rate p b a

/-- **Finite-array Poisson count splitting.** Sample pairs independently across a finite array,
using the entrywise conditional binomial split of each Poisson count. The array of first parts
and the array of remainders then have the product of the two respective product Poisson laws.
In particular the arrays are independent, even when the original rates vary by entry. -/
theorem pi_poissonBinomialSplit_eq_prod {ι : Type*} [Fintype ι]
    (rate : ι → ℝ≥0) (p : I) :
    (Measure.pi (fun i => poissonBinomialSplit (rate i) p)).map
        (fun x : ι → ℕ × ℕ => ((fun i => (x i).1), (fun i => (x i).2))) =
      (Measure.pi (fun i => poissonMeasure (unitInterval.toNNReal p * rate i))).prod
        (Measure.pi (fun i =>
          poissonMeasure (unitInterval.toNNReal (unitInterval.symm p) * rate i))) := by
  simp_rw [poissonBinomialSplit_eq_prod]
  exact (measurePreserving_arrowProdEquivProdArrow ℕ ℕ ι
    (fun i => poissonMeasure (unitInterval.toNNReal p * rate i))
    (fun i => poissonMeasure (unitInterval.toNNReal (unitInterval.symm p) * rate i))).map_eq

end ProbabilityTheory
