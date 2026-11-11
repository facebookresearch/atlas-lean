/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Poisson moments, finite Poisson additivity, and Poisson kernels

Complements to Mathlib's `poissonMeasure`:

* `integral_natCast_poissonMeasure`, `integral_natCast_sq_poissonMeasure`,
  `variance_natCast_poissonMeasure`: a Poisson count with mean `r` has mean `r`, second
  moment `r + r²`, and variance `r`;
* `poissonMeasure_zero`: `Po(0)` is the point mass at `0`;
* `iIndepFun.hasLaw_sum_poissonMeasure`: a finite sum of independent Poisson counts is Poisson
  with the summed mean (iterating Mathlib's two-term `IndepFun.hasLaw_add_poissonMeasure`);
* `poissonMeasureKernel`, `piPoissonKernel`: `r ↦ Po(r)` and `r ↦ ∏ᵢ Po(rᵢ)` as Markov kernels.
-/

@[expose] public section

open MeasureTheory Real Finset
open scoped NNReal Nat

namespace ProbabilityTheory

/-! ### Moments -/

/-- The Poisson masses weighted by `n` sum to `r`. -/
private lemma hasSum_mul_poisson (r : ℝ≥0) :
    HasSum (fun n : ℕ => exp (-r) * r ^ n / (n)! * (n : ℝ)) r := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  have h := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  rw [mul_one] at h
  convert h using 1
  funext k
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The Poisson masses weighted by `n²` sum to `r + r²`. -/
private lemma hasSum_sq_poisson (r : ℝ≥0) :
    HasSum (fun n : ℕ => exp (-r) * r ^ n / (n)! * (n : ℝ) ^ 2) (r + r ^ 2) := by
  have h2 : HasSum (fun n : ℕ => exp (-r) * r ^ n / (n)! * ((n : ℝ) * ((n : ℝ) - 1)))
      ((r : ℝ) ^ 2) := by
    rw [← hasSum_nat_add_iff' 2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      zero_mul, sub_self, mul_zero, zero_add, sub_zero]
    have h := (hasSum_one_poissonMeasure r).mul_left ((r : ℝ) ^ 2)
    rw [mul_one] at h
    convert h using 1
    funext k
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  convert (hasSum_mul_poisson r).add h2 using 1
  funext n
  ring

/-- A Poisson count, cast to `ℝ`, is integrable. -/
theorem integrable_natCast_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa using (hasSum_mul_poisson r).summable

/-- The mean of `Po(r)` is `r`. -/
theorem integral_natCast_poissonMeasure (r : ℝ≥0) :
    ∫ n, (n : ℝ) ∂(poissonMeasure r) = r := by
  rw [integral_poissonMeasure' (integrable_natCast_poissonMeasure r)]
  simpa [smul_eq_mul] using (hasSum_mul_poisson r).tsum_eq

/-- The square of a Poisson count is integrable. -/
theorem integrable_natCast_sq_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa using (hasSum_sq_poisson r).summable

/-- The second moment of `Po(r)` is `r + r²`. -/
theorem integral_natCast_sq_poissonMeasure (r : ℝ≥0) :
    ∫ n, (n : ℝ) ^ 2 ∂(poissonMeasure r) = r + r ^ 2 := by
  rw [integral_poissonMeasure' (integrable_natCast_sq_poissonMeasure r)]
  simpa [smul_eq_mul] using (hasSum_sq_poisson r).tsum_eq

/-- The variance of `Po(r)` is `r`. -/
theorem variance_natCast_poissonMeasure (r : ℝ≥0) :
    Var[fun n : ℕ => (n : ℝ); poissonMeasure r] = r := by
  have hmem : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (integrable_natCast_sq_poissonMeasure r)
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply]
  rw [integral_natCast_sq_poissonMeasure, integral_natCast_poissonMeasure]
  ring

/-! ### Finite sums of independent Poisson counts -/

/-- `Po(0)` is the point mass at `0`. -/
theorem poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  refine Measure.ext_iff_singleton.2 fun n => ?_
  rw [poissonMeasure_singleton]
  rcases n with _ | n <;> simp

/-- **Finite Poisson additivity**: a finite sum of independent Poisson counts with means `r i`
is Poisson with mean `∑ r i`. -/
theorem iIndepFun.hasLaw_sum_poissonMeasure {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → ℕ} {r : ι → ℝ≥0}
    (hind : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (poissonMeasure (r i)) P) (s : Finset ι) :
    HasLaw (∑ i ∈ s, X i) (poissonMeasure (∑ i ∈ s, r i)) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, poissonMeasure_zero]
    exact ⟨aemeasurable_const, by
      change P.map (fun _ => 0) = _
      simp [Measure.map_const]⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm (X a), add_comm (r a)]
    exact (hind.indepFun_finsetSum_of_notMem₀ (fun i => (hX i).aemeasurable) ha)
      |>.hasLaw_add_poissonMeasure ih (hX a)

/-! ### Poisson kernels -/

/-- A family of measures on a countable space with measurable singletons is measurable as soon
as each singleton mass is. -/
private lemma measurable_measure_of_singleton {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β] {κ : α → Measure β}
    (h : ∀ b, Measurable fun a => κ a {b}) : Measurable κ := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hκ : (fun a => κ a s) = fun a => ∑' b, s.indicator (fun b => κ a {b}) b :=
    funext fun a => (Measure.tsum_indicator_apply_singleton _ s hs).symm
  rw [hκ]
  refine Measurable.tsum fun b => ?_
  by_cases hb : b ∈ s
  · simpa [Set.indicator_of_mem hb] using h b
  · simp [Set.indicator_of_notMem hb]

/-- The Poisson law depends measurably on its mean. -/
theorem measurable_poissonMeasure : Measurable poissonMeasure :=
  measurable_measure_of_singleton fun n => by
    simp_rw [poissonMeasure_singleton]
    fun_prop

/-- A product of Poisson laws depends measurably on the vector of means. -/
theorem measurable_pi_poissonMeasure {ι : Type*} [Fintype ι] :
    Measurable fun r : ι → ℝ≥0 => Measure.pi fun i => poissonMeasure (r i) :=
  measurable_measure_of_singleton fun b => by
    simp_rw [Measure.pi_singleton]
    exact Finset.measurable_prod _ fun i _ =>
      (Measure.measurable_coe (measurableSet_singleton _)).comp
        (measurable_poissonMeasure.comp (measurable_pi_apply i))

/-- The Poisson kernel `r ↦ Po(r)`. -/
noncomputable def poissonMeasureKernel : Kernel ℝ≥0 ℕ :=
  ⟨poissonMeasure, measurable_poissonMeasure⟩

@[simp]
theorem poissonMeasureKernel_apply (r : ℝ≥0) : poissonMeasureKernel r = poissonMeasure r := rfl

instance : IsMarkovKernel poissonMeasureKernel :=
  ⟨fun r => by rw [poissonMeasureKernel_apply]; infer_instance⟩

/-- The kernel `r ↦ ∏ᵢ Po(rᵢ)` of independent Poisson counts with means `r i`. -/
noncomputable def piPoissonKernel (ι : Type*) [Fintype ι] : Kernel (ι → ℝ≥0) (ι → ℕ) :=
  ⟨fun r => Measure.pi fun i => poissonMeasure (r i), measurable_pi_poissonMeasure⟩

@[simp]
theorem piPoissonKernel_apply {ι : Type*} [Fintype ι] (r : ι → ℝ≥0) :
    piPoissonKernel ι r = Measure.pi fun i => poissonMeasure (r i) := rfl

instance {ι : Type*} [Fintype ι] : IsMarkovKernel (piPoissonKernel ι) :=
  ⟨fun r => by rw [piPoissonKernel_apply]; infer_instance⟩

/-- Under `∏ᵢ Po(rᵢ)`, the total count is `Po(∑ rᵢ)`. -/
theorem map_sum_pi_poissonMeasure {ι : Type*} [Fintype ι] (r : ι → ℝ≥0) :
    (Measure.pi fun i => poissonMeasure (r i)).map (fun N : ι → ℕ => ∑ i, N i) =
      poissonMeasure (∑ i, r i) := by
  have hind := iIndepFun_pi (μ := fun i => poissonMeasure (r i)) (X := fun _ => id)
    (fun _ => aemeasurable_id)
  have h := iIndepFun.hasLaw_sum_poissonMeasure hind
    (fun i => (measurePreserving_eval (fun i => poissonMeasure (r i)) i).hasLaw) Finset.univ
  have hfun : (∑ i, fun N : ι → ℕ => id (N i)) = fun N => ∑ i, N i := by
    funext N
    simp
  rw [hfun] at h
  exact h.map_eq

/-- Summing independent Poisson counts turns `piPoissonKernel` into the Poisson kernel at the
summed mean. -/
theorem piPoissonKernel_map_sum {ι : Type*} [Fintype ι] :
    (piPoissonKernel ι).map (fun N : ι → ℕ => ∑ i, N i) =
      poissonMeasureKernel.comap (fun r : ι → ℝ≥0 => ∑ i, r i) (by fun_prop) := by
  ext1 r
  rw [Kernel.map_apply _ (by fun_prop), Kernel.comap_apply, piPoissonKernel_apply,
    poissonMeasureKernel_apply, map_sum_pi_poissonMeasure]

end ProbabilityTheory
