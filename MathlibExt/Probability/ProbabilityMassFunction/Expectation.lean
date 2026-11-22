/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.Distributions.Uniform
public import MathlibExt.Probability.ProbabilityMassFunction.Uniform

/-!
# Expectation of a real-valued function under a probability mass function

`PMF.expect p f` is the expected value of a real-valued function `f` under the
probability mass function `p`, defined as the Bochner integral of `f` against
the probability measure `p.toMeasure` associated to `p`.

The definition is bundled with computation lemmas that turn the integral into
an unconditional finite sum on a `Fintype`: `expect_eq_sum` is the workhorse
from which linearity (`expect_add`, `expect_sum`, `expect_const_mul`),
monotonicity (`expect_nonneg`, `expect_le_expect`), the average formula for
the uniform distribution (`expect_uniformOfFintype`), the change-of-variables
formula for `PMF.map` (`expect_map`) and the indicator formula
(`expect_indicator_decide`) are all derived without side conditions.

`PMF.expectENN` is the `ℝ≥0∞`-valued analogue, defined directly as a `tsum`.
It needs no measurability or integrability hypothesis and records a divergent
expectation as `∞`; `expectENN_natCast_toReal` bridges it back to `expect`
for natural-valued observables on finite types.
-/

@[expose] public section

open scoped ENNReal

namespace PMF

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  {p : PMF α} {f g : α → ℝ}

/-- The **expectation** (expected value) of a real-valued function `f` under a
probability mass function `p`: the Bochner integral of `f` against the
probability measure `p.toMeasure` associated to `p`. On a `Fintype` this is
the finite sum `∑ a, (p a).toReal * f a` (see `expect_eq_sum`). As a Bochner
integral it is `0` when `f` is not integrable; nonnegative or natural-valued
observables should use `expectENN`, whose value in `ℝ≥0∞` can be `∞`. -/
noncomputable def expect (p : PMF α) (f : α → ℝ) : ℝ :=
  ∫ a, f a ∂p.toMeasure

/-- The expectation is the `tsum` of the pointwise products, for an
integrable function. This specialises `PMF.integral_eq_tsum` to `ℝ`. -/
theorem expect_eq_tsum (hf : MeasureTheory.Integrable f p.toMeasure) :
    p.expect f = ∑' a, (p a).toReal • f a :=
  integral_eq_tsum p f hf

/-- On a `Fintype` the expectation is an unconditional finite sum. -/
theorem expect_eq_sum [Fintype α] (p : PMF α) (f : α → ℝ) :
    p.expect f = ∑ a, (p a).toReal * f a := by
  rw [expect, integral_eq_sum]
  exact Finset.sum_congr rfl fun a _ => smul_eq_mul _ _

/-- The expectation of a constant function is that constant. -/
theorem expect_const [Fintype α] (p : PMF α) (c : ℝ) :
    p.expect (fun _ => c) = c := by
  have h1 : ∑ a, p a = 1 := (tsum_fintype (fun a => p a)).symm.trans (tsum_coe p)
  have hsum : ∑ a, (p a).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => apply_ne_top p a), h1,
      ENNReal.toReal_one]
  rw [expect_eq_sum, ← Finset.sum_mul, hsum, one_mul]

/-- The expectation under the uniform distribution on a nonempty `Fintype`
is the average of the values. -/
theorem expect_uniformOfFintype [Fintype α] [Nonempty α] (f : α → ℝ) :
    (PMF.uniformFintype α).expect f =
      (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  rw [expect_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [uniformFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- Expectation is additive (finite case, no integrability hypotheses). -/
theorem expect_add [Fintype α] : p.expect (f + g) = p.expect f + p.expect g := by
  rw [expect_eq_sum, expect_eq_sum, expect_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [Pi.add_apply, mul_add]

/-- Expectation commutes with finite sums (finite case). -/
theorem expect_sum [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    p.expect (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, p.expect (f i) := by
  rw [expect_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (expect_eq_sum p (f i)).symm

/-- Expectation pulls out a real scalar multiple (finite case). -/
theorem expect_const_mul [Fintype α] (c : ℝ) (f : α → ℝ) :
    p.expect (fun a => c * f a) = c * p.expect f := by
  rw [expect_eq_sum, expect_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- Expectation pulls out a real scalar multiple, stated with `•`
(finite case). -/
theorem expect_smul [Fintype α] (c : ℝ) (f : α → ℝ) :
    p.expect (c • f) = c * p.expect f := by
  have : (c • f) = fun a => c * f a := funext fun a => smul_eq_mul c (f a)
  rw [this]; exact expect_const_mul c f

/-- The expectation of a nonnegative function is nonnegative (finite case). -/
theorem expect_nonneg [Fintype α] (hf : ∀ a, 0 ≤ f a) : 0 ≤ p.expect f := by
  rw [expect_eq_sum]
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg ENNReal.toReal_nonneg (hf a)

/-- Expectation is monotone in the function (finite case). -/
theorem expect_le_expect [Fintype α] (hfg : ∀ a, f a ≤ g a) :
    p.expect f ≤ p.expect g := by
  rw [expect_eq_sum, expect_eq_sum]
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (hfg a) ENNReal.toReal_nonneg

/-- If all the mass of `p` lies in a finite set `s`, the expectation is the
finite sum over `s`, with no integrability hypothesis and no finiteness
assumption on the ambient type. -/
theorem expect_eq_sum_of_finite_support (s : Finset α)
    (hs : ∀ a ∉ s, p a = 0) (f : α → ℝ) :
    p.expect f = ∑ a ∈ s, (p a).toReal * f a := by
  have hcompl : p.toMeasure (↑s : Set α)ᶜ = 0 := by
    rw [toMeasure_apply_eq_toOuterMeasure_apply _
      (Finset.measurableSet s).compl, toOuterMeasure_apply]
    refine tsum_congr (fun a => ?_) |>.trans tsum_zero
    exact Set.indicator_apply_eq_zero.2 fun ha => hs a (by simpa using ha)
  have hae : ∀ᵐ x ∂p.toMeasure, x ∉ (↑s : Set α) → f x = 0 := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := (↑s : Set α)ᶜ) ?_ hcompl
    intro x hx
    simp only [Set.mem_ofPred_eq, not_imp] at hx
    exact hx.1
  rw [expect, ← MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero hae,
    MeasureTheory.setIntegral_finset s MeasureTheory.IntegrableOn.finset]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [MeasureTheory.measureReal_def,
    PMF.toMeasure_apply_singleton p a (MeasurableSet.singleton a),
    smul_eq_mul]

/-- The expectation of a mapped distribution is the expectation of the
composition (change of variables). The source type is finite; the target
type is arbitrary. -/
theorem expect_map [Fintype α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (g : α → β) (f : β → ℝ) :
    (p.map g).expect f = p.expect (f ∘ g) := by
  classical
  have hmap : ∀ b : β, (p.map g) b =
      ∑ a ∈ Finset.univ.filter (fun a => g a = b), p a := by
    intro b
    rw [map_apply]
    rw [tsum_eq_sum (s := Finset.univ.filter (fun a => g a = b))]
    · exact Finset.sum_congr rfl fun a ha => by
        rw [Finset.mem_filter] at ha
        split_ifs with h
        · rfl
        · exact (h ha.2.symm).elim
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      split_ifs with h
      · exact (ha h.symm).elim
      · rfl
  have hzero : ∀ b ∉ Finset.image g Finset.univ, (p.map g) b = 0 := by
    intro b hb
    rw [hmap b]
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.mem_filter] at ha
    have hbmem : b ∈ Finset.image g Finset.univ :=
      ha.2 ▸ Finset.mem_image_of_mem g ha.1
    exact (hb hbmem).elim
  rw [expect_eq_sum_of_finite_support _ hzero, expect_eq_sum]
  have htoReal : ∀ b : β, ((p.map g) b).toReal * f b =
      ∑ a ∈ Finset.univ.filter (fun a => g a = b), (p a).toReal * f (g a) := by
    intro b
    rw [hmap b, ENNReal.toReal_sum (fun a _ => apply_ne_top p a),
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun a ha => by
      rw [Finset.mem_filter] at ha
      rw [ha.2]
  rw [Finset.sum_congr rfl fun b _ => htoReal b]
  rw [Finset.sum_fiberwise_of_maps_to
    (fun a ha => Finset.mem_image_of_mem g ha)]
  exact Finset.sum_congr rfl fun a _ => rfl

/-- The expectation of the indicator of a decidable property is the total
mass of the elements satisfying it (finite case). -/
theorem expect_indicator_decide [Fintype α] (q : α → Prop)
    [DecidablePred q] :
    p.expect (fun a => if q a then 1 else 0) =
      ∑ a ∈ Finset.univ.filter q, (p a).toReal := by
  rw [expect_eq_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun a _ => by
    split_ifs <;> simp

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The **extended nonnegative expectation** of an `ℝ≥0∞`-valued function
`f` under a probability mass function `p`, defined directly as the `tsum`
`∑' a, p a * f a`. Unlike the Bochner-integral `expect`, it needs no
measurability or integrability hypothesis and takes the value `∞` when the
expected value diverges, rather than collapsing to `0`. -/
noncomputable def expectENN (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, p a * f a

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- On a `Fintype` the extended expectation is an unconditional finite
sum. -/
theorem expectENN_eq_sum [Fintype α] (p : PMF α) (f : α → ℝ≥0∞) :
    p.expectENN f = ∑ a, p a * f a := by
  rw [expectENN, tsum_fintype]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The extended expectation of a constant function is that constant, for
an arbitrary `p` (no finiteness needed). -/
theorem expectENN_const (p : PMF α) (c : ℝ≥0∞) :
    p.expectENN (fun _ => c) = c := by
  rw [expectENN, ENNReal.tsum_mul_right, tsum_coe, one_mul]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The extended expectation under the uniform distribution on a nonempty
`Fintype` is the average of the values. -/
theorem expectENN_uniformOfFintype [Fintype α] [Nonempty α]
    (f : α → ℝ≥0∞) :
    (PMF.uniformFintype α).expectENN f =
      (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ a, f a := by
  rw [expectENN_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [uniformFintype_apply]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Extended expectation is additive, with no finiteness or integrability
hypotheses: `ℝ≥0∞`-valued `tsum`s are always summable. -/
theorem expectENN_add (p : PMF α) (f g : α → ℝ≥0∞) :
    p.expectENN (f + g) = p.expectENN f + p.expectENN g := by
  simp only [expectENN, Pi.add_apply, mul_add, ENNReal.tsum_add]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Extended expectation commutes with finite sums, with no finiteness
hypothesis on the sample space. -/
theorem expectENN_sum (p : PMF α) (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    p.expectENN (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, p.expectENN (f i) := by
  simp only [expectENN, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- If all the mass of `p` lies in a finite set `s`, the extended
expectation is the finite sum over `s`, with no finiteness assumption on
the ambient type. -/
theorem expectENN_eq_sum_of_finite_support (p : PMF α) (s : Finset α)
    (hs : ∀ a ∉ s, p a = 0) (f : α → ℝ≥0∞) :
    p.expectENN f = ∑ a ∈ s, p a * f a := by
  rw [expectENN, tsum_eq_sum (fun a ha => by rw [hs a ha, zero_mul])]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The extended expectation of a mapped distribution is the extended
expectation of the composition (change of variables), for arbitrary
source and target types: both sides are nonnegative `tsum`s, so Tonelli
(`ENNReal.tsum_comm`) applies with no finiteness or measurability
hypotheses. -/
theorem expectENN_map (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    (p.map g).expectENN f = p.expectENN (f ∘ g) := by
  classical
  have hterm : ∀ b : β, (p.map g) b * f b =
      ∑' a, (if b = g a then p a else 0) * f b := by
    intro b
    rw [map_apply, ← ENNReal.tsum_mul_right]
  have hinner : ∀ a : α,
      (∑' b, (if b = g a then p a else 0) * f b) = p a * f (g a) := by
    intro a
    rw [tsum_eq_single (g a)]
    · simp
    · intro b hb
      simp [hb]
  simp only [expectENN, Function.comp_def]
  rw [tsum_congr hterm, ENNReal.tsum_comm]
  exact tsum_congr hinner

/-- Bridge from the extended expectation to the real expectation for a
natural-valued observable on a finite type: the `toReal` of the
`ℝ≥0∞`-valued expectation is the real expectation of the cast. -/
theorem expectENN_natCast_toReal [Fintype α] (p : PMF α) (g : α → ℕ) :
    (p.expectENN (fun a => (g a : ℝ≥0∞))).toReal =
      p.expect (fun a => (g a : ℝ)) := by
  rw [expectENN_eq_sum, expect_eq_sum,
    ENNReal.toReal_sum (fun a _ =>
      ENNReal.mul_ne_top (apply_ne_top p a) (ENNReal.natCast_ne_top _))]
  exact Finset.sum_congr rfl fun a _ => by
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

end PMF
