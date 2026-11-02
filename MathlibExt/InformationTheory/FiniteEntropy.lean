/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Shannon entropy of finite probability mass functions

The logarithm is in base two. Zero-probability atoms contribute zero through
`Real.negMulLog`.

The second half relates finite laws to Mathlib's Kullback–Leibler divergence `klDiv`:

* `toReal_klDiv_eq_sum`: on a finite space, `klDiv μ ν = ∑ μ{a} log (μ{a} / ν{a})` (natural log)
  for `μ ≪ ν` of equal mass.
* `surprisal q`: the information content `-log₂ q` of an outcome of probability `q`, which is `∞`
  at `q = 0`. `crossEntropy p q = ∑ p a · surprisal (q a)` takes values in `ℝ≥0∞`, so an outcome
  that `q` rules out but `p` allows costs `∞`.
* `crossEntropy_eq_shannonEntropy_add_klDiv`: `H(p, q) = H(p) + KL(p ‖ q) / log 2`, with no
  support hypothesis.
* `shannonEntropy_le_crossEntropy` (**Gibbs' inequality**) and `crossEntropy_eq_shannonEntropy_iff`:
  equality only at `q = p`, through Mathlib's `klDiv_eq_zero_iff`.
* `lintegral_surprisal`: the expected surprisal `E_{a ~ p}[-log₂ q a]` is `H(p, q)`.
-/

@[expose] public section

namespace InformationTheory

open scoped BigOperators

/-- **Shannon entropy.** The Shannon entropy in bits of a probability mass function $p$ on a finite
type $\alpha$ is $H(p) = -\sum_{a \in \alpha} p(a) \log_2 p(a)$, where a term with $p(a) = 0$
contributes $0$.

Source: the finite Shannon sum; Li, arXiv:2501.13736v4, entropy conventions. -/
noncomputable def shannonEntropy {α : Type*} [Fintype α] (p : PMF α) : ℝ :=
  (∑ a, Real.negMulLog (p a).toReal) / Real.log 2

/-- **A point mass has zero entropy.** For every outcome $a$ of a finite alphabet, the point mass
at $a$ has Shannon entropy $0$. -/
@[simp] theorem shannonEntropy_pure {α : Type*} [Fintype α] (a : α) :
    shannonEntropy (PMF.pure a) = 0 := by
  classical
  unfold shannonEntropy
  have h : ∑ b : α, Real.negMulLog ((PMF.pure a) b).toReal = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : b = a <;> simp [PMF.pure_apply, hb]
  rw [h, zero_div]

/-- **A constant observation has zero entropy.** For any probability mass function $p$ on a type
$\alpha$ and any point $b$ of a finite alphabet $\beta$, the image of $p$ under the constant map
$\alpha \to \beta$ with value $b$ has Shannon entropy $0$. -/
theorem shannonEntropy_map_const {α β : Type*} [Fintype β]
    (p : PMF α) (b : β) :
    shannonEntropy (p.map (Function.const α b)) = 0 := by
  rw [PMF.map_const, shannonEntropy_pure]

/-- **Entropy is invariant under relabeling.** For a probability mass function $p$ on a finite
alphabet $\alpha$ and a bijection $e : \alpha \to \beta$ onto a finite alphabet $\beta$, the image
of $p$ under $e$ has the same Shannon entropy as $p$. -/
theorem shannonEntropy_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (e : α ≃ β) : shannonEntropy (p.map e) = shannonEntropy p := by
  classical
  have hmass (a : α) : (p.map e) (e a) = p a := by
    simp [PMF.map_apply, e.apply_eq_iff_eq, tsum_fintype]
  unfold shannonEntropy
  congr 1
  rw [← e.sum_comp (fun b => Real.negMulLog ((p.map e) b).toReal)]
  simp only [hmass]

/-- **Appending a singleton coordinate preserves entropy.** For a probability mass function $p$ on
a finite alphabet $\alpha$, the image of $p$ under $a \mapsto (a, 0)$ in $\alpha \times \{0\}$
has the same Shannon entropy as $p$. -/
theorem shannonEntropy_map_prod_singleton {α : Type*} [Fintype α] (p : PMF α) :
    shannonEntropy (p.map (fun a => (a, (0 : Fin 1)))) = shannonEntropy p := by
  let e : α ≃ α × Fin 1 :=
    ⟨fun a => (a, 0), Prod.fst, fun _ => rfl,
      fun z => Prod.ext rfl (Subsingleton.elim _ _)⟩
  exact shannonEntropy_map_equiv p e

/-! ### Kullback–Leibler divergence and cross-entropy -/

section KL

open MeasureTheory Real
open scoped ENNReal

variable {α : Type*}

/-- **Kullback–Leibler divergence on a finite space.** Let $\mu$ and $\nu$ be finite measures on
a finite type $\alpha$ in which every singleton is measurable, with $\mu \ll \nu$ and
$\mu(\alpha) = \nu(\alpha)$. Then the Kullback–Leibler divergence $\mathrm{KL}(\mu \parallel \nu)$,
taken as a real number, equals $\sum_{a \in \alpha} \mu(\{a\}) \log (\mu(\{a\}) / \nu(\{a\}))$,
where $\log$ is the natural logarithm and a term with $\mu(\{a\}) = 0$ is $0$. -/
theorem toReal_klDiv_eq_sum [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (huniv : μ Set.univ = ν Set.univ) :
    (klDiv μ ν).toReal = ∑ a, μ.real {a} * log (μ.real {a} / ν.real {a}) := by
  set f : α → ℝ≥0∞ := fun a ↦ μ {a} / ν {a} with hf_def
  have hf : μ = ν.withDensity f := by
    rw [Measure.ext_iff_singleton]
    intro a
    rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton, hf_def]
    by_cases h0 : ν {a} = 0
    · rw [h0, mul_zero]
      exact hμν h0
    · rw [ENNReal.div_mul_cancel h0 (measure_ne_top ν _)]
  have hrn : μ.rnDeriv ν =ᵐ[ν] f := by
    have := Measure.rnDeriv_withDensity ν (Measurable.of_discrete (f := f))
    rwa [← hf] at this
  rw [toReal_klDiv_of_measure_eq hμν huniv]
  have hllr : llr μ ν =ᵐ[μ] fun a ↦ log (f a).toReal := by
    filter_upwards [hμν.ae_le hrn] with a ha
    rw [llr, ha]
  rw [integral_congr_ae hllr, integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [hf_def, smul_eq_mul, ENNReal.toReal_div, measureReal_def, measureReal_def]

theorem toMeasure_real_singleton [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α)
    (a : α) : p.toMeasure.real {a} = (p a).toReal := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton p a (measurableSet_singleton a)]

theorem toMeasure_absolutelyContinuous [MeasurableSpace α] {p q : PMF α}
    (hpq : ∀ a, q a = 0 → p a = 0) : p.toMeasure ≪ q.toMeasure := by
  refine Measure.AbsolutelyContinuous.mk fun s hsm hs ↦ ?_
  rw [PMF.toMeasure_apply_eq_zero_iff _ hsm, Set.disjoint_left] at hs ⊢
  intro a hap has
  refine (PMF.mem_support_iff _ _).mp hap (hpq a ?_)
  by_contra h
  exact hs ((PMF.mem_support_iff _ _).mpr h) has

/-- **Kullback–Leibler divergence of finite probability laws.** Let $p$ and $q$ be probability
mass functions on a finite type $\alpha$ in which every singleton is measurable, such that
$p(a) = 0$ whenever $q(a) = 0$, and let $P$ and $Q$ be the measures they define. Then the
Kullback–Leibler divergence $\mathrm{KL}(P \parallel Q)$, taken as a real number, equals
$\sum_{a \in \alpha} p(a) \log (p(a) / q(a))$, where $\log$ is the natural logarithm and a term
with $p(a) = 0$ is $0$. -/
theorem toReal_klDiv_toMeasure [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {p q : PMF α} (hpq : ∀ a, q a = 0 → p a = 0) :
    (klDiv p.toMeasure q.toMeasure).toReal =
      ∑ a, (p a).toReal * log ((p a).toReal / (q a).toReal) := by
  rw [toReal_klDiv_eq_sum (toMeasure_absolutelyContinuous hpq) (by simp)]
  simp only [toMeasure_real_singleton]

/-- **Surprisal.** The surprisal (information content) in bits of an outcome of probability
$q$ is $-\log_2 q$, with value $\infty$ when $q = 0$. Formally $q$ ranges over the extended
nonnegative reals $[0, \infty]$: the surprisal of $0$ is $\infty$, the surprisal of
$q \in (0, \infty)$ is $\max(0, -\log_2 q)$, and the surprisal of $\infty$ is $0$. -/
noncomputable def surprisal (q : ℝ≥0∞) : ℝ≥0∞ :=
  if q = 0 then ∞ else ENNReal.ofReal (-logb 2 q.toReal)

theorem surprisal_zero : surprisal 0 = ∞ := by simp [surprisal]

theorem surprisal_of_ne_zero {q : ℝ≥0∞} (hq : q ≠ 0) :
    surprisal q = ENNReal.ofReal (-logb 2 q.toReal) := by simp [surprisal, hq]

theorem surprisal_eq_top_iff {q : ℝ≥0∞} : surprisal q = ∞ ↔ q = 0 := by
  by_cases hq : q = 0
  · simp [hq, surprisal_zero]
  · simp [surprisal_of_ne_zero hq, hq]

/-- **Cross-entropy.** For probability mass functions $p$ and $q$ on a finite alphabet, the
cross-entropy of $q$ relative to $p$ is $H(p, q) = \sum_a p(a) \cdot (-\log_2 q(a))$ in bits, a
value in $[0, \infty]$. Here $-\log_2 q(a)$ is the surprisal of $a$ under $q$, which is $\infty$
when $q(a) = 0$, and a term with $p(a) = 0$ contributes $0$. So $H(p, q)$ is $\infty$ exactly
when $p$ charges an outcome that $q$ rules out. -/
noncomputable def crossEntropy [Fintype α] (p q : PMF α) : ℝ≥0∞ := ∑ a, p a * surprisal (q a)

theorem crossEntropy_eq_top_iff [Fintype α] {p q : PMF α} :
    crossEntropy p q = ∞ ↔ ∃ a, q a = 0 ∧ p a ≠ 0 := by
  simp only [crossEntropy, ENNReal.sum_eq_top, Finset.mem_univ, true_and, ENNReal.mul_eq_top,
    PMF.apply_ne_top, false_and, or_false, surprisal_eq_top_iff]
  exact exists_congr fun a ↦ and_comm

/-- **Cross-entropy of a point mass.** For an outcome $y$ of a finite alphabet and a probability
mass function $q$ on it, the cross-entropy $H(\delta_y, q)$ of $q$ relative to the point mass
$\delta_y$ at $y$ equals the surprisal $-\log_2 q(y)$ of $y$ under $q$, which is $\infty$ when
$q(y) = 0$. -/
theorem crossEntropy_pure [Fintype α] (y : α) (q : PMF α) :
    crossEntropy (PMF.pure y) q = surprisal (q y) := by
  classical
  simp [crossEntropy, PMF.pure_apply]

/-- **Cross-entropy is expected surprisal.** For probability mass functions $p$ and $q$ on a
finite alphabet, the expected surprisal $\mathbb{E}_{a \sim p}[-\log_2 q(a)]$ (with
$-\log_2 0 = \infty$), taken as the integral of a $[0, \infty]$-valued function with respect to
the law $p$, equals the cross-entropy $H(p, q)$. -/
theorem lintegral_surprisal [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) : ∫⁻ a, surprisal (q a) ∂p.toMeasure = crossEntropy p q := by
  rw [lintegral_fintype, crossEntropy]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a), mul_comm]

theorem shannonEntropy_nonneg [Fintype α] (p : PMF α) : 0 ≤ shannonEntropy p :=
  div_nonneg (Finset.sum_nonneg fun a _ ↦ negMulLog_nonneg ENNReal.toReal_nonneg
    (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one p a)))
    (log_nonneg one_le_two)

/-- **Cross-entropy is entropy plus divergence.** For probability mass functions $p$ and $q$ on a
finite alphabet, the cross-entropy $H(p, q)$ in bits equals $H(p) + D(p \parallel q) / \ln 2$,
where $H(p)$ is the Shannon entropy of $p$ in bits and $D(p \parallel q)$ is the
Kullback–Leibler divergence of $p$ from $q$ with the natural logarithm. The identity holds in
$[0, \infty]$ with no support hypothesis: when $p$ charges an outcome that $q$ rules out, both
sides are $\infty$. -/
theorem crossEntropy_eq_shannonEntropy_add_klDiv [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : PMF α) :
    crossEntropy p q = ENNReal.ofReal (shannonEntropy p) +
      klDiv p.toMeasure q.toMeasure / ENNReal.ofReal (log 2) := by
  have hlog : 0 < log 2 := log_pos one_lt_two
  by_cases hpq : ∀ a, q a = 0 → p a = 0
  · have hkl := klDiv_ne_top (toMeasure_absolutelyContinuous hpq)
      (Integrable.of_finite (f := llr p.toMeasure q.toMeasure))
    rw [← ENNReal.ofReal_toReal hkl, ← ENNReal.ofReal_div_of_pos hlog,
      ← ENNReal.ofReal_add (shannonEntropy_nonneg p) (div_nonneg ENNReal.toReal_nonneg hlog.le),
      toReal_klDiv_toMeasure hpq]
    have hterm : ∀ a, p a * surprisal (q a) =
        ENNReal.ofReal (-((p a).toReal * logb 2 (q a).toReal)) := fun a ↦ by
      by_cases hp : p a = 0
      · simp [hp]
      have hq : q a ≠ 0 := fun h ↦ hp (hpq a h)
      rw [surprisal_of_ne_zero hq, ← ENNReal.ofReal_toReal (PMF.apply_ne_top p a),
        ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
        mul_neg]
    have hnonneg : ∀ a, 0 ≤ -((p a).toReal * logb 2 (q a).toReal) := fun a ↦ by
      rw [neg_nonneg]
      refine mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg ?_
      exact logb_nonpos one_lt_two ENNReal.toReal_nonneg
        (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one q a))
    rw [crossEntropy, Finset.sum_congr rfl fun a _ ↦ hterm a,
      ← ENNReal.ofReal_sum_of_nonneg fun a _ ↦ hnonneg a]
    congr 1
    rw [shannonEntropy, ← add_div, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    by_cases hp : p a = 0
    · simp [hp]
    have hq : q a ≠ 0 := fun h ↦ hp (hpq a h)
    have hp' : (p a).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp, PMF.apply_ne_top p a⟩
    have hq' : (q a).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hq, PMF.apply_ne_top q a⟩
    rw [negMulLog, log_div hp' hq', logb]
    field_simp
    ring
  · push Not at hpq
    obtain ⟨a, hq, hp⟩ := hpq
    have hnac : ¬ p.toMeasure ≪ q.toMeasure := fun h ↦ by
      have := h (s := {a})
      simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)] at this
      exact hp (this hq)
    rw [(crossEntropy_eq_top_iff).mpr ⟨a, hq, hp⟩, klDiv_of_not_ac hnac,
      ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top, add_top]

/-- **Gibbs' inequality**: the cross-entropy of any prediction `q` is at least the entropy of the
truth `p`. -/
theorem shannonEntropy_le_crossEntropy [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : PMF α) :
    ENNReal.ofReal (shannonEntropy p) ≤ crossEntropy p q := by
  rw [crossEntropy_eq_shannonEntropy_add_klDiv]
  exact le_self_add

/-- **Equality in Gibbs' inequality.** For probability mass functions $p$ and $q$ on a finite
alphabet, the cross-entropy $H(p, q)$ in bits equals the Shannon entropy $H(p)$ in bits if and
only if $q = p$. Thus log loss is a strictly proper scoring rule. -/
theorem crossEntropy_eq_shannonEntropy_iff [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p q : PMF α) :
    crossEntropy p q = ENNReal.ofReal (shannonEntropy p) ↔ q = p := by
  rw [crossEntropy_eq_shannonEntropy_add_klDiv]
  constructor
  · intro h
    have h0 : klDiv p.toMeasure q.toMeasure / ENNReal.ofReal (log 2) = 0 := by
      have := congrArg (fun x ↦ x - ENNReal.ofReal (shannonEntropy p)) h
      simpa using this
    rw [ENNReal.div_eq_zero_iff, or_iff_left ENNReal.ofReal_ne_top, klDiv_eq_zero_iff,
      PMF.toMeasure_inj] at h0
    exact h0.symm
  · rintro rfl
    rw [klDiv_self, ENNReal.zero_div, add_zero]

end KL

end InformationTheory
