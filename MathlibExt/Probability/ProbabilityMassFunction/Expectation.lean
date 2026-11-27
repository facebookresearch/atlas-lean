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

/-- **Expectation under a probability mass function.** Let $\alpha$ be a type carrying a σ-algebra
in which singletons are measurable, let $p$ be a probability mass function on $\alpha$ and let
$f : \alpha \to \mathbb{R}$. The expectation of $f$ under $p$ is the Bochner integral
$\int f \, d\mu_p$, where $\mu_p$ is the probability measure on $\alpha$ associated to $p$.

On a finite type it equals the finite sum $\sum_{a \in \alpha} p(a) f(a)$, with each mass $p(a)$
read as a real number. As a Bochner integral it is $0$ when $f$ is not integrable; nonnegative
or natural-valued observables should use the extended nonnegative expectation, whose value in
$[0, \infty]$ can be $\infty$. -/
noncomputable def expect (p : PMF α) (f : α → ℝ) : ℝ :=
  ∫ a, f a ∂p.toMeasure

/-- **Expectation as a series.** Let $p$ be a probability mass function on a measurable space
$\alpha$ in which singletons are measurable, and let $f : \alpha \to \mathbb{R}$ be integrable with
respect to the probability measure associated to $p$. Then the expectation of $f$ under $p$ equals
the unordered sum $\sum_{a \in \alpha} p(a) f(a)$. -/
theorem expect_eq_tsum (hf : MeasureTheory.Integrable f p.toMeasure) :
    p.expect f = ∑' a, (p a).toReal • f a :=
  integral_eq_tsum p f hf

/-- **Expectation on a finite type.** Let $p$ be a probability mass function on a finite measurable
space $\alpha$ in which singletons are measurable, and let $f : \alpha \to \mathbb{R}$. Then the
expectation of $f$ under $p$ equals the finite sum $\sum_{a \in \alpha} p(a) f(a)$. -/
theorem expect_eq_sum [Fintype α] (p : PMF α) (f : α → ℝ) :
    p.expect f = ∑ a, (p a).toReal * f a := by
  rw [expect, integral_eq_sum]
  exact Finset.sum_congr rfl fun a _ => smul_eq_mul _ _

/-- **Expectation of a constant on a finite type.** Let $\alpha$ be a finite set with a
$\sigma$-algebra in which singletons are measurable and let $p$ be a probability mass function on
$\alpha$. For every $c \in \mathbb{R}$, the expectation of the constant function $a \mapsto c$
under $p$ is $c$. -/
theorem expect_const [Fintype α] (p : PMF α) (c : ℝ) :
    p.expect (fun _ => c) = c := by
  have h1 : ∑ a, p a = 1 := (tsum_fintype (fun a => p a)).symm.trans (tsum_coe p)
  have hsum : ∑ a, (p a).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => apply_ne_top p a), h1,
      ENNReal.toReal_one]
  rw [expect_eq_sum, ← Finset.sum_mul, hsum, one_mul]

/-- **Expectation under the uniform distribution.** Let $\alpha$ be a nonempty finite type carrying
a σ-algebra in which singletons are measurable. For every function $f : \alpha \to \mathbb{R}$,
the expectation of $f$ under the uniform distribution on $\alpha$ equals the average
$\frac{1}{|\alpha|} \sum_{a \in \alpha} f(a)$. -/
theorem expect_uniformOfFintype [Fintype α] [Nonempty α] (f : α → ℝ) :
    (PMF.uniformFintype α).expect f =
      (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  rw [expect_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [uniformFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **Additivity of expectation on a finite type.** Let $\alpha$ be a finite set with a
$\sigma$-algebra in which singletons are measurable, let $p$ be a probability mass function on
$\alpha$, and write $\mathbb{E}_p[h]$ for the expectation of $h : \alpha \to \mathbb{R}$ under $p$.
For all $f, g : \alpha \to \mathbb{R}$, $\mathbb{E}_p[f + g] = \mathbb{E}_p[f] + \mathbb{E}_p[g]$.

No integrability hypothesis is needed. -/
theorem expect_add [Fintype α] : p.expect (f + g) = p.expect f + p.expect g := by
  rw [expect_eq_sum, expect_eq_sum, expect_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [Pi.add_apply, mul_add]

/-- **Expectation of a finite sum.** Let $p$ be a probability mass function on a finite type
$\alpha$ carrying a σ-algebra in which singletons are measurable, and write $\mathbb{E}_p[g]$ for
the expectation of $g : \alpha \to \mathbb{R}$ under $p$. For every finite subset $s$ of an index
type $\iota$ and every family of functions $f_i : \alpha \to \mathbb{R}$, $i \in \iota$, we have
$\mathbb{E}_p[a \mapsto \sum_{i \in s} f_i(a)] = \sum_{i \in s} \mathbb{E}_p[f_i]$. -/
theorem expect_sum [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    p.expect (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, p.expect (f i) := by
  rw [expect_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (expect_eq_sum p (f i)).symm

/-- **Homogeneity of expectation on a finite type.** Let $\alpha$ be a finite set with a
$\sigma$-algebra in which singletons are measurable, let $p$ be a probability mass function on
$\alpha$, and write $\mathbb{E}_p[h]$ for the expectation of $h : \alpha \to \mathbb{R}$ under $p$.
For every $c \in \mathbb{R}$ and $f : \alpha \to \mathbb{R}$, the function $a \mapsto c\,f(a)$ has
expectation $c\,\mathbb{E}_p[f]$. -/
theorem expect_const_mul [Fintype α] (c : ℝ) (f : α → ℝ) :
    p.expect (fun a => c * f a) = c * p.expect f := by
  rw [expect_eq_sum, expect_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **Expectation of a scalar multiple.** Let $p$ be a probability mass function on a finite
measurable space $\alpha$ in which singletons are measurable, let $c \in \mathbb{R}$ and let
$f : \alpha \to \mathbb{R}$. The expectation under $p$ of the scalar multiple $c f$ (the function
$a \mapsto c \cdot f(a)$) equals $c$ times the expectation of $f$ under $p$. -/
theorem expect_smul [Fintype α] (c : ℝ) (f : α → ℝ) :
    p.expect (c • f) = c * p.expect f := by
  have : (c • f) = fun a => c * f a := funext fun a => smul_eq_mul c (f a)
  rw [this]; exact expect_const_mul c f

/-- **Nonnegativity of expectation.** Let $p$ be a probability mass function on a finite measurable
space $\alpha$ in which singletons are measurable, and let $f : \alpha \to \mathbb{R}$ satisfy
$f(a) \ge 0$ for every $a \in \alpha$. Then the expectation of $f$ under $p$ is nonnegative. -/
theorem expect_nonneg [Fintype α] (hf : ∀ a, 0 ≤ f a) : 0 ≤ p.expect f := by
  rw [expect_eq_sum]
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg ENNReal.toReal_nonneg (hf a)

/-- **Monotonicity of expectation.** Let $p$ be a probability mass function on a finite measurable
space $\alpha$ in which singletons are measurable, and let $f, g : \alpha \to \mathbb{R}$ satisfy
$f(a) \le g(a)$ for every $a \in \alpha$. Then the expectation of $f$ under $p$ is at most the
expectation of $g$ under $p$. -/
theorem expect_le_expect [Fintype α] (hfg : ∀ a, f a ≤ g a) :
    p.expect f ≤ p.expect g := by
  rw [expect_eq_sum, expect_eq_sum]
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (hfg a) ENNReal.toReal_nonneg

/-- **Expectation of a finitely supported distribution.** Let $p$ be a probability mass function
on a measurable space $\alpha$ in which singletons are measurable, and let $s$ be a finite subset
of $\alpha$ such that $p(a) = 0$ for every $a \notin s$. Then for every function
$f : \alpha \to \mathbb{R}$, the expectation of $f$ under $p$ equals $\sum_{a \in s} p(a) f(a)$.

No integrability hypothesis on $f$ and no finiteness assumption on $\alpha$ is needed. -/
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

/-- **Change of variables for expectation.** Let $p$ be a probability mass function on a finite
measurable space $\alpha$ in which singletons are measurable, let $\beta$ be a measurable space in
which singletons are measurable, and let $g : \alpha \to \beta$ and $f : \beta \to \mathbb{R}$.
Write $g_* p$ for the pushforward of $p$ along $g$, which gives each $b \in \beta$ the mass
$\sum_{a :\, g(a) = b} p(a)$. Then the expectation of $f$ under $g_* p$ equals the expectation of
$f \circ g$ under $p$. -/
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

/-- **Expectation of an indicator.** Let $p$ be a probability mass function on a finite measurable
space $\alpha$ in which singletons are measurable, and let $q$ be a property of elements of
$\alpha$. The expectation under $p$ of the function equal to $1$ where $q$ holds and $0$ elsewhere
is $\sum_{a \in \alpha,\ q(a)} p(a)$, the total mass of the elements satisfying $q$. -/
theorem expect_indicator_decide [Fintype α] (q : α → Prop)
    [DecidablePred q] :
    p.expect (fun a => if q a then 1 else 0) =
      ∑ a ∈ Finset.univ.filter q, (p a).toReal := by
  rw [expect_eq_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun a _ => by
    split_ifs <;> simp

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Extended expectation.** For a probability mass function $p$ on a type $\alpha$ and a function
$f : \alpha \to [0, \infty]$, the extended expectation of $f$ under $p$ is the unordered sum
$\sum_{a \in \alpha} p(a) f(a)$ in $[0, \infty]$, which always exists.

Unlike the real-valued expectation, it needs no measurability or integrability hypothesis and
takes the value $\infty$ when the expected value diverges, rather than collapsing to $0$. -/
noncomputable def expectENN (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, p a * f a

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Extended expectation on a finite set.** Let $p$ be a probability mass function on a finite
set $\alpha$. For every $f : \alpha \to [0, \infty]$, the extended expectation of $f$ under $p$
equals the finite sum $\sum_{a \in \alpha} p(a)\, f(a)$. -/
theorem expectENN_eq_sum [Fintype α] (p : PMF α) (f : α → ℝ≥0∞) :
    p.expectENN f = ∑ a, p a * f a := by
  rw [expectENN, tsum_fintype]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Extended expectation of a constant.** Let $p$ be a probability mass function on a set
$\alpha$. For every $c \in [0, \infty]$, the extended expectation of the constant function
$a \mapsto c$ under $p$ is $c$.

The set $\alpha$ need not be finite. -/
theorem expectENN_const (p : PMF α) (c : ℝ≥0∞) :
    p.expectENN (fun _ => c) = c := by
  rw [expectENN, ENNReal.tsum_mul_right, tsum_coe, one_mul]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Extended expectation under the uniform distribution.** Let $\alpha$ be a nonempty finite type
and $f : \alpha \to [0, \infty]$. The extended expectation of $f$ under the uniform distribution on
$\alpha$ equals $|\alpha|^{-1} \sum_{a \in \alpha} f(a)$, computed in $[0, \infty]$. -/
theorem expectENN_uniformOfFintype [Fintype α] [Nonempty α]
    (f : α → ℝ≥0∞) :
    (PMF.uniformFintype α).expectENN f =
      (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ a, f a := by
  rw [expectENN_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [uniformFintype_apply]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Additivity of extended expectation.** Let $p$ be a probability mass function on a set
$\alpha$, and write $\overline{\mathbb{E}}_p[h]$ for the extended expectation of
$h : \alpha \to [0, \infty]$ under $p$. For all $f, g : \alpha \to [0, \infty]$,
$\overline{\mathbb{E}}_p[f + g] = \overline{\mathbb{E}}_p[f] + \overline{\mathbb{E}}_p[g]$.

No finiteness or integrability hypothesis is needed: sums of terms in $[0, \infty]$ always
converge. -/
theorem expectENN_add (p : PMF α) (f g : α → ℝ≥0∞) :
    p.expectENN (f + g) = p.expectENN f + p.expectENN g := by
  simp only [expectENN, Pi.add_apply, mul_add, ENNReal.tsum_add]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Extended expectation of a finite sum.** Let $p$ be a probability mass function on a set
$\alpha$, and write $\overline{\mathbb{E}}_p[h]$ for the extended expectation of
$h : \alpha \to [0, \infty]$ under $p$. For every index set $\iota$, finite subset
$s \subseteq \iota$ and family of functions $f_i : \alpha \to [0, \infty]$ ($i \in \iota$),
$\overline{\mathbb{E}}_p\bigl[a \mapsto \sum_{i \in s} f_i(a)\bigr] =
\sum_{i \in s} \overline{\mathbb{E}}_p[f_i]$.

The set $\alpha$ need not be finite. -/
theorem expectENN_sum (p : PMF α) (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    p.expectENN (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, p.expectENN (f i) := by
  simp only [expectENN, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Extended expectation under a finitely supported distribution.** Let $p$ be a probability
mass function on a set $\alpha$, and let $s \subseteq \alpha$ be a finite set with $p(a) = 0$ for
every $a \notin s$. For every $f : \alpha \to [0, \infty]$, the extended expectation of $f$
under $p$ equals $\sum_{a \in s} p(a)\, f(a)$.

The set $\alpha$ itself need not be finite. -/
theorem expectENN_eq_sum_of_finite_support (p : PMF α) (s : Finset α)
    (hs : ∀ a ∉ s, p a = 0) (f : α → ℝ≥0∞) :
    p.expectENN f = ∑ a ∈ s, p a * f a := by
  rw [expectENN, tsum_eq_sum (fun a ha => by rw [hs a ha, zero_mul])]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Change of variables for extended expectation.** Let $p$ be a probability mass function on a
set $\alpha$, let $g : \alpha \to \beta$ be a map to a set $\beta$, and let $g_* p$ be the
pushforward of $p$ along $g$, the probability mass function $b \mapsto \sum_{a : g(a) = b} p(a)$.
For every $f : \beta \to [0, \infty]$, the extended expectation of $f$ under $g_* p$ equals the
extended expectation of $f \circ g$ under $p$.

No finiteness or measurability hypothesis is needed: both sides are sums of terms in
$[0, \infty]$, whose order of summation can be interchanged freely. -/
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

/-- **Extended and real expectations agree on natural-valued functions.** Let $\alpha$ be a finite
set with a $\sigma$-algebra in which singletons are measurable, let $p$ be a probability mass
function on $\alpha$, and let $g : \alpha \to \mathbb{N}$. Let $x \in [0, \infty]$ be the
extended expectation of $g$, viewed as a function to $[0, \infty]$, under $p$, and send $x$ to
$\mathbb{R}$ by the map that is the identity on $[0, \infty)$ and sends $\infty$ to $0$. The
result is the expectation of $g$, viewed as a real-valued function, under $p$. -/
theorem expectENN_natCast_toReal [Fintype α] (p : PMF α) (g : α → ℕ) :
    (p.expectENN (fun a => (g a : ℝ≥0∞))).toReal =
      p.expect (fun a => (g a : ℝ)) := by
  rw [expectENN_eq_sum, expect_eq_sum,
    ENNReal.toReal_sum (fun a _ =>
      ENNReal.mul_ne_top (apply_ne_top p a) (ENNReal.natCast_ne_top _))]
  exact Finset.sum_congr rfl fun a _ => by
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

end PMF
