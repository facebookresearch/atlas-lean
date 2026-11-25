/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.PNat.Notation
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Standardized real laws and their i.i.d. normal approximation

The sample law is the actual countable product of a real Borel probability law.
Every positive finite sum uses its initial coordinates. The CDF and all moments
are Mathlib's measure-theoretic constructions. Arbitrary-universe i.i.d. models
are transported to this canonical realization by equality of pushforward laws.

Source: the classical Berry--Esseen setup; catalogue constants/19a.md, revision
2c1968cd520b60f1cf3cf50749f7285e800e4e15. Historical sharper bounds are not asserted here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BerryEsseenModel

/-- **Standardized laws with finite third moment.** A measure $\mu$ on $\mathbb{R}$ is a
standardized law when it is a probability measure with mean $\int x \, d\mu(x) = 0$ and variance
$1$, and has finite third absolute moment $\int |x|^3 \, d\mu(x) < \infty$. -/
structure IsStandardizedLaw (μ : Measure ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  mean_zero : (∫ x, x ∂μ) = 0
  variance_one : variance id μ = 1
  third_moment : MemLp id 3 μ

/-- **I.i.d. product law.** For a measure $\mu$ on $\mathbb{R}$, the i.i.d. product law of $\mu$ is
the measure on the sequence space $\mathbb{R}^{\mathbb{N}}$ that is the infinite product
$\mu^{\otimes \mathbb{N}}$ of countably many copies of $\mu$ when $\mu$ is a probability measure,
and the zero measure otherwise. -/
noncomputable def iidLaw (μ : Measure ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ ↦ μ)

/-- **Normalized sum.** For a positive integer $n$ and a real sequence
$\omega = (\omega_0, \omega_1, \dots)$, the normalized sum $S_n(\omega)$ is the sum of the first $n$
coordinates divided by $\sqrt{n}$: $S_n(\omega) = (\omega_0 + \dots + \omega_{n-1})/\sqrt{n}$. -/
noncomputable def normalizedSum (n : ℕ+) (ω : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n.1, ω i) / Real.sqrt (n.1 : ℝ)

/-- **Law of the normalized sum.** For a measure $\mu$ on $\mathbb{R}$ and a positive integer
$n$, the normalized law of $\mu$ at $n$ is the pushforward of the i.i.d. law of $\mu$ on
$\mathbb{R}^{\mathbb{N}}$ (the product measure $\mu^{\otimes \mathbb{N}}$ when $\mu$ is a
probability measure, and the zero measure otherwise) under the normalized sum
$\omega \mapsto (\omega_0 + \dots + \omega_{n-1})/\sqrt{n}$. -/
noncomputable def normalizedLaw (μ : Measure ℝ) (n : ℕ+) : Measure ℝ :=
  (iidLaw μ).map (normalizedSum n)

/-- **Standard normal CDF.** For $x \in \mathbb{R}$, $\Phi(x)$ is the value at $x$ of the
cumulative distribution function of the standard normal distribution $\mathcal{N}(0, 1)$, that
is, the probability that a standard normal random variable is at most $x$. -/
noncomputable def normalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- **Third absolute moment.** The third absolute moment of a measure $\mu$ on $\mathbb{R}$ is the
real number $\int |x|^3 \, d\mu(x)$, taken to be $0$ when $x \mapsto |x|^3$ is not integrable
with respect to $\mu$.

This integrand is integrable whenever $\mu$ is a standardized law. -/
noncomputable def thirdMoment (μ : Measure ℝ) : ℝ := ∫ x, |x| ^ 3 ∂μ

/-- **Finite third absolute moment as an $L^3$ condition.** For every measure $\mu$ on
$\mathbb{R}$, the identity function $x \mapsto x$ belongs to $L^3(\mu)$ if and only if
the function $x \mapsto |x|^3$ is $\mu$-integrable. -/
theorem memLp_three_iff_integrable_absCube (μ : Measure ℝ) :
    MemLp id 3 μ ↔ Integrable (fun x : ℝ ↦ |x| ^ 3) μ := by
  simpa [Real.norm_eq_abs] using (integrable_norm_rpow_iff
    (μ := μ) (f := (id : ℝ → ℝ)) (p := (3 : ENNReal))
    measurable_id.aestronglyMeasurable (by norm_num) (by simp)).symm

/-- **Kolmogorov error.** For a measure $\mu$ on $\mathbb{R}$ and a positive integer $n$, the
Kolmogorov error of $\mu$ at $n$ is the real supremum
$\sup_{x \in \mathbb{R}} |F_{\mu,n}(x) - \Phi(x)|$, where $\Phi$ is the standard normal
cumulative distribution function and $F_{\mu,n}$ is Mathlib's cumulative distribution function
of the normalized law of $\mu$ at $n$. When $\mu$ is a probability measure, $F_{\mu,n}(x)$ is
the mass the normalized law gives to $(-\infty, x]$; otherwise the normalized law is the zero
measure and $F_{\mu,n}$ is a fixed but unspecified cumulative distribution function of some
probability measure, not the zero function.

The values $|F_{\mu,n}(x) - \Phi(x)|$ lie in $[0, 1]$, so the supremum is finite. -/
noncomputable def kolmogorovError (μ : Measure ℝ) (n : ℕ+) : ℝ :=
  sSup (Set.range (fun x : ℝ ↦ |cdf (normalizedLaw μ n) x - normalCDF x|))

/-- **The i.i.d. product of a standardized law is a probability measure.** If $\mu$ is a
standardized law on $\mathbb{R}$, then the i.i.d. product law of $\mu$ on $\mathbb{R}^{\mathbb{N}}$
is a probability measure. -/
theorem iidLaw_probability {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) :
    IsProbabilityMeasure (iidLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.probability
  unfold iidLaw
  infer_instance

/-- **Measurability of the normalized sum.** For every positive integer $n$, the map sending a real
sequence $\omega = (\omega_0, \omega_1, \dots)$ to $(\omega_0 + \dots + \omega_{n-1})/\sqrt{n}$ is
measurable with respect to the product $\sigma$-algebra on $\mathbb{R}^{\mathbb{N}}$. -/
theorem normalizedSum_measurable (n : ℕ+) : Measurable (normalizedSum n) :=
  (Finset.measurable_sum _ (fun i _ ↦ measurable_pi_apply i)).div_const _

/-- **The normalized law is a probability measure.** For every standardized law $\mu$ on
$\mathbb{R}$ (a probability measure with mean $0$, variance $1$ and finite third absolute
moment) and every positive integer $n$, the normalized law of $\mu$ at $n$ is a probability
measure. -/
theorem normalizedLaw_probability {μ : Measure ℝ} (hμ : IsStandardizedLaw μ)
    (n : ℕ+) : IsProbabilityMeasure (normalizedLaw μ n) := by
  let : IsProbabilityMeasure (iidLaw μ) := iidLaw_probability hμ
  unfold normalizedLaw
  infer_instance

/-- **Coordinates of the i.i.d. product are independent.** If $\mu$ is a standardized law on
$\mathbb{R}$, then the coordinate maps $\omega \mapsto \omega_i$ on $\mathbb{R}^{\mathbb{N}}$, for
$i \in \mathbb{N}$, are mutually independent under the i.i.d. product law of $\mu$. -/
theorem iidLaw_independent {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) :
    iIndepFun (fun (i : ℕ) (ω : ℕ → ℝ) ↦ ω i) (iidLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.probability
  exact iIndepFun_infinitePi (fun _ ↦ measurable_id)

/-- **Coordinate laws of the i.i.d. product.** If $\mu$ is a standardized law on $\mathbb{R}$ and
$i$ is a natural number, then the pushforward of the i.i.d. product law of $\mu$ under the
coordinate map $\omega \mapsto \omega_i$ from $\mathbb{R}^{\mathbb{N}}$ to $\mathbb{R}$ is $\mu$. -/
theorem iidLaw_map_eval {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) (i : ℕ) :
    (iidLaw μ).map (fun ω ↦ ω i) = μ := by
  let : IsProbabilityMeasure μ := hμ.probability
  exact Measure.infinitePi_map_eval _ i

/-- **Coordinates of the i.i.d. product are distributed like the original law.** Let $\mu$ be a
standardized law on $\mathbb{R}$ and let $i$ be a natural number. The coordinate map
$\omega \mapsto \omega_i$ on $\mathbb{R}^{\mathbb{N}}$ under the i.i.d. product law of $\mu$ and
the identity map of $\mathbb{R}$ under $\mu$ are identically distributed. -/
theorem iidLaw_identDistrib {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) (i : ℕ) :
    IdentDistrib (fun ω : ℕ → ℝ ↦ ω i) id (iidLaw μ) μ := by
  refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [iidLaw_map_eval hμ, Measure.map_id]

/-- **CDF of the normalized sum.** Let $\mu$ be a standardized law on $\mathbb{R}$
(a probability measure with mean $0$, variance $1$ and finite third absolute moment), let $n$ be
a positive integer and let $x \in \mathbb{R}$. Then the cumulative distribution function of the
normalized law of $\mu$ at $n$, evaluated at $x$, equals the probability under the i.i.d. law
$\mu^{\otimes \mathbb{N}}$ on $\mathbb{R}^{\mathbb{N}}$ of the event
$\{\omega \in \mathbb{R}^{\mathbb{N}} : (\omega_0 + \dots + \omega_{n-1})/\sqrt{n} \le x\}$. -/
theorem normalized_cdf_eq {μ : Measure ℝ} (hμ : IsStandardizedLaw μ)
    (n : ℕ+) (x : ℝ) :
    cdf (normalizedLaw μ n) x = (iidLaw μ).real {ω | normalizedSum n ω ≤ x} := by
  let : IsProbabilityMeasure (normalizedLaw μ n) := normalizedLaw_probability hμ n
  rw [cdf_eq_real, normalizedLaw,
    map_measureReal_apply (normalizedSum_measurable n) measurableSet_Iic]
  rfl

/-- **Standardized laws have an integrable third absolute moment.** If $\mu$ is a standardized law
on $\mathbb{R}$, then the function $x \mapsto |x|^3$ is integrable with respect to $\mu$. -/
theorem thirdMoment_integrable {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) :
    Integrable (fun x : ℝ ↦ |x| ^ 3) μ := by
  have h := hμ.third_moment.integrable_norm_rpow (by norm_num) (by norm_num)
  simpa using h

/-- **Nonnegativity of the third absolute moment.** For every measure $\mu$ on $\mathbb{R}$, the
third absolute moment $\int_{\mathbb{R}} |x|^3 \, d\mu(x)$ is nonnegative.

As a real number, this integral is taken to be $0$ when $|x|^3$ is not $\mu$-integrable. -/
theorem thirdMoment_nonnegative (μ : Measure ℝ) : 0 ≤ thirdMoment μ :=
  integral_nonneg (fun x ↦ pow_nonneg (abs_nonneg x) 3)

/-- **The third absolute moment of a standardized law is positive.** If $\mu$ is a standardized
law on $\mathbb{R}$, that is, a probability measure with mean $0$, variance $1$ and finite third
absolute moment, then its third absolute moment $\int |x|^3 \, d\mu(x)$ is strictly positive.

The variance condition is what excludes a zero third absolute moment. -/
theorem thirdMoment_positive {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) :
    0 < thirdMoment μ := by
  have hne : thirdMoment μ ≠ 0 := by
    intro hz
    have hc : (fun x : ℝ ↦ |x| ^ 3) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun x ↦ pow_nonneg (abs_nonneg x) 3) (thirdMoment_integrable hμ)).mp hz
    have hid : id =ᵐ[μ] (0 : ℝ → ℝ) := hc.mono (fun x hx ↦ by simpa using hx)
    have hv := variance_congr hid
    rw [hμ.variance_one, variance_zero] at hv
    norm_num at hv
  exact lt_of_le_of_ne (thirdMoment_nonnegative μ) hne.symm

/-- **The CDF error is at most one.** Let $\mu$ be a measure on $\mathbb{R}$, $n$ a positive integer
and $x$ a real number. Let $F_{\mu,n}$ be the distribution function of the normalized law of $\mu$
at $n$ and $\Phi$ the standard normal distribution function. Then $|F_{\mu,n}(x) - \Phi(x)| \le 1$.

No assumption is made on $\mu$: both distribution functions take values in $[0, 1]$. -/
theorem pointwise_error_le_one (μ : Measure ℝ) (n : ℕ+) (x : ℝ) :
    |cdf (normalizedLaw μ n) x - normalCDF x| ≤ 1 := by
  have h₁ := cdf_nonneg (normalizedLaw μ n) x
  have h₂ := cdf_le_one (normalizedLaw μ n) x
  have h₃ := cdf_nonneg (gaussianReal 0 1) x
  have h₄ := cdf_le_one (gaussianReal 0 1) x
  unfold normalCDF
  rw [abs_le]
  constructor <;> linarith

/-- **The CDF errors are bounded above.** Let $\mu$ be a measure on $\mathbb{R}$, let $n$ be a
positive integer, let $F$ be the cumulative distribution function of the normalized law of $\mu$
at $n$, and let $\Phi$ be the standard normal cumulative distribution function. Then the set
$\{|F(x) - \Phi(x)| : x \in \mathbb{R}\}$ is bounded above. -/
theorem errorRange_bddAbove (μ : Measure ℝ) (n : ℕ+) :
    BddAbove (Set.range (fun x : ℝ ↦ |cdf (normalizedLaw μ n) x - normalCDF x|)) := by
  refine ⟨1, ?_⟩
  rintro y ⟨x, rfl⟩
  exact pointwise_error_le_one μ n x

/-- **Each CDF error is at most the Kolmogorov error.** Let $\mu$ be a measure on $\mathbb{R}$,
$n$ a positive integer, $F_{\mu,n}$ the distribution function of the normalized law of $\mu$ at
$n$ and $\Phi$ the standard normal distribution function. Then for every real $x$,
$|F_{\mu,n}(x) - \Phi(x)| \le \sup_{y \in \mathbb{R}} |F_{\mu,n}(y) - \Phi(y)|$, the right side
being the Kolmogorov error of $\mu$ at $n$. -/
theorem pointwise_le_kolmogorovError (μ : Measure ℝ) (n : ℕ+) (x : ℝ) :
    |cdf (normalizedLaw μ n) x - normalCDF x| ≤ kolmogorovError μ n :=
  le_csSup (errorRange_bddAbove μ n) ⟨x, rfl⟩

/-- **The Kolmogorov error is nonnegative.** For every measure $\mu$ on $\mathbb{R}$ and every
positive integer $n$, the Kolmogorov error of $\mu$ at $n$, that is
$\sup_{x \in \mathbb{R}} |F_{\mu,n}(x) - \Phi(x)|$ where $F_{\mu,n}$ is Mathlib's cumulative
distribution function of the normalized law of $\mu$ at $n$ and $\Phi$ is the standard normal
cumulative distribution function, is nonnegative.

Here $F_{\mu,n}(x)$ is the mass the normalized law gives to $(-\infty, x]$ when $\mu$ is a
probability measure; otherwise the normalized law is the zero measure and $F_{\mu,n}$ is a
fixed but unspecified cumulative distribution function of some probability measure. -/
theorem kolmogorovError_nonnegative (μ : Measure ℝ) (n : ℕ+) :
    0 ≤ kolmogorovError μ n :=
  (abs_nonneg _).trans (pointwise_le_kolmogorovError μ n 0)

/-- **The Kolmogorov error is at most one.** For every measure $\mu$ on $\mathbb{R}$ and every
positive integer $n$, the Kolmogorov error of $\mu$ at $n$, that is
$\sup_{x \in \mathbb{R}} |F_{\mu,n}(x) - \Phi(x)|$ where $F_{\mu,n}$ is Mathlib's cumulative
distribution function of the normalized law of $\mu$ at $n$ and $\Phi$ is the standard normal
cumulative distribution function, is at most $1$.

Here $F_{\mu,n}(x)$ is the mass the normalized law gives to $(-\infty, x]$ when $\mu$ is a
probability measure; otherwise the normalized law is the zero measure and $F_{\mu,n}$ is a
fixed but unspecified cumulative distribution function of some probability measure. -/
theorem kolmogorovError_le_one (μ : Measure ℝ) (n : ℕ+) :
    kolmogorovError μ n ≤ 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨x, rfl⟩
  exact pointwise_error_le_one μ n x

/-- **Kolmogorov error bounds are uniform CDF bounds.** Let $\mu$ be a measure on $\mathbb{R}$, let
$n$ be a positive integer, let $F$ be the cumulative distribution function of the normalized law
of $\mu$ at $n$, and let $\Phi$ be the standard normal cumulative distribution function. Then for
every real $a$, the Kolmogorov error of $\mu$ at $n$ is at most $a$ if and only if
$|F(x) - \Phi(x)| \le a$ for every real $x$. -/
theorem error_le_iff (μ : Measure ℝ) (n : ℕ+) (a : ℝ) :
    kolmogorovError μ n ≤ a ↔ ∀ x : ℝ, |cdf (normalizedLaw μ n) x - normalCDF x| ≤ a := by
  constructor
  · intro h x
    exact (pointwise_le_kolmogorovError μ n x).trans h
  · intro h
    apply csSup_le (Set.range_nonempty _)
    rintro y ⟨x, rfl⟩
    exact h x

/-- **The standard Gaussian is a standardized law.** The standard normal law $N(0,1)$ on
$\mathbb{R}$ is a standardized law: it is a probability measure with mean $0$, variance $1$ and
finite third absolute moment. -/
theorem standardGaussian_isStandardized : IsStandardizedLaw (gaussianReal 0 1) := by
  refine ⟨inferInstance, integral_id_gaussianReal, ?_, ?_⟩
  · simp [variance_id_gaussianReal]
  · exact memLp_id_gaussianReal (μ := 0) (v := 1) (3 : ℝ≥0)

/-- **The normalized law with one summand.** For every standardized law $\mu$ on $\mathbb{R}$
(a probability measure with mean $0$, variance $1$ and finite third absolute moment), the
normalized law of $\mu$ at $n = 1$ is $\mu$ itself. -/
theorem normalizedLaw_one {μ : Measure ℝ} (hμ : IsStandardizedLaw μ) :
    normalizedLaw μ ⟨1, by decide⟩ = μ := by
  have hsum : normalizedSum ⟨1, by decide⟩ = (fun ω : ℕ → ℝ ↦ ω 0) := by
    funext ω
    simp [normalizedSum]
  unfold normalizedLaw
  rw [hsum, iidLaw_map_eval hμ]

/-- **The Kolmogorov error vanishes for one standard Gaussian summand.** Let $F$ be the distribution
function of the normalized law of the standard normal law $N(0,1)$ at $n = 1$, and $\Phi$ the
standard normal distribution function. Then the Kolmogorov error of $N(0,1)$ at $n = 1$,
$\sup_{x \in \mathbb{R}} |F(x) - \Phi(x)|$, equals $0$. -/
theorem standardGaussian_error_one : kolmogorovError (gaussianReal 0 1) ⟨1, by decide⟩ = 0 := by
  unfold kolmogorovError
  rw [normalizedLaw_one standardGaussian_isStandardized]
  simp [normalCDF]

/-- **Standardized i.i.d. models.** Let $\Omega$ be a measurable space with a measure $P$, and let
$(X_i)_{i \in \mathbb{N}}$ be real-valued functions on $\Omega$. They form a standardized i.i.d.
model when $P$ is a probability measure, every $X_i$ is measurable, the $X_i$ are mutually
independent under $P$, every $X_i$ has the same law under $P$ as $X_0$, and $X_0$ has mean
$\int_\Omega X_0 \, dP = 0$, variance $1$ and finite third absolute moment
$\int_\Omega |X_0|^3 \, dP < \infty$. -/
structure IsIIDModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) : Prop where
  probability : IsProbabilityMeasure P
  measurable : ∀ i, Measurable (X i)
  independent : iIndepFun X P
  identical : ∀ i, IdentDistrib (X i) (X 0) P P
  mean_zero : (∫ ω, X 0 ω ∂P) = 0
  variance_one : variance (X 0) P = 1
  third_moment : MemLp (X 0) 3 P

/-- **The common law of an i.i.d. model is standardized.** Let $P$ be a measure on a measurable
space $\Omega$ and $X_0, X_1, \dots$ real-valued functions on $\Omega$ forming an i.i.d. model:
$P$ is a probability measure, the $X_i$ are measurable, independent and identically distributed,
and $X_0$ has mean $0$, variance $1$ and finite third absolute moment. Then the law of $X_0$, the
pushforward of $P$ under $X_0$, is a standardized law. -/
theorem IsIIDModel.standardizedLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (h : IsIIDModel P X) : IsStandardizedLaw (P.map (X 0)) := by
  let : IsProbabilityMeasure P := h.probability
  have hd : IdentDistrib (X 0) id P (P.map (X 0)) :=
    ⟨(h.measurable 0).aemeasurable, measurable_id.aemeasurable, by simp⟩
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · exact hd.integral_eq.symm.trans h.mean_zero
  · exact hd.variance_eq.symm.trans h.variance_one
  · exact hd.memLp_iff.mp h.third_moment

/-- **The joint law of a standardized i.i.d. model.** If $(X_i)_{i \in \mathbb{N}}$ is a
standardized i.i.d. model on a measurable space $\Omega$ with measure $P$, then the law under $P$
of the sequence map $\omega \mapsto (X_i(\omega))_{i \in \mathbb{N}}$ from $\Omega$ to
$\mathbb{R}^{\mathbb{N}}$ equals the i.i.d. product law of the law of $X_0$ under $P$. -/
theorem IsIIDModel.jointLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (h : IsIIDModel P X) :
    P.map (fun ω i ↦ X i ω) = iidLaw (P.map (X 0)) := by
  calc
    P.map (fun ω i ↦ X i ω) = Measure.infinitePi (fun i ↦ P.map (X i)) :=
      iIndepFun.map_fun_eq_infinitePi_map h.measurable h.independent
    _ = iidLaw (P.map (X 0)) := by
      unfold iidLaw
      congr 1
      funext i
      exact (h.identical i).map_eq

/-- **Normalized sums of an i.i.d. model have the canonical law.** Let $P$ be a probability
measure on a measurable space $\Omega$ and let $X_0, X_1, \dots$ be real random variables on
$\Omega$ that are measurable, independent and identically distributed under $P$, with $X_0$ of
mean $0$, variance $1$ and finite third absolute moment. Then for every positive integer $n$,
the law under $P$ of $(X_0 + \dots + X_{n-1})/\sqrt{n}$ equals the normalized law at $n$ of the
law of $X_0$. -/
theorem IsIIDModel.normalizedLaw_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (h : IsIIDModel P X) (n : ℕ+) :
    P.map (fun ω ↦ (∑ i ∈ Finset.range n.1, X i ω) / Real.sqrt (n.1 : ℝ)) =
      normalizedLaw (P.map (X 0)) n := by
  rw [normalizedLaw, ← h.jointLaw,
    Measure.map_map (normalizedSum_measurable n) (Measurable.of_eval h.measurable)]
  rfl

/-- **Third absolute moment of the common law.** Let $P$ be a measure on a measurable space $\Omega$
and $X_0, X_1, \dots$ real-valued functions on $\Omega$ forming an i.i.d. model: $P$ is a
probability measure, the $X_i$ are measurable, independent and identically distributed, and $X_0$
has mean $0$, variance $1$ and finite third absolute moment. Then the third absolute moment of the
law of $X_0$ equals $\int_\Omega |X_0(\omega)|^3 \, dP(\omega)$. -/
theorem IsIIDModel.thirdMoment_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (h : IsIIDModel P X) :
    thirdMoment (P.map (X 0)) = ∫ ω, |X 0 ω| ^ 3 ∂P := by
  have hd : IdentDistrib (X 0) id P (P.map (X 0)) :=
    ⟨(h.measurable 0).aemeasurable, measurable_id.aemeasurable, by simp⟩
  exact ((hd.comp (continuous_abs.measurable.pow_const 3)).integral_eq).symm

end BerryEsseenModel
