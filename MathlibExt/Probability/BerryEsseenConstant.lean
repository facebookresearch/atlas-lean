/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BerryEsseenModel
public import MathlibExt.Probability.BerryEsseen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Least common i.i.d. Berry--Esseen coefficient

The coefficient is chosen before the real probability law and positive sample
size. The implemented coefficient-42 theorem proves nonemptiness. Positivity
of the third moment proves boundedness below and closure at the real infimum.
The Bernoulli subclass consists of actual standardized two-point laws.

Source: catalogue constants/19a.md, revision 2c1968cd520b60f1cf3cf50749f7285e800e4e15.
The symbolic Esseen benchmark is a definition, not its asserted optimality.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory BerryEsseenModel
open scoped ENNReal NNReal

namespace BerryEsseenConstant

/-- **Admissible Berry–Esseen coefficient.** A real number $C$ is an admissible Berry–Esseen
coefficient when, for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$
and finite third absolute moment $\rho = \int |x|^3 \, d\mu(x)$, and every positive integer $n$,
the Kolmogorov error $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$ is at most $C \rho / \sqrt{n}$.
Here $F_n$ is the distribution function of $(X_1 + \dots + X_n)/\sqrt{n}$ for independent random
variables $X_1, X_2, \dots$ with law $\mu$, and $\Phi$ is the standard normal distribution
function. -/
def IsAdmissible (C : ℝ) : Prop :=
  ∀ μ : Measure ℝ, IsStandardizedLaw μ → ∀ n : ℕ+,
    kolmogorovError μ n ≤ C * thirdMoment μ / Real.sqrt (n.1 : ℝ)

/-- **The optimal Berry–Esseen constant.** Call a real number $C$ admissible if for every
probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute
moment $\rho = \int |x|^3 \, d\mu$, and every positive integer $n$,
$$\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le \frac{C \rho}{\sqrt{n}},$$
where $F_n$ is the distribution function of $(X_1 + \dots + X_n)/\sqrt{n}$ for independent
random variables $X_1, X_2, \dots$ with law $\mu$, and $\Phi$ is the standard normal
distribution function. The optimal Berry–Esseen constant is the infimum of the admissible $C$.

The set of admissible constants is nonempty (it contains $42$) and bounded below by $0$, so
this is a genuine real infimum. -/
noncomputable def value : ℝ := sInf {C : ℝ | IsAdmissible C}

/-- **Esseen's lower-bound constant.** Esseen's constant is the real number
$(\sqrt{10} + 3)/(6\sqrt{2\pi})$.

Esseen showed that the Berry–Esseen constant for i.i.d. sums is at least this number; the
definition records the value only, not that lower bound. -/
noncomputable def esseenConstant : ℝ :=
  (Real.sqrt 10 + 3) / (6 * Real.sqrt (2 * Real.pi))

/-- **Esseen's lower-bound constant is positive.** The number $(\sqrt{10} + 3)/(6\sqrt{2\pi})$ is
positive. -/
theorem esseenConstant_positive : 0 < esseenConstant := by
  unfold esseenConstant
  positivity

/-- **Admissible coefficients are nonnegative.** Every admissible Berry–Esseen coefficient
$C \in \mathbb{R}$ satisfies $C \ge 0$. -/
theorem isAdmissible_nonnegative {C : ℝ} (hC : IsAdmissible C) : 0 ≤ C := by
  have h := hC (gaussianReal 0 1) standardGaussian_isStandardized ⟨1, by decide⟩
  rw [standardGaussian_error_one] at h
  simp only [Nat.cast_one, Real.sqrt_one, div_one] at h
  by_contra hn
  have hneg : C < 0 := lt_of_not_ge hn
  have hprod : C * thirdMoment (gaussianReal 0 1) < 0 :=
    mul_neg_of_neg_of_pos hneg (thirdMoment_positive standardGaussian_isStandardized)
  linarith

/-- **The Berry–Esseen bound with coefficient 42.** The number $42$ is an admissible
Berry–Esseen coefficient: for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$,
variance $1$ and finite third absolute moment $\rho = \int |x|^3 \, d\mu(x)$, and every positive
integer $n$, the Kolmogorov error $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$ is at most
$42 \rho / \sqrt{n}$, where $F_n$ is the distribution function of $(X_1 + \dots + X_n)/\sqrt{n}$
for independent random variables $X_1, X_2, \dots$ with law $\mu$, and $\Phi$ is the standard
normal distribution function. -/
theorem isAdmissible_fortyTwo : IsAdmissible 42 := by
  intro μ hμ n
  let : IsProbabilityMeasure μ := hμ.probability
  let : IsProbabilityMeasure (iidLaw μ) := iidLaw_probability hμ
  let : IsProbabilityMeasure (normalizedLaw μ n) := normalizedLaw_probability hμ n
  have hd := iidLaw_identDistrib hμ 0
  have hmem : MemLp (fun ω : ℕ → ℝ ↦ ω 0) 3 (iidLaw μ) :=
    hd.memLp_iff.mpr hμ.third_moment
  have hmean : (∫ ω : ℕ → ℝ, ω 0 ∂iidLaw μ) = 0 := hd.integral_eq.trans hμ.mean_zero
  have hvar : variance (fun ω : ℕ → ℝ ↦ ω 0) (iidLaw μ) = 1 :=
    hd.variance_eq.trans hμ.variance_one
  have hthird : (∫ ω : ℕ → ℝ, |ω 0| ^ 3 ∂iidLaw μ) = thirdMoment μ :=
    (hd.comp (continuous_abs.measurable.pow_const 3)).integral_eq
  apply (error_le_iff μ n _).mpr
  intro x
  have h := MathlibExt.Probability.BerryEsseenWanted.berry_esseen_explicit
    (fun i (ω : ℕ → ℝ) ↦ ω i) (fun i ↦ measurable_pi_apply i) (iidLaw_independent hμ)
    (fun i ↦ (iidLaw_identDistrib hμ i).trans hd.symm) hmem hmean
    (by rw [hvar]; norm_num) n.1 n.2 x
  simp only [hvar, mul_one, Real.sqrt_one, one_pow, one_mul, hthird] at h
  simp only [normalCDF, cdf_eq_real]
  exact h

/-- **Admissible Berry–Esseen coefficients exist.** The set of real numbers $C$ that are
admissible Berry–Esseen coefficients (common Berry–Esseen coefficients for all standardized laws
and all positive sample sizes) is nonempty. -/
theorem admissible_nonempty : ({C : ℝ | IsAdmissible C} : Set ℝ).Nonempty :=
  ⟨42, isAdmissible_fortyTwo⟩

/-- **The admissible Berry–Esseen coefficients are bounded below.** The set of real numbers $C$
that are admissible Berry–Esseen coefficients (common Berry–Esseen coefficients for all
standardized laws and all positive sample sizes) is bounded below. -/
theorem admissible_bddBelow : BddBelow {C : ℝ | IsAdmissible C} :=
  ⟨0, fun _ h ↦ isAdmissible_nonnegative h⟩

/-- **The optimal Berry–Esseen coefficient is nonnegative.** The infimum $C^*$ of all admissible
Berry–Esseen coefficients satisfies $0 \le C^*$. -/
theorem value_nonnegative : 0 ≤ value :=
  le_csInf admissible_nonempty (fun _ h ↦ isAdmissible_nonnegative h)

/-- **The optimal Berry–Esseen coefficient is at most every admissible one.** If $C$ is an
admissible Berry–Esseen coefficient, then the infimum $C^*$ of all admissible coefficients
satisfies $C^* \le C$. -/
theorem value_le_of_isAdmissible {C : ℝ} (hC : IsAdmissible C) : value ≤ C :=
  csInf_le admissible_bddBelow hC

/-- **The optimal Berry–Esseen coefficient is at most 42.** The infimum $C^*$ of all admissible
Berry–Esseen coefficients satisfies $C^* \le 42$. -/
theorem value_le_fortyTwo : value ≤ 42 := value_le_of_isAdmissible isAdmissible_fortyTwo

/-- **Admissibility is upward closed.** If $C \le D$ are real numbers and $C$ is an admissible
Berry–Esseen coefficient, then $D$ is an admissible Berry–Esseen coefficient. -/
theorem isAdmissible_mono {C D : ℝ} (hC : IsAdmissible C) (hCD : C ≤ D) :
    IsAdmissible D := by
  intro μ hμ n
  exact (hC μ hμ n).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCD (thirdMoment_nonnegative μ)) (Real.sqrt_nonneg _))

/-- **The optimal Berry–Esseen coefficient satisfies the Berry–Esseen bound.** Let $C^*$ be the
infimum of all admissible Berry–Esseen coefficients. For every standardized law $\mu$ on
$\mathbb{R}$ and every positive integer $n$, the Kolmogorov error of $\mu$ at sample size $n$ is
at most $C^* \rho(\mu) / \sqrt{n}$, where $\rho(\mu) = \int |x|^3 \, d\mu(x)$ is the third
absolute moment of $\mu$. -/
theorem value_bound (μ : Measure ℝ) (hμ : IsStandardizedLaw μ) (n : ℕ+) :
    kolmogorovError μ n ≤ value * thirdMoment μ / Real.sqrt (n.1 : ℝ) := by
  have hn : (0 : ℝ) < n.1 := by exact_mod_cast n.2
  have hk : 0 < thirdMoment μ / Real.sqrt (n.1 : ℝ) :=
    div_pos (thirdMoment_positive hμ) (Real.sqrt_pos.mpr hn)
  have hlower : kolmogorovError μ n / (thirdMoment μ / Real.sqrt (n.1 : ℝ)) ≤ value := by
    apply le_csInf admissible_nonempty
    intro C hC
    apply (div_le_iff₀ hk).mpr
    simpa only [mul_div_assoc] using hC μ hμ n
  simpa only [mul_div_assoc] using (div_le_iff₀ hk).mp hlower

/-- **The optimal Berry–Esseen coefficient is admissible.** The infimum $C^*$ of all admissible
Berry–Esseen coefficients is itself an admissible coefficient. -/
theorem value_isAdmissible : IsAdmissible value := value_bound

/-- **The Berry–Esseen constant is the least admissible coefficient.** The infimum $C^*$ of all
admissible Berry–Esseen coefficients is the least element of the set of admissible
coefficients: $C^*$ is admissible, and $C^* \le C$ for every admissible coefficient $C$. -/
theorem value_isLeast : IsLeast {C : ℝ | IsAdmissible C} value :=
  ⟨value_isAdmissible, fun _ h ↦ value_le_of_isAdmissible h⟩

/-- **Admissible coefficients are exactly those above the optimal one.** A real number $C$ is an
admissible Berry–Esseen coefficient if and only if $C_0 \le C$, where $C_0$ is the optimal
Berry–Esseen coefficient, the infimum of the set of admissible coefficients. -/
theorem isAdmissible_iff_value_le (C : ℝ) : IsAdmissible C ↔ value ≤ C :=
  ⟨value_le_of_isAdmissible, isAdmissible_mono value_isAdmissible⟩

/-- **Admissible coefficients bound every standardized i.i.d. sequence.** Let $C$ be an admissible
Berry–Esseen coefficient. Let $X_0, X_1, X_2, \dots$ be measurable real random variables on a
probability space $(\Omega, P)$ that are independent and identically distributed, with
$\mathbb{E}[X_0] = 0$, $\operatorname{Var}(X_0) = 1$ and $\mathbb{E}|X_0|^3 < \infty$. Then for
every positive integer $n$ and every real $x$,
$$
\left| P\left( \frac{X_0 + \dots + X_{n-1}}{\sqrt{n}} \le x \right) - \Phi(x) \right|
\le \frac{C \, \mathbb{E}|X_0|^3}{\sqrt{n}},
$$
where $\Phi$ is the distribution function of the standard normal law. -/
theorem iid_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    {C : ℝ} (hC : IsAdmissible C) (h : IsIIDModel P X) (n : ℕ+) (x : ℝ) :
    |cdf (P.map (fun ω ↦ (∑ i ∈ Finset.range n.1, X i ω) /
        Real.sqrt (n.1 : ℝ))) x - normalCDF x| ≤
      C * (∫ ω, |X 0 ω| ^ 3 ∂P) / Real.sqrt (n.1 : ℝ) := by
  have hp := (pointwise_le_kolmogorovError (P.map (X 0)) n x).trans
    (hC _ h.standardizedLaw n)
  rw [← h.normalizedLaw_eq n, h.thirdMoment_eq] at hp
  exact hp

/-- **Standardized two-point law.** A measure $\mu$ on $\mathbb{R}$ is a standardized two-point
law when it is a probability measure with mean $0$, variance $1$ and finite third absolute
moment, and there are real numbers $a \ne b$ with $\mu(\mathbb{R} \setminus \{a, b\}) = 0$. -/
def IsBernoulliLaw (μ : Measure ℝ) : Prop :=
  IsStandardizedLaw μ ∧ ∃ a b : ℝ, a ≠ b ∧ μ ({a, b}ᶜ) = 0

/-- **Symmetric Bernoulli law.** The symmetric Bernoulli law is the measure
$\frac12 \delta_{-1} + \frac12 \delta_1$ on $\mathbb{R}$, where $\delta_a$ denotes the Dirac mass
at $a$; it puts mass $1/2$ at each of the points $-1$ and $1$. -/
noncomputable def symmetricBernoulliLaw : Measure ℝ :=
  ((1 / 2 : ℝ≥0) : ENNReal) • Measure.dirac (-1) +
    ((1 / 2 : ℝ≥0) : ENNReal) • Measure.dirac 1

/-- The two actual atom masses add to one. -/
instance symmetricBernoulli_probability : IsProbabilityMeasure symmetricBernoulliLaw where
  measure_univ := by
    simp only [symmetricBernoulliLaw, Measure.add_apply, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    norm_cast
    norm_num

/-- **The symmetric Bernoulli law has moments of all orders.** For every exponent
$p \in [0, \infty]$, the identity function of $\mathbb{R}$ belongs to $L^p$ of the symmetric
Bernoulli law. -/
theorem symmetricBernoulli_memLp (p : ENNReal) : MemLp id p symmetricBernoulliLaw := by
  have hbound : ∀ᵐ x ∂symmetricBernoulliLaw, ‖x‖ ≤ 1 := by
    rw [symmetricBernoulliLaw, ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure (by simp) _, Measure.ae_smul_measure (by simp) _⟩
  exact MemLp.of_bound measurable_id.aestronglyMeasurable 1 hbound

/-- **Integrals against the symmetric Bernoulli law.** For every function
$f : \mathbb{R} \to \mathbb{R}$, the integral of $f$ against the symmetric Bernoulli law
$\frac12 \delta_{-1} + \frac12 \delta_1$ equals $\frac12 f(-1) + \frac12 f(1)$. -/
theorem symmetricBernoulli_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂symmetricBernoulliLaw) = (1 / 2) * f (-1) + (1 / 2) * f 1 := by
  have h₁ : Integrable f (Measure.dirac (-1)) := integrable_dirac (by simp)
  have h₂ : Integrable f (Measure.dirac 1) := integrable_dirac (by simp)
  rw [symmetricBernoulliLaw, integral_add_measure
    (h₁.smul_measure (c := ((1 / 2 : ℝ≥0) : ENNReal)) ENNReal.coe_ne_top)
    (h₂.smul_measure (c := ((1 / 2 : ℝ≥0) : ENNReal)) ENNReal.coe_ne_top)]
  simp [integral_smul_measure, integral_dirac]

/-- **The symmetric Bernoulli law is standardized.** The symmetric Bernoulli law, which puts mass
$1/2$ at each of the points $-1$ and $1$, is a standardized law: it is a probability measure on
$\mathbb{R}$ with mean $0$ and variance $1$, and it has a finite third absolute moment. -/
theorem symmetricBernoulli_isStandardized : IsStandardizedLaw symmetricBernoulliLaw := by
  refine ⟨inferInstance, ?_, ?_, symmetricBernoulli_memLp 3⟩
  · rw [symmetricBernoulli_integral]
    norm_num
  · rw [variance_eq_sub (symmetricBernoulli_memLp 2)]
    change (∫ x, x ^ 2 ∂symmetricBernoulliLaw) -
      (∫ x, x ∂symmetricBernoulliLaw) ^ 2 = 1
    rw [symmetricBernoulli_integral, symmetricBernoulli_integral]
    norm_num

/-- **The symmetric Bernoulli law is a standardized two-point law.** The law
$\frac12 \delta_{-1} + \frac12 \delta_1$ on $\mathbb{R}$ is a probability measure with mean $0$,
variance $1$ and finite third absolute moment, and it is concentrated on the two distinct points
$-1$ and $1$. -/
theorem symmetricBernoulli_isBernoulli : IsBernoulliLaw symmetricBernoulliLaw := by
  refine ⟨symmetricBernoulli_isStandardized, -1, 1, by norm_num, ?_⟩
  norm_num [symmetricBernoulliLaw, Measure.add_apply, Measure.smul_apply]

/-- **Third absolute moment of the symmetric Bernoulli law.** The third absolute moment
$\int |x|^3 \, d\mu(x)$ of the symmetric Bernoulli law $\mu$ equals $1$. -/
theorem symmetricBernoulli_thirdMoment : thirdMoment symmetricBernoulliLaw = 1 := by
  rw [thirdMoment, symmetricBernoulli_integral]
  norm_num

/-- **Admissible Berry–Esseen coefficient for two-point laws.** A real number $C$ is an admissible
Berry–Esseen coefficient for standardized two-point laws when, for every probability measure $\mu$
on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute moment
$\rho = \int |x|^3 \, d\mu(x)$ that is concentrated on two distinct points, and every positive
integer $n$, the Kolmogorov error $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$ is at most
$C \rho / \sqrt{n}$. Here $F_n$ is the distribution function of $(X_1 + \dots + X_n)/\sqrt{n}$ for
independent random variables $X_1, X_2, \dots$ with law $\mu$, and $\Phi$ is the standard normal
distribution function. -/
def IsBernoulliAdmissible (C : ℝ) : Prop :=
  ∀ μ : Measure ℝ, IsBernoulliLaw μ → ∀ n : ℕ+,
    kolmogorovError μ n ≤ C * thirdMoment μ / Real.sqrt (n.1 : ℝ)

/-- **Bernoulli Berry–Esseen constant.** The Bernoulli Berry–Esseen constant is the infimum, in
$\mathbb{R}$, of the set of real numbers $C$ that are admissible Berry–Esseen coefficients for the
Bernoulli subclass: for every standardized law $\mu$ (a probability measure on $\mathbb{R}$ with
mean $0$, variance $1$ and finite third absolute moment) concentrated on two distinct points, and
every positive integer $n$, the supremum over $x \in \mathbb{R}$ of the distance between the
distribution function of $(X_0 + \dots + X_{n-1})/\sqrt{n}$ at $x$, for independent
$\mu$-distributed $X_0, \dots, X_{n-1}$, and the standard normal distribution function at $x$ is
at most $C \rho(\mu) / \sqrt{n}$, where $\rho(\mu) = \int |x|^3 \, d\mu(x)$. -/
noncomputable def bernoulliValue : ℝ := sInf {C : ℝ | IsBernoulliAdmissible C}

/-- **Bernoulli-admissible coefficients are nonnegative.** Every real number $C$ that is an
admissible Berry–Esseen coefficient for standardized two-point laws satisfies $C \ge 0$.

The class of standardized two-point laws is nonempty: it contains the law with mass $1/2$ at each
of $-1$ and $1$. -/
theorem isBernoulliAdmissible_nonnegative {C : ℝ} (hC : IsBernoulliAdmissible C) :
    0 ≤ C := by
  have h := hC symmetricBernoulliLaw symmetricBernoulli_isBernoulli ⟨1, by decide⟩
  simp only [symmetricBernoulli_thirdMoment, mul_one, Nat.cast_one,
    Real.sqrt_one, div_one] at h
  exact (kolmogorovError_nonnegative _ _).trans h

/-- **Bernoulli-admissible coefficients exist.** The set of real numbers $C$ that are admissible
Berry–Esseen coefficients for the Bernoulli subclass (common Berry–Esseen coefficients for all
standardized laws concentrated on two points and all positive sample sizes) is nonempty.

The coefficient $42$, admissible for all standardized laws, is one such coefficient. -/
theorem bernoulliAdmissible_nonempty : ({C : ℝ | IsBernoulliAdmissible C} : Set ℝ).Nonempty :=
  ⟨42, fun μ hμ ↦ isAdmissible_fortyTwo μ hμ.1⟩

/-- **The Bernoulli-admissible coefficients are bounded below.** The set of real numbers $C$ that
are admissible Berry–Esseen coefficients for the Bernoulli subclass (common Berry–Esseen
coefficients for all standardized laws concentrated on two points and all positive sample sizes)
is bounded below. -/
theorem bernoulliAdmissible_bddBelow : BddBelow {C : ℝ | IsBernoulliAdmissible C} :=
  ⟨0, fun _ h ↦ isBernoulliAdmissible_nonnegative h⟩

/-- **The Bernoulli Berry–Esseen constant is nonnegative.** The infimum of the real numbers that
are admissible Berry–Esseen coefficients for the Bernoulli subclass is nonnegative. -/
theorem bernoulliValue_nonnegative : 0 ≤ bernoulliValue :=
  le_csInf bernoulliAdmissible_nonempty (fun _ h ↦ isBernoulliAdmissible_nonnegative h)

/-- **The Bernoulli Berry–Esseen constant is at most the general one.** The infimum of the real
numbers that are admissible Berry–Esseen coefficients for the Bernoulli subclass is at most the
infimum of the real numbers that are admissible Berry–Esseen coefficients for all standardized
laws. -/
theorem bernoulliValue_le_value : bernoulliValue ≤ value :=
  csInf_le bernoulliAdmissible_bddBelow (fun μ hμ ↦ value_isAdmissible μ hμ.1)

end BerryEsseenConstant
