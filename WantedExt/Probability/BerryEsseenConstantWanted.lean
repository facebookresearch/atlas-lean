/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BerryEsseenConstant
public import Batteries.Util.ProofWanted

/-!
# Source requests for the absolute i.i.d. Berry--Esseen constant

These propositions use actual standardized probability laws and normalized
i.i.d. sums. Every missing proof is private `ProofWanted` data, not a proof or
assumption. Decimal endpoints are source literals, not checked rounding
certificates. The catalogue's false four-term 2013 minimum is not requested.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory BerryEsseenModel BerryEsseenConstant

namespace BerryEsseenWanted

/-- **Statement of Zolotarev's Berry–Esseen bound.** The proposition that the Berry–Esseen
constant $C_0$ is at most $0.82$. Here $C_0$ is the infimum of the real numbers $C$ such that
for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third
absolute moment $\beta_3 = \int |x|^3 \, d\mu(x)$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, where $X_1, \dots, X_n$ are independent with
law $\mu$, satisfies $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le C \beta_3 / \sqrt{n}$; here
$\Phi$ is the standard normal distribution function.

Source: catalogue C19a, upper row Z1967; the non-i.i.d. 0.9051 is context only. -/
def zolotarev1967UpperBound : Prop := value ≤ (82 / 100 : ℝ)

/-- **Statement of van Beek's Berry–Esseen bound.** The proposition that the Berry–Esseen
constant $C_0$ is at most $0.7975$. Here $C_0$ is the infimum of the real numbers $C$ such that
for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third
absolute moment $\beta_3 = \int |x|^3 \, d\mu(x)$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, where $X_1, \dots, X_n$ are independent with
law $\mu$, satisfies $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le C \beta_3 / \sqrt{n}$; here
$\Phi$ is the standard normal distribution function.

Source: catalogue C19a, upper row vB1972; original primary text is not retained here. -/
def vanBeek1972UpperBound : Prop := value ≤ (7975 / 10000 : ℝ)

/-- **Statement of Shiganov's Berry–Esseen bound.** The proposition that the Berry–Esseen
constant $C_0$ is at most $0.7655$. Here $C_0$ is the infimum of the real numbers $C$ such that
for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third
absolute moment $\beta_3 = \int |x|^3 \, d\mu(x)$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, where $X_1, \dots, X_n$ are independent with
law $\mu$, satisfies $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le C \beta_3 / \sqrt{n}$; here
$\Phi$ is the standard normal distribution function.

Source: catalogue C19a, upper row Shi1986; retained Shevtsova2011 introduction reports it. -/
def shiganov1986UpperBound : Prop := value ≤ (7655 / 10000 : ℝ)

/-- **Statement of Shevtsova's 2006 Berry–Esseen bound.** Let $C_0$ be the infimum of all
real $C$ such that for every real probability law $\mu$ with mean $0$, variance $1$ and finite
third absolute moment $\rho = \int |x|^3\,d\mu$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, for independent $X_1, \dots, X_n$ with law
$\mu$, satisfies $\sup_x |F_n(x) - \Phi(x)| \le C \rho / \sqrt{n}$, where $\Phi$ is the
standard normal distribution function. This is the proposition $C_0 \le 0.7056$.

Source: catalogue C19a, upper row She2006; retained Shevtsova2011 introduction reports it. -/
def shevtsova2006UpperBound : Prop := value ≤ (7056 / 10000 : ℝ)

/-- **Statement of the Korolev–Shevtsova upper bound.** For a probability measure $\mu$ on
$\mathbb{R}$ and an integer $n \ge 1$, let $F_n$ be the distribution function of
$(X_1 + \dots + X_n)/\sqrt{n}$ for independent random variables $X_1, X_2, \dots$ each with law
$\mu$, let $\Delta_n(\mu) = \sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$, where $\Phi$ is the
standard normal distribution function, and let $\beta_3(\mu) = \int |x|^3 \, d\mu$. Let $C_0$ be
the optimal i.i.d. Berry–Esseen constant, the infimum of all real $C$ such that
$\Delta_n(\mu) \le C \beta_3(\mu) / \sqrt{n}$ for every integer $n \ge 1$ and every probability
measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute moment. This
is the proposition that $C_0 \le 0.5129$.

Source: catalogue C19a, upper row KS2009; retained Shevtsova2011 lines 141-148. -/
def korolevShevtsova2009UpperBound : Prop := value ≤ (5129 / 10000 : ℝ)

/-- **Statement of Tyurin's Berry–Esseen bound.** The proposition that the Berry–Esseen
constant $C_0$ is at most $0.4785$. Here $C_0$ is the infimum of the real numbers $C$ such that
for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third
absolute moment $\beta_3 = \int |x|^3 \, d\mu(x)$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, where $X_1, \dots, X_n$ are independent with
law $\mu$, satisfies $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le C \beta_3 / \sqrt{n}$; here
$\Phi$ is the standard normal distribution function.

Source: catalogue C19a, upper row Tyu2009; retained Shevtsova2011 lines 150-154. -/
def tyurin2009UpperBound : Prop := value ≤ (4785 / 10000 : ℝ)

/-- **Statement of Shevtsova's 2011 Berry–Esseen bound.** Let $C_0$ be the infimum of all
real $C$ such that for every real probability law $\mu$ with mean $0$, variance $1$ and finite
third absolute moment $\rho = \int |x|^3\,d\mu$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, for independent $X_1, \dots, X_n$ with law
$\mu$, satisfies $\sup_x |F_n(x) - \Phi(x)| \le C \rho / \sqrt{n}$, where $\Phi$ is the
standard normal distribution function. This is the proposition $C_0 \le 0.4748$.

Source: catalogue C19a, upper row She2011; retained arXiv1111.6554 Corollary 1. -/
def shevtsova2011UpperBound : Prop := value ≤ (4748 / 10000 : ℝ)

/-- **Statement of Shevtsova's 2013 Berry–Esseen bound.** Let $C_0$ be the infimum of all
real $C$ such that for every real probability law $\mu$ with mean $0$, variance $1$ and finite
third absolute moment $\rho = \int |x|^3\,d\mu$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, for independent $X_1, \dots, X_n$ with law
$\mu$, satisfies $\sup_x |F_n(x) - \Phi(x)| \le C \rho / \sqrt{n}$, where $\Phi$ is the
standard normal distribution function. This is the proposition $C_0 \le 0.4690$.

Source: catalogue C19a, upper row She2013. The original primary text and the
correct structural formula remain unresolved; this is only the literal bound request. -/
def shevtsova2013UpperBound : Prop := value ≤ (4690 / 10000 : ℝ)

/-- **Statement of the unverified Berry–Esseen bound 0.4395.** The proposition that the Berry–Esseen
constant $C_0$ is at most $0.4395$. Here $C_0$ is the infimum of the real numbers $C$ such that
for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third
absolute moment $\beta_3 = \int |x|^3 \, d\mu(x)$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, where $X_1, \dots, X_n$ are independent with
law $\mu$, satisfies $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le C \beta_3 / \sqrt{n}$; here
$\Phi$ is the standard normal distribution function.

Source: catalogue C19a, upper row XL2026, explicitly unverified. No external
repository certificate or compiler-trusting proof is accepted by this request. -/
def xiaoLi2026UnverifiedUpperBound : Prop := value ≤ (4395 / 10000 : ℝ)

/-- **Statement of Lin's 2026 Berry–Esseen bound.** Let $C_0$ be the infimum of all
real $C$ such that for every real probability law $\mu$ with mean $0$, variance $1$ and finite
third absolute moment $\rho = \int |x|^3\,d\mu$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, for independent $X_1, \dots, X_n$ with law
$\mu$, satisfies $\sup_x |F_n(x) - \Phi(x)| \le C \rho / \sqrt{n}$, where $\Phi$ is the
standard normal distribution function. This is the proposition $C_0 \le 0.423$.

Source: catalogue C19a, upper row Lin2026, explicitly unverified. No external
repository certificate or comparator result is asserted here. -/
def lin2026UnverifiedUpperBound : Prop := value ≤ (423 / 1000 : ℝ)

/-- **Statement of the Korolev–Shevtsova structural Berry–Esseen bound.** For a probability
measure $\mu$ on $\mathbb{R}$ and an integer $n \ge 1$, let $F_n$ be the distribution function of
$(X_1 + \dots + X_n)/\sqrt{n}$ for independent random variables $X_1, X_2, \dots$ each with law
$\mu$, let $\Delta_n(\mu) = \sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$, where $\Phi$ is the
standard normal distribution function, and let $\beta_3(\mu) = \int |x|^3 \, d\mu$. This is the
proposition that for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$
and finite third absolute moment and every integer $n \ge 1$,
$$\Delta_n(\mu) \le \frac{0.34445\,(\beta_3(\mu) + 0.489)}{\sqrt{n}}.$$

Source: catalogue C19a, KS2009 upper-row comment, and the exact retained
Shevtsova2011 quotation at lines 141-148. The additive offset is 0.489, not 0.429. -/
def korolevShevtsova2009Structural : Prop :=
  ∀ μ : Measure ℝ, IsStandardizedLaw μ → ∀ n : ℕ+,
    kolmogorovError μ n ≤ (34445 / 100000 : ℝ) *
      (thirdMoment μ + 489 / 1000) / Real.sqrt (n.1 : ℝ)

/-- **Statement of Esseen's lower bound for the Berry–Esseen constant.** For a probability measure
$\mu$ on $\mathbb{R}$ and an integer $n \ge 1$, let $F_n$ be the distribution function of
$(X_1 + \dots + X_n)/\sqrt{n}$ for independent random variables $X_1, X_2, \dots$ each with law
$\mu$, let $\Delta_n(\mu) = \sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$, where $\Phi$ is the
standard normal distribution function, and let $\beta_3(\mu) = \int |x|^3 \, d\mu$. Let $C_0$ be
the optimal i.i.d. Berry–Esseen constant, the infimum of all real $C$ such that
$\Delta_n(\mu) \le C \beta_3(\mu) / \sqrt{n}$ for every integer $n \ge 1$ and every probability
measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute moment. This
is the proposition that $(\sqrt{10} + 3)/(6\sqrt{2\pi}) \le C_0$.

Source: catalogue C19a, lower row E1956, and retained Shevtsova2011 lines
185-194. The symbolic endpoint is not replaced by its decimal approximation. -/
def esseen1956LowerBound : Prop := esseenConstant ≤ value

/-- **Statement of Esseen's asymptotic lower bound for a two-point law.** For a probability
measure $\mu$ on $\mathbb{R}$ and an integer $n \ge 1$, let $F_n$ be the distribution function of
$(X_1 + \dots + X_n)/\sqrt{n}$ for independent random variables $X_1, X_2, \dots$ each with law
$\mu$, let $\Delta_n(\mu) = \sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$, where $\Phi$ is the
standard normal distribution function, let $\beta_3(\mu) = \int |x|^3 \, d\mu$, and let
$C_E = (\sqrt{10} + 3)/(6\sqrt{2\pi})$. This is the proposition that there is a probability
measure $\mu$ on $\mathbb{R}$ with mean $0$ and variance $1$ that is concentrated on two distinct
points, such that for every real $\varepsilon > 0$ and every $N \in \mathbb{N}$ there is a positive
integer $n \ge N$ with
$$\Delta_n(\mu) \ge \frac{(C_E - \varepsilon)\,\beta_3(\mu)}{\sqrt{n}}.$$

Source: catalogue C19a, lower-row Bernoulli asymptotic comment. A single
actual standardized two-point law is chosen before epsilon and the sample-size
threshold. Its normalized sums approach the lower coefficient along arbitrarily
large sample sizes; an original Esseen primary comparison remains a source gap. -/
def esseenBernoulliAsymptoticLowerBound : Prop :=
  ∃ μ : Measure ℝ, IsBernoulliLaw μ ∧ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ n : ℕ+, N ≤ n.1 ∧
      (esseenConstant - ε) * thirdMoment μ / Real.sqrt (n.1 : ℝ) ≤ kolmogorovError μ n

/-- **Statement of Schulz's Bernoulli Berry–Esseen optimum.** Let $C_B$ be the infimum of all
real $C$ such that for every real probability law $\mu$ with mean $0$, variance $1$ and finite
third absolute moment $\rho = \int |x|^3\,d\mu$ that is concentrated on two points, that is,
$\mu(\mathbb{R} \setminus \{a, b\}) = 0$ for some reals $a \ne b$, and every integer $n \ge 1$,
the distribution function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, for independent
$X_1, \dots, X_n$ with law $\mu$, satisfies $\sup_x |F_n(x) - \Phi(x)| \le C \rho / \sqrt{n}$,
where $\Phi$ is the standard normal distribution function. This is the proposition
$C_B = (\sqrt{10} + 3)/(6\sqrt{2\pi})$.

Source: catalogue C19a, Bernoulli/binomial comment and Sch2016 reference.
The actual subclass consists of centered variance-one two-point laws. The full
Schulz primary proof has not been acquired or verified in this lane. -/
def schulz2016BernoulliOptimum : Prop := bernoulliValue = esseenConstant

/-- **Statement of the Kolmogorov distance via left-continuous distribution functions.** This is
the proposition that for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance
$1$ and finite third absolute moment and every integer $n \ge 1$, if $S_n = X_1 + \dots + X_n$ for
independent random variables $X_1, X_2, \dots$ each with law $\mu$, then
$$
\sup_{x \in \mathbb{R}} \bigl|P(S_n/\sqrt{n} < x) - \Phi(x)\bigr|
= \sup_{x \in \mathbb{R}} \bigl|P(S_n/\sqrt{n} \le x) - \Phi(x)\bigr|,
$$
where $\Phi$ is the standard normal distribution function.

Source: the right-CDF catalogue definition and retained Shevtsova2011
lines 104-108, which explicitly use a left-continuous CDF. This probability
bridge is requested, not inferred by replacing strict with non-strict events. -/
def leftRightCDFErrorEquivalence : Prop :=
  ∀ μ : Measure ℝ, IsStandardizedLaw μ → ∀ n : ℕ+,
    sSup (Set.range (fun x : ℝ ↦
      |(normalizedLaw μ n).real (Set.Iio x) - normalCDF x|)) = kolmogorovError μ n

/-- **Zolotarev's upper bound for the Berry–Esseen constant.** The Berry–Esseen constant $C_0$ is
at most $0.82$. Here $C_0$ is the infimum of the real numbers $C$ such that for every
probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute
moment $\beta_3 = \int |x|^3 \, d\mu(x)$, and every integer $n \ge 1$, the distribution function
$F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, where $X_1, \dots, X_n$ are independent with law $\mu$,
satisfies $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le C \beta_3 / \sqrt{n}$; here $\Phi$ is
the standard normal distribution function.

Source: catalogue C19a, Z1967 upper row. -/
theorem_wanted zolotarev1967UpperBound_holds : zolotarev1967UpperBound

/-- **Van Beek's upper bound for the Berry–Esseen constant.** The Berry–Esseen constant $C_0$ is
at most $0.7975$. Here $C_0$ is the infimum of the real numbers $C$ such that for every
probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute
moment $\beta_3 = \int |x|^3 \, d\mu(x)$, and every integer $n \ge 1$, the distribution function
$F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, where $X_1, \dots, X_n$ are independent with law $\mu$,
satisfies $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le C \beta_3 / \sqrt{n}$; here $\Phi$ is
the standard normal distribution function.

Source: catalogue C19a, vB1972 upper row. -/
theorem_wanted vanBeek1972UpperBound_holds : vanBeek1972UpperBound

/-- **Shiganov's upper bound for the Berry–Esseen constant.** The Berry–Esseen constant $C_0$ is
at most $0.7655$. Here $C_0$ is the infimum of the real numbers $C$ such that for every
probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute
moment $\beta_3 = \int |x|^3 \, d\mu(x)$, and every integer $n \ge 1$, the distribution function
$F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, where $X_1, \dots, X_n$ are independent with law $\mu$,
satisfies $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le C \beta_3 / \sqrt{n}$; here $\Phi$ is
the standard normal distribution function.

Source: catalogue C19a, Shi1986 upper row. -/
theorem_wanted shiganov1986UpperBound_holds : shiganov1986UpperBound

/-- **Shevtsova's 2006 Berry–Esseen bound.** Let $C_0$ be the infimum of all
real $C$ such that for every real probability law $\mu$ with mean $0$, variance $1$ and finite
third absolute moment $\rho = \int |x|^3\,d\mu$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, for independent $X_1, \dots, X_n$ with law
$\mu$, satisfies $\sup_x |F_n(x) - \Phi(x)| \le C \rho / \sqrt{n}$, where $\Phi$ is the
standard normal distribution function. Then $C_0 \le 0.7056$.

Source: catalogue C19a, She2006 upper row. -/
theorem_wanted shevtsova2006UpperBound_holds : shevtsova2006UpperBound

/-- **Korolev–Shevtsova upper bound for the Berry–Esseen constant.** For a probability measure
$\mu$ on $\mathbb{R}$ and an integer $n \ge 1$, let $F_n$ be the distribution function of
$(X_1 + \dots + X_n)/\sqrt{n}$ for independent random variables $X_1, X_2, \dots$ each with law
$\mu$, let $\Delta_n(\mu) = \sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$, where $\Phi$ is the
standard normal distribution function, and let $\beta_3(\mu) = \int |x|^3 \, d\mu$. Let $C_0$ be
the optimal i.i.d. Berry–Esseen constant, the infimum of all real $C$ such that
$\Delta_n(\mu) \le C \beta_3(\mu) / \sqrt{n}$ for every integer $n \ge 1$ and every probability
measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute moment. Then
$C_0 \le 0.5129$.

Source: catalogue C19a, KS2009 upper row; retained Shevtsova2011 quotation. -/
theorem_wanted korolevShevtsova2009UpperBound_holds : korolevShevtsova2009UpperBound

/-- **Tyurin's upper bound for the Berry–Esseen constant.** The Berry–Esseen constant $C_0$ is
at most $0.4785$. Here $C_0$ is the infimum of the real numbers $C$ such that for every
probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute
moment $\beta_3 = \int |x|^3 \, d\mu(x)$, and every integer $n \ge 1$, the distribution function
$F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, where $X_1, \dots, X_n$ are independent with law $\mu$,
satisfies $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le C \beta_3 / \sqrt{n}$; here $\Phi$ is
the standard normal distribution function.

Source: catalogue C19a, Tyu2009 upper row. -/
theorem_wanted tyurin2009UpperBound_holds : tyurin2009UpperBound

/-- **Shevtsova's 2011 Berry–Esseen bound.** Let $C_0$ be the infimum of all
real $C$ such that for every real probability law $\mu$ with mean $0$, variance $1$ and finite
third absolute moment $\rho = \int |x|^3\,d\mu$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, for independent $X_1, \dots, X_n$ with law
$\mu$, satisfies $\sup_x |F_n(x) - \Phi(x)| \le C \rho / \sqrt{n}$, where $\Phi$ is the
standard normal distribution function. Then $C_0 \le 0.4748$.

Source: catalogue C19a, She2011 upper row; retained primary Corollary 1. -/
theorem_wanted shevtsova2011UpperBound_holds : shevtsova2011UpperBound

/-- **Shevtsova's 2013 Berry–Esseen bound.** Let $C_0$ be the infimum of all
real $C$ such that for every real probability law $\mu$ with mean $0$, variance $1$ and finite
third absolute moment $\rho = \int |x|^3\,d\mu$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, for independent $X_1, \dots, X_n$ with law
$\mu$, satisfies $\sup_x |F_n(x) - \Phi(x)| \le C \rho / \sqrt{n}$, where $\Phi$ is the
standard normal distribution function. Then $C_0 \le 0.4690$.

Source: catalogue C19a, She2013 upper row; the primary correction is unresolved. -/
theorem_wanted shevtsova2013UpperBound_holds : shevtsova2013UpperBound

/-- **The unverified upper bound 0.4395 for the Berry–Esseen constant.** The Berry–Esseen
constant $C_0$ is at most $0.4395$. Here $C_0$ is the infimum of the real numbers $C$ such that
for every probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third
absolute moment $\beta_3 = \int |x|^3 \, d\mu(x)$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, where $X_1, \dots, X_n$ are independent with
law $\mu$, satisfies $\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le C \beta_3 / \sqrt{n}$; here
$\Phi$ is the standard normal distribution function.

Source: catalogue C19a, explicitly unverified XL2026 row. -/
theorem_wanted xiaoLi2026UnverifiedUpperBound_holds : xiaoLi2026UnverifiedUpperBound

/-- **Lin's 2026 Berry–Esseen bound.** Let $C_0$ be the infimum of all
real $C$ such that for every real probability law $\mu$ with mean $0$, variance $1$ and finite
third absolute moment $\rho = \int |x|^3\,d\mu$, and every integer $n \ge 1$, the distribution
function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, for independent $X_1, \dots, X_n$ with law
$\mu$, satisfies $\sup_x |F_n(x) - \Phi(x)| \le C \rho / \sqrt{n}$, where $\Phi$ is the
standard normal distribution function. Then $C_0 \le 0.423$.

Source: catalogue C19a, explicitly unverified Lin2026 row. -/
theorem_wanted lin2026UnverifiedUpperBound_holds : lin2026UnverifiedUpperBound

/-- **Korolev–Shevtsova structural Berry–Esseen bound.** For a probability measure $\mu$ on
$\mathbb{R}$ and an integer $n \ge 1$, let $F_n$ be the distribution function of
$(X_1 + \dots + X_n)/\sqrt{n}$ for independent random variables $X_1, X_2, \dots$ each with law
$\mu$, let $\Delta_n(\mu) = \sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$, where $\Phi$ is the
standard normal distribution function, and let $\beta_3(\mu) = \int |x|^3 \, d\mu$. Then for every
probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute
moment and every integer $n \ge 1$,
$$\Delta_n(\mu) \le \frac{0.34445\,(\beta_3(\mu) + 0.489)}{\sqrt{n}}.$$

Source: catalogue C19a, KS2009 structural comment; retained 2011 equation. -/
theorem_wanted korolevShevtsova2009Structural_holds : korolevShevtsova2009Structural

/-- **Esseen's lower bound for the Berry–Esseen constant.** For a probability measure
$\mu$ on $\mathbb{R}$ and an integer $n \ge 1$, let $F_n$ be the distribution function of
$(X_1 + \dots + X_n)/\sqrt{n}$ for independent random variables $X_1, X_2, \dots$ each with law
$\mu$, let $\Delta_n(\mu) = \sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$, where $\Phi$ is the
standard normal distribution function, and let $\beta_3(\mu) = \int |x|^3 \, d\mu$. Let $C_0$ be
the optimal i.i.d. Berry–Esseen constant, the infimum of all real $C$ such that
$\Delta_n(\mu) \le C \beta_3(\mu) / \sqrt{n}$ for every integer $n \ge 1$ and every probability
measure $\mu$ on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute moment. Then
$(\sqrt{10} + 3)/(6\sqrt{2\pi}) \le C_0$.

Source: catalogue C19a, E1956 lower row; retained 2011 exact benchmark. -/
theorem_wanted esseen1956LowerBound_holds : esseen1956LowerBound

/-- **Esseen's asymptotic lower bound for a two-point law.** For a probability measure $\mu$ on
$\mathbb{R}$ and an integer $n \ge 1$, let $F_n$ be the distribution function of
$(X_1 + \dots + X_n)/\sqrt{n}$ for independent random variables $X_1, X_2, \dots$ each with law
$\mu$, let $\Delta_n(\mu) = \sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)|$, where $\Phi$ is the
standard normal distribution function, let $\beta_3(\mu) = \int |x|^3 \, d\mu$, and let
$C_E = (\sqrt{10} + 3)/(6\sqrt{2\pi})$. There is a probability measure $\mu$ on $\mathbb{R}$ with
mean $0$ and variance $1$ that is concentrated on two distinct points, such that for every real
$\varepsilon > 0$ and every $N \in \mathbb{N}$ there is a positive integer $n \ge N$ with
$$\Delta_n(\mu) \ge \frac{(C_E - \varepsilon)\,\beta_3(\mu)}{\sqrt{n}}.$$

In other words, $\limsup_{n \to \infty} \sqrt{n}\,\Delta_n(\mu) / \beta_3(\mu) \ge C_E$.

Source: catalogue C19a, the asymptotic normalized Bernoulli lower-row clause. -/
theorem_wanted esseenBernoulliAsymptoticLowerBound_holds : esseenBernoulliAsymptoticLowerBound

/-- **Schulz's Bernoulli Berry–Esseen optimum.** Let $C_B$ be the infimum of all
real $C$ such that for every real probability law $\mu$ with mean $0$, variance $1$ and finite
third absolute moment $\rho = \int |x|^3\,d\mu$ that is concentrated on two points, that is,
$\mu(\mathbb{R} \setminus \{a, b\}) = 0$ for some reals $a \ne b$, and every integer $n \ge 1$,
the distribution function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, for independent
$X_1, \dots, X_n$ with law $\mu$, satisfies $\sup_x |F_n(x) - \Phi(x)| \le C \rho / \sqrt{n}$,
where $\Phi$ is the standard normal distribution function. Then
$C_B = (\sqrt{10} + 3)/(6\sqrt{2\pi})$.

Source: catalogue C19a, Bernoulli/binomial comment, Schulz2016. -/
theorem_wanted schulz2016BernoulliOptimum_holds : schulz2016BernoulliOptimum

/-- **Kolmogorov distance via left-continuous distribution functions.** Let $\mu$ be a probability
measure on $\mathbb{R}$ with mean $0$, variance $1$ and finite third absolute moment, let $n \ge 1$
be an integer, and let $S_n = X_1 + \dots + X_n$ for independent random variables $X_1, X_2, \dots$
each with law $\mu$. Then
$$
\sup_{x \in \mathbb{R}} \bigl|P(S_n/\sqrt{n} < x) - \Phi(x)\bigr|
= \sup_{x \in \mathbb{R}} \bigl|P(S_n/\sqrt{n} \le x) - \Phi(x)\bigr|,
$$
where $\Phi$ is the standard normal distribution function.

Source: catalogue C19a right CDF and Shevtsova2011's explicit left convention. -/
theorem_wanted leftRightCDFErrorEquivalence_holds : leftRightCDFErrorEquivalence

end BerryEsseenWanted
