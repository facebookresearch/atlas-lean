/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.PrimeDistribution
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polymath8b's concrete dyadic distribution assumptions

This is the retained arXiv:1407.4897v4 formulation. The separately published 2015
erratum correction text is unavailable, so its applicability is unresolved.
These predicates are source assumptions for private proof requests, not assumed
theorems. No equivalence to the distinct cumulative C66 predicate is asserted.
All non-fixed source quantities vary with the real parameter `x`; constants,
exponents and thresholds in eventual estimates are independent of `x`.
-/

@[expose] public section

namespace WantedExt.NumberTheory.Polymath8b

open Filter MathlibExt.NumberTheory.PrimeDistribution

/-- **Subpower bound.** For functions $f, g : \mathbb{R} \to \mathbb{R}$, $f$ is bounded by $g$ up
to subpower losses if for every real $\delta > 0$ we have $f(x) = O(x^{\delta} g(x))$ as
$x \to \infty$.

Source: Polymath8b, arXiv:1407.4897v4, Definition 1.6. -/
def SubpowerBound (f g : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → Asymptotics.IsBigO atTop f (fun x ↦ x ^ δ * g x)

/-- **Support in a dyadic interval.** A finitely supported sequence
$\alpha : \mathbb{N} \to \mathbb{R}$ is supported in the dyadic interval at scale
$N \in \mathbb{R}$ if every $n$ with $\alpha(n) \ne 0$ satisfies $n \ge 1$ and $N \le n \le 2N$.

Source: Polymath8b v4, Claim 2.6. -/
def DyadicSupport (α : ℕ →₀ ℝ) (N : ℝ) : Prop :=
  ∀ n ∈ α.support, 1 ≤ n ∧ N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N

/-- **Divisor–logarithm bound for a family of sequences.** A family $(\alpha_x)_{x \in \mathbb{R}}$
of finitely supported sequences $\alpha_x : \mathbb{N} \to \mathbb{R}$ satisfies the
divisor–logarithm bound if there are a real number $C > 0$ and natural numbers $k$ and $l$ such
that for all sufficiently large real $x$ and all integers $n \ge 1$,
$$|\alpha_x(n)| \le C \, \tau(n)^k (\log x)^l,$$
where $\tau(n)$ is the number of positive divisors of $n$. The constants $C$, $k$ and $l$ depend
neither on $x$ nor on $n$.

Source: Polymath8b v4, Claim 2.6, TeX label `ab-div`. -/
def DivisorLogBound (α : ℝ → ℕ →₀ ℝ) : Prop :=
  ∃ C : ℝ, ∃ k l : ℕ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ n : ℕ, 1 ≤ n → |α x n| ≤
      C * (n.divisors.card : ℝ) ^ k * Real.log x ^ l

/-- **Siegel–Walfisz hypothesis for a family of sequences.** Let $(\beta_x)_{x \in \mathbb{R}}$
be a family of finitely supported sequences $\beta_x : \mathbb{N} \to \mathbb{R}$ and let
$M : \mathbb{R} \to \mathbb{R}$. The family satisfies the Siegel–Walfisz hypothesis at scale $M$
if for every real $A \ge 1$ there are a real number $C > 0$ and a natural number $k$ such that,
for all sufficiently large real $x$ and all natural numbers $q \ge 1$, $r \ge 1$ and $a$ with
$\gcd(a, q) = 1$,
$$|\Delta(\beta_x^{(r)}; a \bmod q)| \le C \, \tau(qr)^k \, M(x) / (\log x)^A.$$
Here $\beta_x^{(r)}$ is the sequence equal to $\beta_x(n)$ when $\gcd(n, r) = 1$ and to $0$
otherwise, $\Delta(\cdot\,; a \bmod q)$ is the discrepancy in the residue class of $a$ modulo $q$,
and $\tau(m)$ is the number of positive divisors of $m$.

Source: Polymath8b v4, Claim 2.6, TeX label `sig` and its uniformity footnote. -/
def SiegelWalfisz (β : ℝ → ℕ →₀ ℝ) (M : ℝ → ℝ) : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∃ k : ℕ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ q r a : ℕ, (h1q : 1 ≤ q) → 1 ≤ r → Nat.Coprime a q →
      |discrepancy ((β x).filter (fun n ↦ Nat.Coprime n r)) ⟨q, h1q⟩ a| ≤
        C * ((q * r).divisors.card : ℝ) ^ k * M x / Real.log x ^ A

/-- **Elliott–Halberstam estimate at level $\theta$.** For a real number $\theta$, the
Elliott–Halberstam estimate at level $\theta$ is the following statement. Let
$Q : \mathbb{R} \to \mathbb{N}$ be such that $Q(x) = O(x^{\delta} x^{\theta})$ as $x \to \infty$
for every real $\delta > 0$, and let $A \ge 1$ be real. Then there is a real number $C > 0$ such
that for all sufficiently large real $x$, the averaged discrepancy of $\Lambda_x$ up to $Q(x)$ is
at most $C x / (\log x)^A$. Here $\Lambda_x$ is the sequence equal to the von Mangoldt function
$\Lambda(n)$ for integers $n \ge 1$ with $x \le n \le 2x$ and to $0$ otherwise, and the averaged
discrepancy of a sequence $\alpha$ up to $Q$ is $\sum_{q=1}^{Q} \Delta^*(\alpha; q)$, where
$\Delta^*(\alpha; q)$ is the largest absolute value of the discrepancy of $\alpha$ in a residue
class modulo $q$ coprime to $q$.

Source: Polymath8b v4, Claim 2.2. -/
def ElliottHalberstamAt (θ : ℝ) : Prop :=
  ∀ Q : ℝ → ℕ, SubpowerBound (fun x ↦ (Q x : ℝ)) (fun x ↦ x ^ θ) →
    ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      averagedDiscrepancy (dyadicVonMangoldt x) (Q x) ≤ C * x / Real.log x ^ A

/-- **Generalized Elliott–Halberstam estimate at level $\theta$.** For a real number $\theta$,
the generalized Elliott–Halberstam estimate at level $\theta$ is the following statement. Let
$\varepsilon > 0$ be real, let $N, M : \mathbb{R} \to \mathbb{R}$, and let
$(\alpha_x)_{x \in \mathbb{R}}$ and $(\beta_x)_{x \in \mathbb{R}}$ be families of finitely
supported sequences $\mathbb{N} \to \mathbb{R}$. Assume that for all sufficiently large real $x$
we have $N(x) > 0$ and $M(x) > 0$, $\alpha_x$ is supported in the dyadic interval at scale
$N(x)$ and $\beta_x$ is supported in the dyadic interval at scale $M(x)$; that for every real
$\delta > 0$, as $x \to \infty$, $x^{\varepsilon} = O(x^{\delta} N(x))$,
$N(x) = O(x^{\delta} x^{1 - \varepsilon})$, $x^{\varepsilon} = O(x^{\delta} M(x))$ and
$M(x) = O(x^{\delta} x^{1 - \varepsilon})$; that $N(x) M(x) = O(x)$ and $x = O(N(x) M(x))$ as
$x \to \infty$; that both families satisfy the divisor–logarithm bound; and that
$(\beta_x)$ satisfies the Siegel–Walfisz hypothesis at scale $M$. Let
$Q : \mathbb{R} \to \mathbb{N}$ be such that $Q(x) = O(x^{\delta} x^{\theta})$ as $x \to \infty$
for every real $\delta > 0$, and let $A \ge 1$ be real. Then there is a real number $C > 0$ such
that for all sufficiently large real $x$, the averaged discrepancy of the multiplicative
convolution $\alpha_x \star \beta_x$ up to $Q(x)$ is at most $C x / (\log x)^A$.

Source: Polymath8b v4, Claim 2.6, TeX labels `ab-div`, `sig`, and `qq-gen`. -/
def GeneralizedElliottHalberstamAt (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N M : ℝ → ℝ, ∀ α β : ℝ → ℕ →₀ ℝ,
    (∀ᶠ x : ℝ in atTop, 0 < N x ∧ 0 < M x ∧
      DyadicSupport (α x) (N x) ∧ DyadicSupport (β x) (M x)) →
    SubpowerBound (fun x ↦ x ^ ε) N →
    SubpowerBound N (fun x ↦ x ^ (1 - ε)) →
    SubpowerBound (fun x ↦ x ^ ε) M →
    SubpowerBound M (fun x ↦ x ^ (1 - ε)) →
    Asymptotics.IsTheta atTop (fun x ↦ N x * M x) (fun x ↦ x) →
    DivisorLogBound α → DivisorLogBound β → SiegelWalfisz β M →
    ∀ Q : ℝ → ℕ, SubpowerBound (fun x ↦ (Q x : ℝ)) (fun x ↦ x ^ θ) →
      ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
        averagedDiscrepancy (convolution (α x) (β x)) (Q x) ≤ C * x / Real.log x ^ A

/-- **Elliott–Halberstam conjecture (dyadic form).** The Elliott–Halberstam estimate at level
$\theta$ holds for every real number $\theta$ with $0 < \theta < 1$.

Source: Polymath8b v4, Theorems 1.1 and 1.3 and Claim 2.2. -/
def ElliottHalberstam : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ElliottHalberstamAt θ

/-- **Generalized Elliott–Halberstam conjecture (dyadic form).** The generalized
Elliott–Halberstam estimate at level $\theta$ holds for every real number $\theta$ with
$0 < \theta < 1$.

Source: Polymath8b v4, Theorem 1.4 and Claim 2.6. -/
def GeneralizedElliottHalberstam : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → GeneralizedElliottHalberstamAt θ

end WantedExt.NumberTheory.Polymath8b
