/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Order.Filter.AtTopBot.Basic
public import MathlibExt.NumberTheory.LcmDenseSets

namespace MetaMathlibExt

@[expose] public section

open Filter

/-- **Dense sets with unusually large least common multiples.** Let $\operatorname{Log}_2$ and
$\operatorname{Log}_3$ be the second and third iterated truncated logarithms. For a set $A$ of
natural numbers and real $x$, write $S_A(x) = \sum_{n \in A,\ 1 \le n \le x} 1/n$, and write
$L_A(x)$ for the sum of $1/\operatorname{lcm}(n, m)$ over all ordered pairs $(n, m)$ with
$n, m \in A$, $1 \le n \le x$ and $1 \le m \le x$. Then for every real $C_0 > 0$ there is a set
$A$ of natural numbers with the following two properties. First, there is a function
$\varepsilon : \mathbb{R} \to \mathbb{R}$ with $\varepsilon(x) \to 0$ as $x \to \infty$ such that
for all sufficiently large real $x$,
$S_A(x) = \exp((C_0/2 + \varepsilon(x))(\operatorname{Log}_2 x)^{1/2} \operatorname{Log}_3 x)$.
Second, there is a constant $K > 0$ such that $L_A(x) \le K\, S_A(x)^2$ for all sufficiently
large real $x$.

The source presents this as a negative answer to Erdős problem #442. Its accompanying claim that
the exponent is optimal is made precise by Theorem 2(ii) and is stated separately.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Theorem 1.
-/
public theorem_wanted exists_dense_set_large_lcm :
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ A : Set ℕ,
        (∃ e : ℝ → ℝ,
          Tendsto e atTop (nhds 0) ∧
          ∀ᶠ x in atTop,
            recipSumUpTo A x =
              Real.exp ((C₀ / 2 + e x) *
                truncLog2 x ^ (1 / 2 : ℝ) * truncLog3 x)) ∧
        ∃ K : ℝ, 0 < K ∧
          ∀ᶠ x in atTop,
            lcmReciprocalSum A x ≤ K * recipSumUpTo A x ^ 2

/-- **Dense sets with controlled gcd defect.** Let $e$ be Euler's number. There is an absolute
constant $C > 0$ with the following property. Let $C_0 > 0$ be real, and let $F_{C_0}$ be the
growth function of the dense-set construction. Then there is a set $A$ of natural numbers such
that, writing $S_A(x) = \sum_{n \in A,\ 1 \le n \le x} 1/n$ for its harmonic sum up to $x$ and
$\mathcal{E}_A(x)$ for its gcd defect up to $x$, the following two statements hold. First, there
is a constant $K > 0$ with $F_{C_0}(x)/K \le S_A(x) \le K\, F_{C_0}(x)$ for all sufficiently large
real $x$. Second, there is a function $\varepsilon : \mathbb{R} \to \mathbb{R}$ with
$\varepsilon(x) \to 0$ as $x \to \infty$ such that
$\mathcal{E}_A(x) \le C\,(\exp(e^2 C_0^2) - 1 + \varepsilon(x))$ for all sufficiently large
real $x$.

The factor $e^2$ follows the journal version of the source; the arXiv preprint prints
$\exp(C_0^2)$, but its proof, through the factor $e^\ell$ of (35), gives $e^2 C_0^2$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Theorem 2(i).
-/
public theorem_wanted exists_dense_set_controlled_defect :
    ∃ C : ℝ, 0 < C ∧
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ A : Set ℕ,
        (∃ K : ℝ, 0 < K ∧
          ∀ᶠ x in atTop,
            lcmDenseGrowthF C₀ x / K ≤ recipSumUpTo A x ∧
            recipSumUpTo A x ≤ K * lcmDenseGrowthF C₀ x) ∧
        ∃ e : ℝ → ℝ,
          Tendsto e atTop (nhds 0) ∧
          ∀ᶠ x in atTop,
            lcmDefect A x ≤ C * (Real.exp (Real.exp 2 * C₀ ^ 2) - 1 + e x)

/-- **Baby version of the dense-set construction.** Let $e$ be Euler's number, let
$\operatorname{Log}_2$ and $\operatorname{Log}_3$ be the second and third iterated truncated
logarithms, and for a set $B$ of natural numbers and real $x$ write
$S_B(x) = \sum_{n \in B,\ 1 \le n \le x} 1/n$ and $\mathcal{E}_B(x)$ for the gcd defect of $B$ up
to $x$. There is an absolute constant $C > 0$ such that for every real $C_0 > 0$ there are sets
$A_0, A_1, A_2, \dots$ of natural numbers with the following property: for every $\varepsilon > 0$
there are a real $\delta > 0$ and a natural number $k_0$ such that for every natural number
$k \ge k_0$ and every real $x$ with $|C_0 (\operatorname{Log}_2 x)^{1/2} - k| \le \delta k$, there
is a real $\eta$ with $|\eta| \le \varepsilon$ and
$S_{A_k}(x) = \exp((C_0/2 + \eta)(\operatorname{Log}_2 x)^{1/2} \operatorname{Log}_3 x)$, and
moreover $\mathcal{E}_{A_k}(x) \le C(\exp(e^2 C_0^2) - 1 + \varepsilon)$.

In the source this is Proposition 1, a simplified version of the construction for Theorem 2(i)
(its lead-in sentence refers to Theorem 2(ii)): the sets $A_k$ satisfy (31) and the bound (21)
in the range (32), with all $o(1)$ terms taken as $k \to \infty$. Above, these $o(1)$ terms are
written with $\varepsilon$, $\delta$ and $k_0$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Proposition 1, (31) and (32), with (21)
(`integers-2024-A100-prop-1`).
-/
public theorem_wanted exists_dense_sets_baby :
    ∃ C : ℝ, 0 < C ∧
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ A : ℕ → Set ℕ,
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x : ℝ,
            |C₀ * truncLog2 x ^ (1 / 2 : ℝ) - k| ≤ δ * k →
              (∃ e : ℝ, |e| ≤ ε ∧
                recipSumUpTo (A k) x =
                  Real.exp ((C₀ / 2 + e) * truncLog2 x ^ (1 / 2 : ℝ) * truncLog3 x)) ∧
              lcmDefect (A k) x ≤ C * (Real.exp (Real.exp 2 * C₀ ^ 2) - 1 + ε)

/-- **Harmonic sums of sets with small gcd defect.** For a set $A$ of natural numbers and a real
number $x$, let $S_A(x)$ be the sum of $1/n$ over $n \in A$ with $1 \le n \le x$, and let the
defect of $A$ at $x$ be the sum of $\gcd(n, m)/(nm)$ over $n, m \in A$ with $1 \le n, m \le x$,
divided by $S_A(x)^2$, minus $1$ (the defect is $-1$ when $S_A(x) = 0$). Let
$\operatorname{Log} x = \max(\log x, 1)$ be the truncated logarithm, let
$\operatorname{Log}_2 x = \operatorname{Log}(\operatorname{Log} x)$ and let
$\operatorname{Log}_3 x = \operatorname{Log}(\operatorname{Log}_2 x)$. For every real
$C_0 > 0$ there are a function $e : \mathbb{R} \to \mathbb{R}$ with $e(x) \to 0$ as
$x \to \infty$ and a real $x_0$ such that for every real $x \ge x_0$ and every set $A$ of natural
numbers whose defect at $x$ is at most $C_0^2$,
$$S_A(x) \le \exp\bigl((C_0 + e(x)) (\operatorname{Log}_2 x)^{1/2} \operatorname{Log}_3 x\bigr).$$

The function $e$ and the threshold $x_0$ are chosen before $x$ and $A$, so the $o(1)$ error is
uniform in $A$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Theorem 2(ii).
-/
public theorem_wanted uniform_harmonic_bound_of_defect :
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ e : ℝ → ℝ,
        Tendsto e atTop (nhds 0) ∧
        ∀ᶠ x in atTop,
          ∀ A : Set ℕ,
            lcmDefect A x ≤ C₀ ^ 2 →
            recipSumUpTo A x ≤
              Real.exp ((C₀ + e x) *
                truncLog2 x ^ (1 / 2 : ℝ) * truncLog3 x)

end

end MetaMathlibExt
