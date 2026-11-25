/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.GeneralizedFibonacciZeta
public import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace MetaMathlibExt

@[expose] public section

open Filter
open scoped BigOperators Topology

/-- **Meromorphic continuation of the ℓ-generalized Fibonacci zeta function.** Let $\ell \ge 2$,
let $F$ be an $\ell$-generalized Fibonacci sequence, let $\alpha > 1$ be a real number with
$\alpha^\ell = \sum_{i=0}^{\ell-1} \alpha^i$, and let $S$ be the set of possible poles determined
by $\ell$ and $\alpha$. Then there is a function $f : \mathbb{C} \to \mathbb{C}$ such that
$f(s) = \sum_{n \ge 1} F(n)^{-s}$ for every complex $s$ with $\operatorname{Re} s > 0$, $f$ is
complex differentiable at every point outside $S$, and for every $s_0 \in S$ the limit of
$(s - s_0) f(s)$ as $s \to s_0$ with $s \ne s_0$ exists in $\mathbb{C}$.

The last clause says that $f$ has at most simple poles, all lying in $S$; the residues are
stated separately.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public theorem_wanted lGeneralizedFibonacciZeta_meromorphicContinuation
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : ℤ → ℤ)
    (hF : IsLGeneralizedFibonacci ℓ F) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i) :
    ∃ f : ℂ → ℂ,
      (∀ s : ℂ, 0 < s.re →
        f s = ∑' j : ℕ, ((F ((j : ℤ) + 1) : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, s ∉ lGeneralizedFibonacciZetaPoleSet ℓ α →
        DifferentiableAt ℂ f s) ∧
      ∀ s₀ : ℂ, s₀ ∈ lGeneralizedFibonacciZetaPoleSet ℓ α →
        ∃ r : ℂ,
          Tendsto (fun s : ℂ => (s - s₀) * f s) (𝓝[≠] s₀) (𝓝 r)

/-- **Residues of the ℓ-generalized Fibonacci zeta function.** Let $\ell \ge 2$, let $F$ be an
$\ell$-generalized Fibonacci sequence, and let $\alpha > 1$ be a real number with
$\alpha^\ell = \sum_{i<\ell} \alpha^i$. Let $R$ be the set of complex roots of
$X^\ell - \sum_{i<\ell} X^i$ other than $\alpha$, let $s_{\kappa,n}$ be the possible pole and
$\rho_{\kappa,n}$ the residue expression indexed by a function $\kappa$ from $\mathbb{C}$ to the
natural numbers and an integer $n$, and let $S$ be the set of all possible poles $s_{\kappa,n}$.
Fix $\kappa$ and $n$ such that whenever $s_{\kappa',n'} = s_{\kappa,n}$, we have $n' = n$ and
$\kappa'(\beta) = \kappa(\beta)$ for every $\beta \in R$. Let $f : \mathbb{C} \to \mathbb{C}$
satisfy $f(s) = \sum_{m \ge 1} F_m^{-s}$ (principal complex powers) for every $s$ with
$\operatorname{Re} s > 0$, and let $f$ be complex differentiable at every point outside $S$.
Then $(s - s_{\kappa,n}) f(s)$ tends to $\rho_{\kappa,n}$ as $s$ tends to $s_{\kappa,n}$ with
$s \ne s_{\kappa,n}$.

The hypothesis that $(\kappa, n)$ is the only index of its pole is not in the paper: when
different indices give the same pole, their residue contributions add up, a case the printed
formula does not address.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1
(residue formula). -/
public theorem_wanted lGeneralizedFibonacciZeta_residue
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : ℤ → ℤ)
    (hF : IsLGeneralizedFibonacci ℓ F) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i)
    (κ : ℂ → ℕ) (n : ℤ)
    (hunique : ∀ (κ' : ℂ → ℕ) (n' : ℤ),
      lGeneralizedFibonacciZetaPole ℓ α κ' n' =
          lGeneralizedFibonacciZetaPole ℓ α κ n →
        n' = n ∧
          ∀ β ∈ lGeneralizedFibonacciOtherRoots ℓ α, κ' β = κ β)
    (f : ℂ → ℂ)
    (hseries : ∀ s : ℂ, 0 < s.re →
      f s = ∑' j : ℕ, ((F ((j : ℤ) + 1) : ℂ) ^ (-s)))
    (hregular : ∀ s : ℂ, s ∉ lGeneralizedFibonacciZetaPoleSet ℓ α →
      DifferentiableAt ℂ f s) :
    Tendsto
      (fun s : ℂ =>
        (s - lGeneralizedFibonacciZetaPole ℓ α κ n) * f s)
      (𝓝[≠] lGeneralizedFibonacciZetaPole ℓ α κ n)
      (𝓝 (lGeneralizedFibonacciZetaResidue ℓ α κ n))

/-- **Explicit possible poles of the ℓ-generalized Fibonacci zeta function.** Let $\ell \ge 2$, let
$\alpha > 1$ be a real number with $\alpha^\ell = \sum_{i=0}^{\ell-1} \alpha^i$, and let $k$ be a
natural number divisible by $\ell - 1$; write $q = k/(\ell - 1)$. Then for every integer $n$, the
point $-(k + q) + i\pi(2n + q)/\log \alpha$ if $\ell$ is even, and $-(k + q) + 2\pi i n/\log \alpha$
if $\ell$ is odd, belongs to the set $S$ of possible poles of the $\ell$-generalized Fibonacci
zeta function determined by $\ell$ and $\alpha$.

A witnessing exponent tuple takes the constant value $q$ at every root of the characteristic
polynomial other than $\alpha$.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Corollary 1. -/
public theorem_wanted lGeneralizedFibonacciZeta_corollaryPole_mem
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i)
    (k : ℕ) (hk : ℓ - 1 ∣ k) (n : ℤ) :
    lGeneralizedFibonacciZetaCorollaryPole ℓ k α n ∈
      lGeneralizedFibonacciZetaPoleSet ℓ α

/-- **Rational values of the ℓ-generalized Fibonacci zeta function at negative integers.** Let
$\ell \ge 2$, let $F$ be an $\ell$-generalized Fibonacci sequence, let $\alpha > 1$ be a real
number with $\alpha^\ell = \sum_{i=0}^{\ell-1} \alpha^i$, and let $S$ be the set of possible
poles determined by $\ell$ and $\alpha$. Let $m$ be a positive integer and let
$f : \mathbb{C} \to \mathbb{C}$ be a function that satisfies $f(s) = \sum_{n \ge 1} F(n)^{-s}$
whenever $\operatorname{Re} s > 0$ and is complex differentiable at every point outside $S$. If
$f$ is complex differentiable at $-m$, then $f(-m)$ is a rational number.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 2. -/
public theorem_wanted lGeneralizedFibonacciZeta_negInt_rational
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : ℤ → ℤ)
    (hF : IsLGeneralizedFibonacci ℓ F) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i)
    (m : ℕ) (hm : 0 < m) (f : ℂ → ℂ)
    (hseries : ∀ s : ℂ, 0 < s.re →
      f s = ∑' j : ℕ, ((F ((j : ℤ) + 1) : ℂ) ^ (-s)))
    (hregular : ∀ s : ℂ, s ∉ lGeneralizedFibonacciZetaPoleSet ℓ α →
      DifferentiableAt ℂ f s)
    (hmregular : DifferentiableAt ℂ f (-(m : ℂ))) :
    ∃ q : ℚ, f (-(m : ℂ)) = (q : ℂ)

end

end MetaMathlibExt
