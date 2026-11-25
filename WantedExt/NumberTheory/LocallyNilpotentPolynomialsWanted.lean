/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LocallyNilpotentPolynomials

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **Infinitely many primes avoid $\gamma \alpha^n - \beta$.** Let $\alpha, \beta, \gamma$ be
nonzero integers such that $\beta \ne \gamma \alpha^k$ and $\beta \alpha^k \ne \gamma$ for every
natural number $k$, that is, $\beta / \gamma$ is not $\alpha^k$ for any integer $k$. Then there
are infinitely many primes $p$ such that $p$ divides none of the integers $\gamma \alpha^n - \beta$
with $n \ge 1$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Lemma 3.2. -/
public theorem_wanted infinite_primes_not_dvd_mul_pow_sub (α β γ : ℤ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hγ : γ ≠ 0) (h : ∀ k : ℕ, β ≠ γ * α ^ k ∧ β * α ^ k ≠ γ) :
    {p : ℕ | p.Prime ∧ ∀ n : ℕ, 0 < n → ¬ (p : ℤ) ∣ γ * α ^ n - β}.Infinite

/-- **Classification of locally nilpotent polynomials at $0$.** A polynomial $u \in \mathbb{Z}[x]$
of positive degree is locally nilpotent at $0$ if and only if it has one of the following forms:
$x + b$ with $b \in \mathbb{Z}$, $b \ne 0$; $ax + b$ with $a, b \in \mathbb{Z}$, $b \ne 0$, $a$
divisible by at least one prime, and every prime divisor of $a$ dividing $b$; $x\,p(x)$ with
$p \in \mathbb{Z}[x]$, $p \ne 0$; or $(x - a)p(x)$ with $a \in \mathbb{Z}$, $a \ne 0$, and
$p \in \mathbb{Z}[x]$ with $p(0) = -1$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Theorem 4.4. -/
public theorem_wanted locallyNilpotentAt_zero_classification :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 0 ∅} =
      {u | ∃ b : ℤ, b ≠ 0 ∧ u = X + C b} ∪
        {u | ∃ a b : ℤ, b ≠ 0 ∧ (∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a) ∧
          (∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b) ∧ u = C a * X + C b} ∪
        {u | ∃ p : ℤ[X], p ≠ 0 ∧ u = X * p} ∪
        {u | ∃ (a : ℤ) (p : ℤ[X]), a ≠ 0 ∧ p.eval 0 = -1 ∧ u = (X - C a) * p}

/-- **Linear polynomials weakly locally nilpotent but not nilpotent at $1$.** Let $A$ be a finite
set of primes, and let $c$ range over the positive integers all of whose prime factors lie in $A$.
A polynomial $u \in \mathbb{Z}[x]$ of degree $1$ is weakly locally nilpotent at $1$ outside $A$ and
not nilpotent at $1$ if and only if $u$ is one of: $x + c$; $x - c$ with $c \ne 1$; $cx + 1$ or
$-cx + 1$ with $c \ne 1$; or $-2x - 1$, the last only when $2 \in A$.

Writing $c = q_1^{s_1} \cdots q_k^{s_k}$ with the $q_i$ the primes of $A$, the condition $c \ne 1$
is the paper's $\sum s_i \ge 1$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Corollary 5.2. -/
public theorem_wanted linear_weaklyLocallyNilpotent_not_nilpotentAt_one (A : Finset ℕ)
    (hA : ∀ p ∈ A, p.Prime) :
    {u : ℤ[X] | u.natDegree = 1 ∧ IsWeaklyLocallyNilpotentAt u 1 ↑A ∧
        ¬ IsNilpotentAt u 1} =
      {u | ∃ c : ℤ, (0 < c ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c → p ∈ A) ∧ u = X + C c} ∪
        {u | ∃ c : ℤ, (0 < c ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c → p ∈ A) ∧ c ≠ 1 ∧
          u = X - C c} ∪
        {u | ∃ c ε : ℤ, (0 < c ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c → p ∈ A) ∧ c ≠ 1 ∧
          (ε = 1 ∨ ε = -1) ∧ u = C (ε * c) * X + 1} ∪
        {u | 2 ∈ A ∧ u = -2 * X - 1}

end

end MetaMathlibExt
