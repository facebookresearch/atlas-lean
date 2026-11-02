/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **Weakly locally nilpotent polynomial at a point.** Let $u \in \mathbb{Z}[x]$ and
$r \in \mathbb{Z}$, and let $A$ be a set of natural numbers. Write $u^{(m)}$ for the $m$-fold
iterate of $u$ as a map $\mathbb{Z} \to \mathbb{Z}$. Then $u$ is weakly locally nilpotent at $r$
outside $A$ if for every prime $p \notin A$ there is $m \ge 1$ such that $p$ divides
$u^{(m)}(r)$. For $A = \emptyset$ this is called locally nilpotent at $r$.

Only the primes in $A$ matter, so $A$ is usually taken to be a set of primes.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2. -/
public def IsWeaklyLocallyNilpotentAt (u : ℤ[X]) (r : ℤ) (A : Set ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ A → ∃ m, 0 < m ∧ (p : ℤ) ∣ (fun x => u.eval x)^[m] r

/-- **Nilpotent polynomial at a point.** Let $u \in \mathbb{Z}[x]$ and $r \in \mathbb{Z}$, and
write $u^{(n)}$ for the $n$-fold iterate of $u$ as a map $\mathbb{Z} \to \mathbb{Z}$. Then $u$ is
nilpotent at $r$ if $u^{(n)}(r) = 0$ for some $n \ge 1$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2. -/
public def IsNilpotentAt (u : ℤ[X]) (r : ℤ) : Prop :=
  ∃ n, 0 < n ∧ (fun x => u.eval x)^[n] r = 0

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

/-- **Iterates of $x + 1$.** Let $u(x) = x + 1 \in \mathbb{Z}[x]$ and write $u^{(m)}$ for its
$m$-fold iterate as a map $\mathbb{Z} \to \mathbb{Z}$. For every integer $r$ and every natural
number $m$, $u^{(m)}(r) = r + m$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2, example (e). -/
public theorem iterate_eval_X_add_one (r : ℤ) (m : ℕ) :
    (fun x => (X + 1 : ℤ[X]).eval x)^[m] r = r + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    simp
    ring

/-- **$x + 1$ is locally nilpotent at $1$.** Let $u(x) = x + 1 \in \mathbb{Z}[x]$ and write
$u^{(m)}$ for the $m$-fold iterate of $u$ as a map $\mathbb{Z} \to \mathbb{Z}$. Then for every
prime $p$ there is $m \ge 1$ such that $p$ divides $u^{(m)}(1)$.

One can take $m = p - 1$, since $u^{(p-1)}(1) = p$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2, example (e). -/
public theorem isWeaklyLocallyNilpotentAt_X_add_one :
    IsWeaklyLocallyNilpotentAt (X + 1) 1 ∅ := by
  intro p hp _
  refine ⟨p - 1, by have := hp.two_le; omega, ?_⟩
  rw [iterate_eval_X_add_one]
  have : ((p - 1 : ℕ) : ℤ) = p - 1 := by have := hp.one_le; push_cast [this]; ring
  rw [this]
  simp

/-- **$x + 1$ is not nilpotent at $1$.** The polynomial $x + 1 \in \mathbb{Z}[x]$ is not nilpotent
at $1$.

Writing $u(x) = x + 1$, the iterates satisfy $u^{(n)}(1) = n + 1 \ne 0$ for every $n \ge 1$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2, example (e). -/
public theorem not_isNilpotentAt_X_add_one : ¬ IsNilpotentAt (X + 1) 1 := by
  rintro ⟨n, _, hn⟩
  rw [iterate_eval_X_add_one] at hn
  omega

/-- **Classification of locally nilpotent polynomials at $1$.** A polynomial $u \in \mathbb{Z}[x]$
of positive degree is locally nilpotent at $1$ if and only if it has one of the following forms,
for some $p \in \mathbb{Z}[x]$: $(x-1)p(x)$ with $p \ne 0$; $-2x + 4 + p(x)(x-1)(x-2)$;
$-2x^2 + 7x - 3 + p(x)(x-1)(x-2)(x-3)$; or $u = x + 1$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Theorem 4.1. -/
public theorem_wanted locallyNilpotentAt_one_classification :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 1 ∅} =
      {u | ∃ p : ℤ[X], p ≠ 0 ∧ u = (X - 1) * p} ∪
        {u | ∃ p : ℤ[X], u = -2 * X + 4 + p * (X - 1) * (X - 2)} ∪
        {u | ∃ p : ℤ[X], u = -2 * X ^ 2 + 7 * X - 3 + p * (X - 1) * (X - 2) * (X - 3)} ∪
        {X + 1}

/-- **Classification of locally nilpotent polynomials at $-1$.** A polynomial $u \in \mathbb{Z}[x]$
of positive degree is locally nilpotent at $-1$ if and only if it has one of the following forms,
for some $p \in \mathbb{Z}[x]$: $(x+1)p(x)$ with $p \ne 0$; $-2x - 4 + p(x)(x+1)(x+2)$;
$2x^2 + 7x + 3 + p(x)(x+1)(x+2)(x+3)$; or $u = x - 1$.

These are the images of the polynomials locally nilpotent at $1$ under $u(x) \mapsto -u(-x)$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Corollary 4.2. -/
public theorem_wanted locallyNilpotentAt_neg_one_classification :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u (-1) ∅} =
      {u | ∃ p : ℤ[X], p ≠ 0 ∧ u = (X + 1) * p} ∪
        {u | ∃ p : ℤ[X], u = -2 * X - 4 + p * (X + 1) * (X + 2)} ∪
        {u | ∃ p : ℤ[X], u = 2 * X ^ 2 + 7 * X + 3 + p * (X + 1) * (X + 2) * (X + 3)} ∪
        {X - 1}

/-- **Locally nilpotent but not nilpotent polynomials at $\pm 1$.** The only polynomial
$u \in \mathbb{Z}[x]$ of positive degree that is locally nilpotent at $1$ but not nilpotent at $1$
is $x + 1$, and the only polynomial of positive degree that is locally nilpotent at $-1$ but not
nilpotent at $-1$ is $x - 1$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Corollary 4.3. -/
public theorem_wanted locallyNilpotent_not_nilpotentAt_one_neg_one :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 1 ∅ ∧ ¬ IsNilpotentAt u 1} =
        {X + 1} ∧
      {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u (-1) ∅ ∧
        ¬ IsNilpotentAt u (-1)} = {X - 1}

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

/-- **Polynomials locally nilpotent but not nilpotent at $0$.** A polynomial $u \in \mathbb{Z}[x]$
of degree at least $1$ is locally nilpotent at $0$ and not nilpotent at $0$ if and only if either
$u = x + b$ for some integer $b \ne 0$, or $u = ax + b$ for some integers $a$ and $b$ with
$b \ne 0$ such that $a$ has at least one prime divisor and every prime divisor of $a$ divides $b$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Corollary 4.5. -/
public theorem_wanted locallyNilpotent_not_nilpotentAt_zero :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 0 ∅ ∧ ¬ IsNilpotentAt u 0} =
      {u | ∃ b : ℤ, b ≠ 0 ∧ u = X + C b} ∪
        {u | ∃ a b : ℤ, b ≠ 0 ∧ (∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a) ∧
          (∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b) ∧ u = C a * X + C b}

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
