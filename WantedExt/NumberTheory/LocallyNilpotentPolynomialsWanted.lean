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

/-- A polynomial `u ∈ ℤ[x]` is weakly locally nilpotent at `r` outside a set `A` of primes
if for every prime `p ∉ A` some iterate `u^{(m)}(r)`, `m ≥ 1`, is divisible by `p`. For
`A = ∅` this is "locally nilpotent at `r`".

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2. -/
public def IsWeaklyLocallyNilpotentAt (u : ℤ[X]) (r : ℤ) (A : Set ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ A → ∃ m, 0 < m ∧ (p : ℤ) ∣ (fun x => u.eval x)^[m] r

/-- A polynomial `u ∈ ℤ[x]` is nilpotent at `r` if some iterate `u^{(n)}(r)`, `n ≥ 1`,
is `0`.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2. -/
public def IsNilpotentAt (u : ℤ[X]) (r : ℤ) : Prop :=
  ∃ n, 0 < n ∧ (fun x => u.eval x)^[n] r = 0

/-- CRS lemma: if `α, β, γ` are nonzero integers and `β / γ` is not an integer power `α^k`
(`k ∈ ℤ`), then infinitely many primes divide none of `γ αⁿ - β`, `n ≥ 1`. The condition
`β / γ ≠ α^k` is stated division-free: `β ≠ γ αᵏ` and `β αᵏ ≠ γ` for all `k ∈ ℕ` (the cases
`k ≥ 0` and `k ≤ 0`).

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Lemma 3.2. -/
public theorem_wanted infinite_primes_not_dvd_mul_pow_sub (α β γ : ℤ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hγ : γ ≠ 0) (h : ∀ k : ℕ, β ≠ γ * α ^ k ∧ β * α ^ k ≠ γ) :
    {p : ℕ | p.Prime ∧ ∀ n : ℕ, 0 < n → ¬ (p : ℤ) ∣ γ * α ^ n - β}.Infinite

/-- Iterates of `x + 1`: `u^{(m)}(r) = r + m`.

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

/-- `x + 1` is locally nilpotent at `1`: `u^{(p-1)}(1) = p`.

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

/-- `x + 1` is not nilpotent at `1`: `u^{(n)}(1) = n + 1 ≠ 0`.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2, example (e). -/
public theorem not_isNilpotentAt_X_add_one : ¬ IsNilpotentAt (X + 1) 1 := by
  rintro ⟨n, _, hn⟩
  rw [iterate_eval_X_add_one] at hn
  omega

/-- Classification of the locally nilpotent polynomials at `1` (degree `≥ 1`): exactly
`(x-1)p(x)` with `p ≠ 0`, `-2x + 4 + p(x)(x-1)(x-2)`,
`-2x^2 + 7x - 3 + p(x)(x-1)(x-2)(x-3)` (`p ∈ ℤ[x]`), and `x + 1`. The paper's
nilpotency-index annotations are not part of this statement.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Theorem 4.1. -/
public theorem_wanted locallyNilpotentAt_one_classification :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 1 ∅} =
      {u | ∃ p : ℤ[X], p ≠ 0 ∧ u = (X - 1) * p} ∪
        {u | ∃ p : ℤ[X], u = -2 * X + 4 + p * (X - 1) * (X - 2)} ∪
        {u | ∃ p : ℤ[X], u = -2 * X ^ 2 + 7 * X - 3 + p * (X - 1) * (X - 2) * (X - 3)} ∪
        {X + 1}

/-- Classification of the locally nilpotent polynomials at `-1` (degree `≥ 1`), the image of
Theorem 4.1 under `u(x) ↦ -u(-x)`: exactly `(x+1)p(x)` with `p ≠ 0`,
`-2x - 4 + p(x)(x+1)(x+2)`, `2x^2 + 7x + 3 + p(x)(x+1)(x+2)(x+3)` (`p ∈ ℤ[x]`), and `x - 1`.
The nilpotency-index annotations are not part of this statement.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Corollary 4.2. -/
public theorem_wanted locallyNilpotentAt_neg_one_classification :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u (-1) ∅} =
      {u | ∃ p : ℤ[X], p ≠ 0 ∧ u = (X + 1) * p} ∪
        {u | ∃ p : ℤ[X], u = -2 * X - 4 + p * (X + 1) * (X + 2)} ∪
        {u | ∃ p : ℤ[X], u = 2 * X ^ 2 + 7 * X + 3 + p * (X + 1) * (X + 2) * (X + 3)} ∪
        {X - 1}

/-- The locally nilpotent but non-nilpotent polynomials at `1` and at `-1` are exactly
`x + 1` and `x - 1` respectively (`S_1 = {x + 1}`, `S_{-1} = {x - 1}`).

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Corollary 4.3. -/
public theorem_wanted locallyNilpotent_not_nilpotentAt_one_neg_one :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 1 ∅ ∧ ¬ IsNilpotentAt u 1} =
        {X + 1} ∧
      {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u (-1) ∅ ∧
        ¬ IsNilpotentAt u (-1)} = {X - 1}

/-- Classification of the locally nilpotent polynomials at `0` (degree `≥ 1`): exactly
`x + b` with `b ≠ 0`; `ax + b` with `b ≠ 0` and `P(b) ⊇ P(a) ≠ ∅` (`P(n)` the set of prime
divisors of `n`); `x p(x)` with `p ≠ 0`; and `(x - a) p(x)` with `a ≠ 0`, `p(0) = -1`.
The nilpotency annotations are not part of this statement.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Theorem 4.4. -/
public theorem_wanted locallyNilpotentAt_zero_classification :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 0 ∅} =
      {u | ∃ b : ℤ, b ≠ 0 ∧ u = X + C b} ∪
        {u | ∃ a b : ℤ, b ≠ 0 ∧ (∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a) ∧
          (∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b) ∧ u = C a * X + C b} ∪
        {u | ∃ p : ℤ[X], p ≠ 0 ∧ u = X * p} ∪
        {u | ∃ (a : ℤ) (p : ℤ[X]), a ≠ 0 ∧ p.eval 0 = -1 ∧ u = (X - C a) * p}

/-- The locally nilpotent but non-nilpotent polynomials at `0` (`S_0`) are exactly
`x + b` with `b ≠ 0` and `ax + b` with `b ≠ 0` and `P(b) ⊇ P(a) ≠ ∅`.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Corollary 4.5. -/
public theorem_wanted locallyNilpotent_not_nilpotentAt_zero :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 0 ∅ ∧ ¬ IsNilpotentAt u 0} =
      {u | ∃ b : ℤ, b ≠ 0 ∧ u = X + C b} ∪
        {u | ∃ a b : ℤ, b ≠ 0 ∧ (∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a) ∧
          (∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b) ∧ u = C a * X + C b}

/-- For a finite set `A` of primes, the linear polynomials weakly locally nilpotent at `1`
outside `A` and not nilpotent at `1` are exactly `x + c`, `x - c` with `c ≠ 1`,
`±c x + 1` with `c ≠ 1`, and (only when `2 ∈ A`) `-2x - 1`, where `c` ranges over the
positive integers all of whose prime factors lie in `A` (`c = q_1^{s_1} ⋯ q_k^{s_k}`;
`c ≠ 1` is the paper's `∑ s_i ≥ 1`).

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
