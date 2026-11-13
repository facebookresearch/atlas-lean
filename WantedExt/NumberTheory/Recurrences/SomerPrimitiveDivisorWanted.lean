/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic

open scoped Filter

namespace MetaMathlibExt

@[expose] public section

/-- **Somer's primitive divisor theorem.** Let $P$ and $Q$ be integers with $Q \ne 0$, and let
$(u_n)_{n \ge 0}$ be the integer sequence with $u_0 = 0$, $u_1 = 1$ and
$u_{n+2} = Pu_{n+1} - Qu_n$ (the Lucas sequence of the first kind). Suppose the sequence is
nondegenerate: whenever complex numbers $\alpha$ and $\beta$ satisfy $\alpha + \beta = P$,
$\alpha\beta = Q$ and $\beta \ne 0$, no power $(\alpha / \beta)^k$ with $k \ge 1$ equals
$1$. Then for all sufficiently large $n$ the term $u_n$ has a primitive prime divisor: a
prime $p$ that divides $u_n$ but divides no $u_m$ with $0 < m < n$.

Nondegeneracy also excludes the double-root case $\alpha = \beta$.

Source: Chris Smyth, *The Terms in Lucas Sequences Divisible by Their
Indices*, Journal of Integer Sequences 13 (2010), Article 10.2.4, invoking
Somer's Theorem 1, lines 632–634,
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Smyth/smyth2.tex>. -/
theorem_wanted somer_eventually_has_primitive_prime_divisor
    (P Q : ℤ) (u : ℕ → ℤ)
    (hu0 : u 0 = 0)
    (hu1 : u 1 = 1)
    (huRec : ∀ n : ℕ, u (n + 2) = P * u (n + 1) - Q * u n)
    (hQ : Q ≠ 0)
    (hNondeg : ∀ α β : ℂ, α + β = (P : ℂ) → α * β = (Q : ℂ) → β ≠ 0 →
      ∀ k : ℕ, 0 < k → (α / β) ^ k ≠ 1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ p : ℕ, Nat.Prime p ∧ (p : ℤ) ∣ u n ∧
        ∀ m : ℕ, 0 < m → m < n → ¬ (p : ℤ) ∣ u m

end

end MetaMathlibExt
