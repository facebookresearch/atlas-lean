/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wilson's theorem modulo `p^2` from Faulhaber polynomials

Statement from Claire Levaillant, "Wilson's Theorem
Modulo `p^2` Derived from Faulhaber Polynomials",
*INTEGERS* 24 (2024), Article A87
(<https://math.colgate.edu/~integers/vol24.html>).

Theorem 1: with `δ₀(k)` defined by
`k^(p-1) ≡ 1 + p δ₀(k) (mod p^2)` (so `δ₀(k)` is the
Fermat quotient `(k^(p-1) - 1) / p`), one has
`(p - 1)! ≡ -1 + p ∑_{k=1}^{p-1} δ₀(k) (mod p^2)`.
Verified for all odd primes `p ≤ 31` (it fails at
`p = 2`).

Not stated (see the source audit table): Lemmas 1-3
(the Hensel-lift digits `t_k`), Proposition 1
(quoted), Theorem 2 (the Faulhaber trailing
coefficient `c₁(l)`), Theorem 3 and Corollary 2
(their `mod p^3` formulas could not be pinned from
the extraction), and Corollary 1 (the Bernoulli form
`(p-1)! ≡ p B_{p-1} - p (mod p^2)`, whose faithful
formulation needs the `p`-adic denominator of
`B_{p-1}`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.NumberTheory.FermatQuotient

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.WilsonFaulhaberWanted

/-- Coprimality witness for terms of the sum below:
`1 ≤ k ≤ p - 1` and `p` prime give `IsCoprime k p`. -/
private theorem coprime_of_mem {p k : ℕ} (hp : p.Prime)
    (h : k ∈ Finset.Icc 1 (p - 1)) : IsCoprime (k : ℤ) (p : ℤ) := by
  rw [Finset.mem_Icc] at h
  have hlt : k < p := by have := hp.pos; omega
  exact Nat.isCoprime_iff_coprime.mpr
    ((hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt h.1 hlt)).symm)

/-- **Wilson's theorem modulo $p^2$.** Let $p$ be an odd prime and, for $1 \le k \le p - 1$, let
$q_p(k)$ be the Fermat quotient of $k$, the integer with $k^{p-1} = 1 + p\, q_p(k)$. Then
$$
(p - 1)! \equiv -1 + p \sum_{k=1}^{p-1} q_p(k) \pmod{p^2}.
$$

Source: Claire Levaillant, "Wilson's Theorem Modulo
`p^2` Derived from Faulhaber Polynomials", Theorem 1. -/
theorem_wanted wilson_mod_prime_sq (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    (Nat.factorial (p - 1) : ZMod (p ^ 2)) =
      -1 + (p : ZMod (p ^ 2)) *
        ∑ k ∈ (Finset.Icc 1 (p - 1)).attach,
          ((Int.fermatQuotient p hp (k.1 : ℤ)
            (coprime_of_mem hp k.2) : ℤ) : ZMod (p ^ 2))

end MathlibExt.NumberTheory.WilsonFaulhaberWanted
