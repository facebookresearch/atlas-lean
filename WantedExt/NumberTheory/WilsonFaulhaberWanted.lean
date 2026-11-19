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

Also stated: Lemma 1 (the Hensel digit `t_k^{(0)}`),
Theorem 2 (the Faulhaber trailing coefficient `c₁(l)`),
Corollary 1 (Glaisher's Bernoulli form), Theorem 3 and
Lemma 3 (`mod p^3`), with the `p`-adic congruences in `ℚ`
read through `padicNorm`.

Not stated (see the source audit table): Lemma 2 and
Corollary 2 (false as printed), Proposition 1 (quoted,
false as printed at `k = 0`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.Algebra.Polynomial.Eval.Defs
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

/-- **Theorem 1**: let `δ₀(k)` be defined for
`1 ≤ k ≤ p - 1` by
`k^(p-1) ≡ 1 + p δ₀(k) (mod p^2)`. Then
`(p - 1)! ≡ -1 + p ∑_{k=1}^{p-1} δ₀(k) (mod p^2)`.
Here `δ₀(k)` is `Int.fermatQuotient` (the sum runs
over the attached subtype so that each term carries
its coprimality witness).

Source: Claire Levaillant, "Wilson's Theorem Modulo
`p^2` Derived from Faulhaber Polynomials", Theorem 1. -/
theorem_wanted wilson_mod_prime_sq (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    (Nat.factorial (p - 1) : ZMod (p ^ 2)) =
      -1 + (p : ZMod (p ^ 2)) *
        ∑ k ∈ (Finset.Icc 1 (p - 1)).attach,
          ((Int.fermatQuotient p hp (k.1 : ℤ)
            (coprime_of_mem hp k.2) : ℤ) : ZMod (p ^ 2))

/-- **Lemma 1**: for `1 ≤ k ≤ p - 1` let `k + p t` (with `t ∈ ℤ`) satisfy
`(k + p t)^(p-1) + (p - 1)! ≡ 0 (mod p^2)`, i.e. `t` reduces to the second
`p`-adic digit `t_k^{(0)}` of the Hensel root `x_k ≡ k (mod p)` of
`X^(p-1) + (p - 1)!`. Then `p t ≡ k (1 + (p - 1)! + p δ₀(k)) (mod p^2)`, with
`δ₀(k)` the Fermat quotient (`Int.fermatQuotient`).

Source: Claire Levaillant, *Wilson's Theorem Modulo p^2 Derived from Faulhaber
Polynomials*, INTEGERS 24 (2024), Article A87, Lemma 1. -/
theorem_wanted hensel_digit_mul_prime_mod_sq (p : ℕ) (hp : p.Prime) (k : ℕ)
    (hk : k ∈ Finset.Icc 1 (p - 1)) (t : ℤ)
    (ht : (p : ℤ) ^ 2 ∣ ((k : ℤ) + p * t) ^ (p - 1) + (Nat.factorial (p - 1) : ℤ)) :
    (((p : ℤ) * t : ℤ) : ZMod (p ^ 2)) =
      (k : ZMod (p ^ 2)) * (1 + (Nat.factorial (p - 1) : ZMod (p ^ 2)) +
        (p : ZMod (p ^ 2)) *
          ((Int.fermatQuotient p hp (k : ℤ) (coprime_of_mem hp hk) : ℤ) : ZMod (p ^ 2)))

/-- **Theorem 2**: let `p = 2l + 1` be an odd prime and `a = p(p - 1)/2`. The
Faulhaber polynomial `F ∈ ℚ[a]` with `∑_{k=1}^{n} k^p = F(n(n+1)/2)` for all `n`
exists, and its coefficients `c_i(l)` of `a^(i+1)` (`1 ≤ i ≤ l`) satisfy
(i) `c_i(l) ∈ ℤ_p` and (ii) `(p - 1)! ≡ c_1(l)/2 - p (mod p^2)`, both read in
`ℚ` through the `p`-adic norm. The identity at `n = p - 1` is the paper's (3).

Source: Claire Levaillant, *Wilson's Theorem Modulo p^2 Derived from Faulhaber
Polynomials*, INTEGERS 24 (2024), Article A87, Theorem 2. -/
theorem_wanted faulhaber_coeff_integral_and_wilson (p l : ℕ) (hp : p.Prime)
    (hpl : p = 2 * l + 1) :
    (∃ F : Polynomial ℚ, ∀ n : ℕ,
        ∑ k ∈ Finset.Icc 1 n, (k : ℚ) ^ p = F.eval ((n * (n + 1) / 2 : ℕ) : ℚ)) ∧
      ∀ F : Polynomial ℚ, (∀ n : ℕ,
          ∑ k ∈ Finset.Icc 1 n, (k : ℚ) ^ p = F.eval ((n * (n + 1) / 2 : ℕ) : ℚ)) →
        (∀ i ∈ Finset.Icc 1 l, padicNorm p (F.coeff (i + 1)) ≤ 1) ∧
          padicNorm p ((Nat.factorial (p - 1) : ℚ) - (F.coeff 2 / 2 - p)) ≤
            (p : ℚ) ^ (-2 : ℤ)

/-- **Corollary 1** (Glaisher): `(p - 1)! ≡ p B_{p-1} - p (mod p^2)`, read in `ℚ`
through the `p`-adic norm (`p B_{p-1}` is `p`-integral by von Staudt–Clausen).
Stated for every prime with Mathlib's `bernoulli` (`B₁ = -1/2`); at `p = 2` the
paper's second-type `B₁ = 1/2` would give `1 ≢ -1 (mod 4)`.

Source: Claire Levaillant, *Wilson's Theorem Modulo p^2 Derived from Faulhaber
Polynomials*, INTEGERS 24 (2024), Article A87, Corollary 1 (after Glaisher). -/
theorem_wanted wilson_mod_prime_sq_bernoulli (p : ℕ) (hp : p.Prime) :
    padicNorm p ((Nat.factorial (p - 1) : ℚ) - (p * bernoulli (p - 1) - p)) ≤
      (p : ℚ) ^ (-2 : ℤ)

/-- **Theorem 3**: for an odd prime `p` let `δ₀(k)`, `δ₁(k)` be the second and
third `p`-adic digits of `k^(p-1) ≡ 1 + p δ₀(k) + p^2 δ₁(k) (mod p^3)` (here
`((k^(p-1) - 1)/p) % p` and `((k^(p-1) - 1)/p^2) % p`). Then
`(p - 1)! ≡ -1 + p ∑ δ₀(i) + p^2 ∑ (δ₀(i) + δ₁(i)) - (p^2/2)((∑ δ₀(i))^2 + ∑ δ₀(i)^2)
(mod p^3)`, sums over `1 ≤ i ≤ p - 1`, read in `ℚ` through the `p`-adic norm.
`p ≠ 2` is added (the formula divides by `2`; at `p = 2` the difference is `2`).

Source: Claire Levaillant, *Wilson's Theorem Modulo p^2 Derived from Faulhaber
Polynomials*, INTEGERS 24 (2024), Article A87, Theorem 3. -/
theorem_wanted wilson_mod_prime_cube_digits (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    padicNorm p ((Nat.factorial (p - 1) : ℚ) -
      (-1 + p * ∑ i ∈ Finset.Icc 1 (p - 1), (((i ^ (p - 1) - 1) / p % p : ℕ) : ℚ) +
        p ^ 2 * ∑ i ∈ Finset.Icc 1 (p - 1),
          ((((i ^ (p - 1) - 1) / p % p : ℕ) : ℚ) + (((i ^ (p - 1) - 1) / p ^ 2 % p : ℕ) : ℚ)) -
        p ^ 2 / 2 * ((∑ i ∈ Finset.Icc 1 (p - 1), (((i ^ (p - 1) - 1) / p % p : ℕ) : ℚ)) ^ 2 +
          ∑ i ∈ Finset.Icc 1 (p - 1), (((i ^ (p - 1) - 1) / p % p : ℕ) : ℚ) ^ 2))) ≤
      (p : ℚ) ^ (-3 : ℤ)

/-- **Lemma 3**: for an odd prime `p`, with `S₁ = ∑_{i=1}^{p-1} i^(p-1)` and
`S₂ = ∑_{i=1}^{p-1} (i^(p-1))^2`,
`(p - 1)! ≡ -1 - (S₁^2 + S₂)/2 + (2p + 1) S₁ - (p - 1)(3p/2 + 1) (mod p^3)`,
read in `ℚ` through the `p`-adic norm. `p ≠ 2` is added (the formula divides by
`2`; at `p = 2` the difference is `2`).

Source: Claire Levaillant, *Wilson's Theorem Modulo p^2 Derived from Faulhaber
Polynomials*, INTEGERS 24 (2024), Article A87, Lemma 3. -/
theorem_wanted wilson_mod_prime_cube_power_sums (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    padicNorm p ((Nat.factorial (p - 1) : ℚ) -
      (-1 - ((∑ i ∈ Finset.Icc 1 (p - 1), (i : ℚ) ^ (p - 1)) ^ 2 +
          ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ℚ) ^ (p - 1)) ^ 2) / 2 +
        (2 * p + 1) * ∑ i ∈ Finset.Icc 1 (p - 1), (i : ℚ) ^ (p - 1) -
        (p - 1) * (3 / 2 * p + 1))) ≤
      (p : ℚ) ^ (-3 : ℤ)

end MathlibExt.NumberTheory.WilsonFaulhaberWanted
