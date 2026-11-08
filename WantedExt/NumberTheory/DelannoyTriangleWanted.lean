/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Congruence properties for the Delannoy triangle coefficients

Statements from Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", *Journal of Integer Sequences* 29
(2026), Article 26.5.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Djadi/djadi6.html>).

The Delannoy triangle coefficient `C(n, k)_{[2]}` is
the Delannoy number `D(k, n - k)
= ∑_j C(k, j) C(n - k, j) 2^j` (this reading, rather
than `D(n, k)`, is forced by Theorems 1 and 9, both
verified numerically under it). For `k ≤ n` this
agrees with the existing
`MetaMathlibExt.ordinaryRiordanPascalLikeMatrix n k 1`
(the `r = 1` case of that Riordan array is documented
there as the Delannoy triangle; agreement checked
numerically for `n, k ≤ 9`), which is used below;
all statements only use `k ≤ n`. The central Delannoy
number `D_k = ∑_j C(k, j)^2 2^j` is the existing
`MetaMathlibExt.binomialPowerSeq 1 1 k`
`= ∑_j C(k, j) C(k + j, j)` (agreement checked
numerically for `k ≤ 11`). Also `q_p(2)` is the
existing `Int.fermatQuotient`, and the harmonic
numbers are taken in `ZMod m` (all denominators are
units at the stated ranges). All congruences were
verified numerically at small primes.

Not stated (see the source audit table): Lemma 12,
whose sequence `T_k(b, c)` is not defined in the
extracted statements.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix
public import MathlibExt.NumberTheory.ArithmeticFunction.BinomialPowerRealizability
public import MathlibExt.NumberTheory.FermatQuotient

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.DelannoyTriangleWanted

/-- The harmonic number `H_k = ∑_{1 ≤ i ≤ k} 1 / i`
taken in `ZMod m`. -/
def harmonicMod (m k : ℕ) : ZMod m :=
  ∑ i ∈ Finset.Icc 1 k, (i : ZMod m)⁻¹

/-- The order-two harmonic number
`H_{k,2} = ∑_{1 ≤ i ≤ k} 1 / i^2` taken in `ZMod m`. -/
def harmonic2Mod (m k : ℕ) : ZMod m :=
  ∑ i ∈ Finset.Icc 1 k, ((i : ZMod m) ^ 2)⁻¹

/-- **Theorem 1**: for every prime `p ≥ 5`,
`C(2p, p)_{[2]} ≡ 3 + 2p q_p(2) - p^2 q_p(2)^2` and
`C(2p-1, p-1)_{[2]}
  ≡ 1 + 2p q_p(2) - p^2 q_p(2)^2 (mod p^3)`, where
`q_p(2) = (2^{p-1} - 1) / p` is the Fermat quotient.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Theorem 1. -/
theorem_wanted delannoy_two_mul (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
          (2 * p) p 1 : ZMod (p ^ 3)) =
        3 + 2 * (p : ZMod (p ^ 3)) *
            (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) -
          (p : ZMod (p ^ 3)) ^ 2 *
            (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) ^ 2 ∧
      (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
            (2 * p - 1) (p - 1) 1 : ZMod (p ^ 3)) =
        1 + 2 * (p : ZMod (p ^ 3)) *
            (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) -
          (p : ZMod (p ^ 3)) ^ 2 *
            (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) ^ 2

/-- **Theorem 4**: for a prime `p ≥ 5` and a positive
integer `n`,
`C(np-1, p-1)_{[2]}
  ≡ 1 + (n-1) p q_p(2) (2 - p q_p(2)) (mod p^3)`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Theorem 4. -/
theorem_wanted delannoy_mul_sub_one (p n : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 ≤ n)
    (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
          (n * p - 1) (p - 1) 1 : ZMod (p ^ 3)) =
      1 + ((n : ZMod (p ^ 3)) - 1) * (p : ZMod (p ^ 3)) *
          (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) *
        (2 - (p : ZMod (p ^ 3)) *
          (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)))

/-- **Lemma 5**: for an odd prime `p`, an integer `s`,
and `1 ≤ k ≤ p - 1`,
`C(sp-1, k) ≡ (-1)^k (1 - sp H_k
  + (s^2 p^2 / 2) (H_k^2 - H_{k,2})) (mod p^3)`, where
the binomial coefficient is written as
`∏_{i=1}^k (sp - i) / k!` in `ZMod (p^3)`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 5. -/
theorem_wanted choose_mul_sub_one_mod (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (s : ℤ) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ p - 1) :
    (∏ i ∈ Finset.Icc 1 k,
        ((s * (p : ℤ) - (i : ℤ)) : ZMod (p ^ 3))) *
        ((Nat.factorial k : ZMod (p ^ 3)))⁻¹ =
      (-1) ^ k * (1 - (s : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) *
          harmonicMod (p ^ 3) k +
        (s : ZMod (p ^ 3)) ^ 2 * (p : ZMod (p ^ 3)) ^ 2 *
          (2 : ZMod (p ^ 3))⁻¹ *
          (harmonicMod (p ^ 3) k ^ 2 - harmonic2Mod (p ^ 3) k))

/-- **Lemma 6**: for a prime `p > 3`,
`∑_{k=1}^{p-1} 2^k / k ≡ -2 q_p(2) (mod p^2)` and
`∑_{k=1}^{p-1} 2^k / k^2 ≡ -q_p(2)^2 (mod p)`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 6. -/
theorem_wanted sum_two_pow_div (p : ℕ) (hp : p.Prime)
    (hp3 : 3 < p) (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (∑ k ∈ Finset.Icc 1 (p - 1),
        (2 : ZMod (p ^ 2)) ^ k * (k : ZMod (p ^ 2))⁻¹) =
        -2 * (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 2)) ∧
      (∑ k ∈ Finset.Icc 1 (p - 1),
          (2 : ZMod p) ^ k * ((k : ZMod p) ^ 2)⁻¹) =
        -((Int.fermatQuotient p hp 2 h2p : ZMod p)) ^ 2

/-- **Lemma 7**: for a prime `p ≥ 5`,
`∑_{k=1}^{p-1} H_k 2^k / k ≡ -q_p(2)^2 (mod p)`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 7. -/
theorem_wanted sum_harmonic_two_pow_div (p : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (∑ k ∈ Finset.Icc 1 (p - 1),
        harmonicMod p k * (2 : ZMod p) ^ k * (k : ZMod p)⁻¹) =
      -((Int.fermatQuotient p hp 2 h2p : ZMod p)) ^ 2

/-- **Theorem 9**: for an odd prime `p`,
`∑_{0 ≤ k ≤ n ≤ p-1} C(n, k)_{[2]} ≡ (2 / p) (mod p)`,
where `(2 / p)` is the Legendre symbol.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Theorem 9. -/
theorem_wanted sum_delannoy (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (∑ n ∈ Finset.range p, ∑ k ∈ Finset.range (n + 1),
        (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
            n k 1 : ZMod p)) =
      (legendreSym p 2 : ZMod p)

/-- **Lemma 11**: for a prime `p` and integers
`0 ≤ j ≤ k ≤ p - 2`,
`C(p-j, k+1) + (-1)^k C(k+j, k+1) ≡ 0 (mod p)`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 11. -/
theorem_wanted choose_add_choose_mod (p j k : ℕ)
    (hp : p.Prime) (hjk : j ≤ k) (hk : k ≤ p - 2) :
    (Nat.choose (p - j) (k + 1) : ZMod p) +
        (-1) ^ k * (Nat.choose (k + j) (k + 1) : ZMod p) = 0

/-- **Lemma 13**: for every integer `k ≥ 0`,
`∑_{j=0}^k C(k, j) C(k+j, k+1) = (D_{k+1} - 3 D_k) / 4`,
where `D_k` is the central Delannoy number (stated in
the multiplied-out form over `ℤ`).

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 13. -/
theorem_wanted sum_choose_choose_binomialPowerSeq (k : ℕ) :
    4 * (∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j * Nat.choose (k + j) (k + 1) : ℤ)) =
      (MetaMathlibExt.binomialPowerSeq 1 1 (k + 1) : ℤ) -
        3 * (MetaMathlibExt.binomialPowerSeq 1 1 k : ℤ)

end MathlibExt.NumberTheory.DelannoyTriangleWanted
