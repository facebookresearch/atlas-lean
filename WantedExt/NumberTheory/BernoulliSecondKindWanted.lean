/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Formulas involving Bernoulli and Stirling numbers of both kinds

Statements from Bakir Farhi, "Formulas Involving Bernoulli
and Stirling Numbers of Both Kinds", *Journal of Integer
Sequences* 28 (2025), Article 25.2.6
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Farhi/farhi26.tex>).

Notation: `Bₙ` is Mathlib's `bernoulli`, `Bₙ(X)` is
Mathlib's `Polynomial.bernoulli`, `S(n,k)` is
`Nat.stirlingSecond`, the signed Stirling numbers of the
first kind `s(n,k)` are MathlibExt's `signedStirlingFirst`,
`X^{\underline n}` is Mathlib's falling-factorial
polynomial `descPochhammer`, and the Bernoulli numbers of the
second kind `Bₙ^*` (exponential generating function
`t / log(1 + t)`, in Roman's normalization) are
MathlibExt's `MetaMathlibExt.MetaMathlibExt.bernoulliSecond`. The paper's `ℕ` is the positive
integers; the convolution identities (Corollaries 7, 10,
Theorem 13, Corollary 15) are stated for `1 ≤ k ≤ n` as
printed, and Lemma 3's complex sequences are stated over
`ℚ`. All identities were verified by exact rational
computation before stating.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.PowerSeries.Log
public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst
public import MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKind

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.BernoulliSecondKindWanted

/-- **Theorem 1**: `Bₙ(X) = Bₙ + ∑_{k=1}^n (n/k)
S(n-1,k-1) X^{\underline k}` as polynomials.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 1. -/
theorem_wanted bernoulli_poly_eq (n : ℕ) :
    Polynomial.bernoulli n =
      Polynomial.C (bernoulli n) +
        ∑ k ∈ Finset.Icc 1 n, Polynomial.C
          ((n : ℚ) / k * (Nat.stirlingSecond (n - 1) (k - 1) : ℚ)) *
          descPochhammer ℚ k

/-- **Corollary 2**: `Bₙ = -∑_{k=1}^n (n/k) S(n-1,k-1)
Bₖ^*` for `n ≥ 1`.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Corollary 2. -/
theorem_wanted bernoulli_eq_neg_sum (n : ℕ) (hn : 1 ≤ n) :
    bernoulli n =
      -∑ k ∈ Finset.Icc 1 n, (n : ℚ) / k *
        (Nat.stirlingSecond (n - 1) (k - 1) : ℚ) *
        MetaMathlibExt.bernoulliSecond k

/-- **Lemma 3** (Stirling inversion): for rational
sequences `u, v`, `u n = ∑_{k=0}^n s(n,k) v k` for all `n`
if and only if `v n = ∑_{k=0}^n S(n,k) u k` for all `n`
(paper: complex sequences).

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Lemma 3. -/
theorem_wanted stirling_inversion_iff (u v : ℕ → ℚ) :
    (∀ n, u n = ∑ k ∈ Finset.range (n + 1),
      (MetaMathlibExt.signedStirlingFirst n k : ℚ) * v k) ↔
    (∀ n, v n = ∑ k ∈ Finset.range (n + 1),
      (Nat.stirlingSecond n k : ℚ) * u k)

/-- **Theorem 4**: `Bₙ^* = -∑_{k=1}^n (n/k) s(n-1,k-1)
Bₖ` for `n ≥ 1`.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 4. -/
theorem_wanted bernoulliSecond_eq_neg_sum (n : ℕ)
    (hn : 1 ≤ n) :
    MetaMathlibExt.bernoulliSecond n =
      -∑ k ∈ Finset.Icc 1 n, (n : ℚ) / k *
        (MetaMathlibExt.signedStirlingFirst (n - 1) (k - 1) : ℚ) * bernoulli k

/-- **Theorem 5**: `X^{\underline n} = Bₙ^* +
∑_{k=1}^n (n/k) s(n-1,k-1) Bₖ(X)` as polynomials.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 5. -/
theorem_wanted descPochhammer_eq (n : ℕ) :
    descPochhammer ℚ n =
      Polynomial.C (MetaMathlibExt.bernoulliSecond n) +
        ∑ k ∈ Finset.Icc 1 n, Polynomial.C
          ((n : ℚ) / k * (MetaMathlibExt.signedStirlingFirst (n - 1) (k - 1) : ℚ)) *
          Polynomial.bernoulli k

/-- **Corollary 7**: `∑_{i=k}^n S(n-1,i-1) s(i,k)/i =
(1/n) C(n,k) B_{n-k}` for `1 ≤ k ≤ n`.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Corollary 7. -/
theorem_wanted sum_stirlingSecond_signed_div (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ i ∈ Finset.Icc k n,
        (Nat.stirlingSecond (n - 1) (i - 1) : ℚ) *
          (MetaMathlibExt.signedStirlingFirst i k : ℚ) / i =
      (1 / (n : ℚ)) * (Nat.choose n k : ℚ) * bernoulli (n - k)

/-- **Corollary 9**: `Bₙ = ∑_{i=0}^n (-1)^i (i!/(i+1))
S(n,i)`.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Corollary 9. -/
theorem_wanted bernoulli_eq_sum_stirlingSecond (n : ℕ) :
    bernoulli n =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℚ) ^ i *
        ((i.factorial : ℚ) / (i + 1)) *
        (Nat.stirlingSecond n i : ℚ)

/-- **Corollary 10**: `∑_{i=k}^n S(n,i) s(i,k)/i = (1/n)
C(n,k) B_{n-k} + δ_{n-1,k}` for `1 ≤ k ≤ n`.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Corollary 10. -/
theorem_wanted sum_stirlingSecond_signed_div_delta (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ i ∈ Finset.Icc k n,
        (Nat.stirlingSecond n i : ℚ) *
          (MetaMathlibExt.signedStirlingFirst i k : ℚ) / i =
      (1 / (n : ℚ)) * (Nat.choose n k : ℚ) * bernoulli (n - k) +
        (if n - 1 = k then 1 else 0)

/-- **Proposition 11**: `Bₙ^* = ∑_{i=0}^n s(n,i)/(i+1)`.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Proposition 11. -/
theorem_wanted bernoulliSecond_eq_sum (n : ℕ) :
    MetaMathlibExt.bernoulliSecond n =
      ∑ i ∈ Finset.range (n + 1),
        (MetaMathlibExt.signedStirlingFirst n i : ℚ) / (i + 1)

/-- **Theorem 13**: `∑_{i=k}^n s(n-1,i-1) S(i,k)/i =
(1/n) C(n,k) B_{n-k}^*` for `1 ≤ k ≤ n`.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 13. -/
theorem_wanted sum_signed_stirlingSecond_div (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ i ∈ Finset.Icc k n,
        (MetaMathlibExt.signedStirlingFirst (n - 1) (i - 1) : ℚ) *
          (Nat.stirlingSecond i k : ℚ) / i =
      (1 / (n : ℚ)) * (Nat.choose n k : ℚ) *
        MetaMathlibExt.bernoulliSecond (n - k)

/-- **Corollary 15**: `∑_{i=k}^n s(n,i) S(i,k)/i =
(-1)^{n-k} ((n-1)!/k!) ∑_{ℓ=0}^{n-k} ((-1)^ℓ/ℓ!) B_ℓ^*`
for `1 ≤ k ≤ n`.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Corollary 15. -/
theorem_wanted sum_signed_stirlingSecond_div_eq (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ i ∈ Finset.Icc k n,
        (MetaMathlibExt.signedStirlingFirst n i : ℚ) *
          (Nat.stirlingSecond i k : ℚ) / i =
      (-1 : ℚ) ^ (n - k) *
        ((n - 1).factorial : ℚ) / k.factorial *
        ∑ l ∈ Finset.range (n - k + 1),
          ((-1 : ℚ) ^ l / l.factorial) * MetaMathlibExt.bernoulliSecond l

/-- **Theorem 17**: for `r ≥ 1`, `∑_{k=0}^n (-1)^k
(k!/(k+r)) S(n,k) = (1/(r-1)!) ∑_{k=0}^{r-1}
|s(r,k+1)| B_{n+k}`, with `|s|` the unsigned Stirling
numbers of the first kind.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 17. -/
theorem_wanted sum_stirlingSecond_div_add (r n : ℕ)
    (hr : 1 ≤ r) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k *
        ((k.factorial : ℚ) / (k + r)) *
        (Nat.stirlingSecond n k : ℚ) =
      (1 / ((r - 1).factorial : ℚ)) *
        ∑ k ∈ Finset.range r,
          (Nat.stirlingFirst r (k + 1) : ℚ) * bernoulli (n + k)

/-- **Theorem 19**: for `r ≥ 1`, `∑_{k=0}^n s(n,k)/(k+r)
= ∑_{k=0}^{r-1} λ_{r,n,k} B_{n+k}^*` where
`λ_{r,n,k} = ∑_{ℓ=0}^{r-1-k} C(r-1,ℓ) S(r-1-ℓ,k) n^ℓ`.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 19. -/
theorem_wanted sum_signed_div_add (r n : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ Finset.range (n + 1),
        (MetaMathlibExt.signedStirlingFirst n k : ℚ) / (k + r) =
      ∑ k ∈ Finset.range r,
        (∑ l ∈ Finset.range (r - k), (Nat.choose (r - 1) l : ℚ) *
          (Nat.stirlingSecond (r - 1 - l) k : ℚ) * (n : ℚ) ^ l) *
        MetaMathlibExt.bernoulliSecond (n + k)

end MathlibExt.NumberTheory.BernoulliSecondKindWanted
