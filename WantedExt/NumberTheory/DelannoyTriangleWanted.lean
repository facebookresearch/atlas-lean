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

Lemma 12 (quoted from Sun) uses Sun's generalized
central trinomial coefficients `T_n(b, c)`, defined in
`MathlibExt.NumberTheory.TrinomialCoefficient`
as `MetaMathlibExt.generalizedCentralTrinomial`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.NumberTheory.TrinomialCoefficient
public import WantedExt.Combinatorics.Enumerative.GeneralizedMotzkinModPWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix
public import MathlibExt.NumberTheory.BinomialHarmonicExpansion
public import MathlibExt.NumberTheory.DelannoyBinomialSum
public import MathlibExt.NumberTheory.DelannoyBinomialCongruence
public import MathlibExt.NumberTheory.DelannoyHarmonicCongruence
public import MathlibExt.NumberTheory.DelannoyPrimeCube
public import MathlibExt.NumberTheory.DelannoyPrimeCubeGeneralIndex
public import MathlibExt.NumberTheory.FermatQuotient
public import MathlibExt.NumberTheory.DelannoyTriangle

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.DelannoyTriangleWanted

/-- **Sums of $2^k/k$ and $2^k/k^2$ over $1 \le k \le p - 1$.** Let $p > 3$ be a prime and let
$q_p(2) = (2^{p-1} - 1)/p$ be the Fermat quotient of $2$. Then
$$\sum_{k=1}^{p-1} \frac{2^k}{k} \equiv -2\,q_p(2) \pmod{p^2}$$
and
$$\sum_{k=1}^{p-1} \frac{2^k}{k^2} \equiv -q_p(2)^2 \pmod{p},$$
where $1/k$ is the inverse of $k$ modulo $p^2$ and $1/k^2$ the inverse of $k^2$ modulo $p$.

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

/-- Bridge to the existing symmetric-case API: the constant
term of `(a x⁻¹ + b + a x)ⁿ`
(`MetaMathlibExt.centralTrinomial a b n`) is `T_n(b, a²)`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Section 4; Nadav Kohen, *Density and
Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Definitions. -/
theorem_wanted centralTrinomial_eq_generalizedCentralTrinomial
    (a b : ℤ) (n : ℕ) :
    MetaMathlibExt.centralTrinomial a b n =
      MetaMathlibExt.generalizedCentralTrinomial b (a ^ 2) n

/-- **Lemma 12** (Sun, Theorem 1.2(i)): for an odd prime
`p`, `b, c ∈ ℤ` and `m ≢ 0 (mod p)`,
`∑_{k=0}^{p-1} T_k(b, c) / m^k ≡ (((m - b)² - 4c)/p) (mod p)`,
with `1/m^k` read as `(m⁻¹)^k` in `ZMod p`.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Journal of Integer Sequences 29 (2026),
Article 26.5.2, Lemma 12 (quoting Z.-W. Sun, Sci. China
Math. 57 (2014), Theorem 1.2(i)). -/
theorem_wanted sum_generalizedCentralTrinomial_div_pow (p : ℕ)
    [Fact p.Prime] (hp2 : p ≠ 2) (b c m : ℤ) (hm : ¬ (p : ℤ) ∣ m) :
    (∑ k ∈ Finset.range p,
        (MetaMathlibExt.generalizedCentralTrinomial b c k : ZMod p) * ((m : ZMod p)⁻¹) ^ k) =
      (legendreSym p ((m - b) ^ 2 - 4 * c) : ZMod p)

end MathlibExt.NumberTheory.DelannoyTriangleWanted
