/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The maximum length for Ducci sequences on `ℤ_m^n` when `n` is even

Statements from Mark L. Lewis and Shannon M. Tefft, "The
Maximum Length for Ducci Sequences on `ℤ_m^n` when `n`
is Even", *INTEGERS* 26 (2026), Article A17
(<https://math.colgate.edu/~integers/aa17/aa17.pdf>).

The Ducci map on `ℤ_m^n` is `D(x)_i = x_i + x_{i+1}`
(indices cyclically); `ducciCoeff n r s` is the paper's
coefficient `a_{r,s}` of `x_s` in the first entry of
`D^r(x)`, i.e. `∑_{j ≡ s-1 (mod n)} C(r, j)` (equal to
`C(r, s-1)` for `r < n`, as the paper notes). Lemma 2 is
stated with upper index `p^k - p^{k-1}`: the extracted
`p^k - p^{k-1} - 1` gives binomial coefficients that are
never `0 mod p` on the checked grid, while with
`p^k - p^{k-1}` the stated case values hold for all
checked `p, k` and `j ≤ p^k - p^{k-1}` (it is the
Lucas-theorem computation); the range hypothesis is
necessary, since for `j` above the upper index the
binomial coefficient vanishes while the case value does
not (e.g. `p = 3`, `k = 2`, `j = 9`).
All statements were verified numerically (binomial
congruences for `p ≤ 7`; the predecessor criterion by
brute force for `m ∈ {2, 3, 4, 6}`, `n ∈ {2, 4}`).
Theorem 1 uses the paper's Definition 1 and Section 1:
`L_m(n) = Len(0, …, 0, 1)`, the least `α` such that
`D^{α+β}(u) = D^α(u)` for some `β ≥ 1`
(`ducciMaxLength`).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.DucciSequence
public import MathlibExt.NumberTheory.DucciCoefficientReduction

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.DucciWanted

/-- **Vanishing of Ducci coefficients modulo $p$.** For integers $N \ge 1$, $r \ge 0$ and $s \ge 1$
write $a^{(N)}_{r,s} = \sum_{0 \le j \le r,\ j \equiv s - 1 \ (\mathrm{mod}\ N)} \binom{r}{j}$ for
the Ducci coefficients of length $N$. Let $p$ be a prime, let $k \ge 0$ and $n_1 \ge 2$ be
integers, and let $n = p^k n_1$. Let $c \ge 1$, and let $s$ be an integer with $1 \le s \le n$
that is not of the form $b\,p^k + 1$ with $0 \le b < n_1$. Then
$a^{(n)}_{c p^k, s} \equiv 0 \pmod{p}$.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Lemma 3. -/
theorem_wanted ducciCoeff_vanish_mod (p k n1 c s : ℕ)
    (hp : p.Prime) (hn1 : 2 ≤ n1) (hc : 1 ≤ c)
    (hs1 : 1 ≤ s) (hs2 : s ≤ p ^ k * n1)
    (hs : ¬ ∃ b : ℕ, b < n1 ∧ s = b * p ^ k + 1) :
    ((ducciCoeff (p ^ k * n1) (c * p ^ k) s : ℤ) : ZMod p) = 0

/-- **Theorem 1 (1)**: for even `n` and `m ≥ 2` with
`gcd(n, m) = 1`, `L_m(n) = 1`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Theorem 1, part 1 (`integers-2026-A17-thm-1`). The
hypothesis `m ≥ 2` is added: for `m = 1` the basic tuple
is `0`, already in its cycle, so `L_1(n) = 0`. -/
theorem_wanted ducciMaxLength_eq_one_of_coprime (m n : ℕ) [NeZero m] [NeZero n] (hn : Even n)
    (hm : 2 ≤ m) (hnm : Nat.Coprime n m) :
    ducciMaxLength m n = 1

/-- **Theorem 1 (2)**: for even `n = p^k n₁` and
`m = p m₁` with `p` prime, `k ≥ 1`, `gcd(n₁, m₁) = 1` and
`p ∤ n₁, m₁`, `L_m(n) = p^k`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Theorem 1, part 2 (`integers-2026-A17-thm-1`). -/
theorem_wanted ducciMaxLength_eq_prime_pow (m n p k n₁ m₁ : ℕ) [NeZero m] [NeZero n] (hn : Even n)
    (hp : p.Prime) (hk : 1 ≤ k) (hn₁ : n = p ^ k * n₁) (hm₁ : m = p * m₁)
    (hcop : Nat.Coprime n₁ m₁) (hpn : ¬ p ∣ n₁) (hpm : ¬ p ∣ m₁) :
    ducciMaxLength m n = p ^ k

/-- **Theorem 1 (3)**: for even `n = p^k n₁` and
`m = p^l m₁` with `p` prime, `k, l ≥ 1`,
`gcd(n₁, m₁) = 1` and `p ∤ n₁, m₁`,
`L_m(n) ≤ p^{k-1} (l (p - 1) + 1)`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Theorem 1, part 3 (`integers-2026-A17-thm-1`). -/
theorem_wanted ducciMaxLength_le_prime_pow (m n p k l n₁ m₁ : ℕ) [NeZero m] [NeZero n] (hn : Even n)
    (hp : p.Prime) (hk : 1 ≤ k) (hl : 1 ≤ l) (hn₁ : n = p ^ k * n₁) (hm₁ : m = p ^ l * m₁)
    (hcop : Nat.Coprime n₁ m₁) (hpn : ¬ p ∣ n₁) (hpm : ¬ p ∣ m₁) :
    ducciMaxLength m n ≤ p ^ (k - 1) * (l * (p - 1) + 1)

/-- **Theorem 1 (4)**: for even `n = ∏ p_i^{k_i} n₁` and
`m = ∏ p_i^{l_i} m₁` with primes `p_1 < ⋯ < p_t`
(`t ≥ 1`), `k_i, l_i ≥ 1`, `gcd(n₁, m₁) = 1` and
`p_i ∤ n₁, m₁`, `L_m(n) = max_i L_{p_i^{l_i}}(n)`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Theorem 1, part 4 (`integers-2026-A17-thm-1`). The
exponents are taken positive as in parts 2 and 3; `t ≥ 1`
is needed for the maximum (for `t = 0` and `m ≥ 2`, part 1
gives `L_m(n) = 1`; for `m = 1` the length is `0`). -/
theorem_wanted ducciMaxLength_eq_sup (m n t n₁ m₁ : ℕ) [NeZero m] [NeZero n] (hn : Even n)
    (ht : 1 ≤ t) (p k l : Fin t → ℕ) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, 1 ≤ l i)
    (hn₁ : n = (∏ i, p i ^ k i) * n₁) (hm₁ : m = (∏ i, p i ^ l i) * m₁)
    (hcop : Nat.Coprime n₁ m₁) (hpn : ∀ i, ¬ p i ∣ n₁) (hpm : ∀ i, ¬ p i ∣ m₁) :
    ducciMaxLength m n = Finset.univ.sup fun i =>
      haveI : NeZero (p i ^ l i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
      ducciMaxLength (p i ^ l i) n

end MathlibExt.NumberTheory.DucciWanted
