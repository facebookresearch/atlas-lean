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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.DucciWanted

/-- The coefficient `a_{r,s}` of `x_s` (`1 ≤ s ≤ n`) in
the first entry of the `r`-th iterate of the Ducci map
on `ℤ_m^n`, as an integer count:
`∑_{j ≡ s - 1 (mod n)} C(r, j)`. -/
def ducciCoeff (n r s : ℕ) : ℕ :=
  ∑ j ∈ (Finset.range (r + 1)).filter
    (fun j => j % n = (s - 1) % n), Nat.choose r j

/-- **Lemma 1**: for prime `p`, `k ≥ 1`, and
`j ≤ p^k - 1`, `C(p^k - 1, j) ≡ (-1)^j (mod p)`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Lemma 1. -/
theorem_wanted choose_prime_pow_sub_one_mod (p k j : ℕ)
    (hp : p.Prime) (hk : 1 ≤ k) (hj : j ≤ p ^ k - 1) :
    ((Nat.choose (p ^ k - 1) j : ℤ) : ZMod p) = (-1) ^ j

/-- **Lemma 2**: for an odd prime `p`, `k > 1`, and
`j ≤ p^k - p^{k-1}`,
`C(p^k - p^{k-1}, j) ≡ (-1)^c (mod p)` if
`j = c * p^{k-1}` for some `c`, and `≡ 0 (mod p)`
otherwise.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Lemma 2. -/
theorem_wanted choose_prime_pow_sub_mod (p k j : ℕ)
    (hp : p.Prime) (hpo : p ≠ 2) (hk : 2 ≤ k)
    (hj : j ≤ p ^ k - p ^ (k - 1)) :
    ((Nat.choose (p ^ k - p ^ (k - 1)) j : ℤ) : ZMod p) =
      if j % p ^ (k - 1) = 0 then (-1) ^ (j / p ^ (k - 1))
      else 0

/-- **Lemma 3**: let `n = p^k * n₁` with `p` prime and
`n₁ > 1`. For `c ≥ 1` and `s` not of the form
`b * p^k + 1` with `0 ≤ b < n₁`, `a_{c * p^k, s} ≡ 0
(mod p)`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Lemma 3. -/
theorem_wanted ducciCoeff_vanish_mod (p k n1 c s : ℕ)
    (hp : p.Prime) (hn1 : 2 ≤ n1) (hc : 1 ≤ c)
    (hs1 : 1 ≤ s) (hs2 : s ≤ p ^ k * n1)
    (hs : ¬ ∃ b : ℕ, b < n1 ∧ s = b * p ^ k + 1) :
    ((ducciCoeff (p ^ k * n1) (c * p ^ k) s : ℤ) : ZMod p) = 0

/-- **Lemma 4**: with `n = p^k * n₁` as in Lemma 3, for
`c ≥ 1` and `0 ≤ b < n₁`,
`a_{c * p^k, b * p^k + 1} ≡ a*_{c, b + 1} (mod p)`, where
`a*` denotes the coefficients for `n₁`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Lemma 4. -/
theorem_wanted ducciCoeff_reduce_mod (p k n1 c b : ℕ)
    (hp : p.Prime) (hn1 : 2 ≤ n1) (hc : 1 ≤ c) (hb : b < n1) :
    ((ducciCoeff (p ^ k * n1) (c * p ^ k) (b * p ^ k + 1) : ℤ) :
      ZMod p) =
      ((ducciCoeff n1 c (b + 1) : ℤ) : ZMod p)

/-- **Theorem 2**: for even `n`, a tuple
`x ∈ ℤ_m^n` has a Ducci predecessor (a tuple `y` with
`y_i + y_{i+1} = x_i` for all `i`, indices cyclically)
if and only if the alternating sum
`x_1 - x_2 + ⋯ + x_{n-1} - x_n` vanishes in `ℤ_m`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Theorem 2. -/
theorem_wanted ducci_pred_iff (m n : ℕ) [NeZero n]
    (hn : Even n) (x : Fin n → ZMod m) :
    (∃ y : Fin n → ZMod m, ∀ i : Fin n, y i + y (i + 1) = x i) ↔
      ∑ i : Fin n, (-1 : ZMod m) ^ i.val * x i = 0

/-- The Ducci map on `ℤ_m^n`:
`D(x)_i = x_i + x_{i+1}`, indices cyclic.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Section 1. -/
def ducciMap (m n : ℕ) [NeZero n] (x : Fin n → ZMod m) : Fin n → ZMod m :=
  fun i => x i + x (i + 1)

/-- The basic tuple `(0, …, 0, 1) ∈ ℤ_m^n`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Section 1 (basic Ducci sequence). -/
def ducciBasic (m n : ℕ) [NeZero n] : Fin n → ZMod m :=
  fun i => if i.val = n - 1 then 1 else 0

/-- `L_m(n) = Len(0, …, 0, 1)`: the least `α` such that
`D^{α+β}(u) = D^α(u)` for some `β ≥ 1`, `u` the basic
tuple. The modulus is positive (`[NeZero m]`), so `ℤ_m^n` is
finite and such `α` exists; for `m = 0` the sequence in
`ℤ^n` need not recur.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Definition 1 and Section 1. -/
noncomputable def ducciMaxLength (m n : ℕ) [NeZero m] [NeZero n] : ℕ :=
  sInf {α | ∃ β, 1 ≤ β ∧
    (ducciMap m n)^[α + β] (ducciBasic m n) = (ducciMap m n)^[α] (ducciBasic m n)}

/-- Characteristic value: in `ℤ_5^4`, `D(0, 0, 0, 1) = (0, 0, 1, 1)`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Section 1 (example). -/
theorem ducciMap_basic_five_four :
    ducciMap 5 4 (ducciBasic 5 4) = ![0, 0, 1, 1] := by
  decide

/-- `L_m(n)` is at most any `α` that returns after some
`β ≥ 1` steps.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Definition 1. -/
theorem ducciMaxLength_le {m n : ℕ} [NeZero m] [NeZero n] {α β : ℕ} (hβ : 1 ≤ β)
    (h : (ducciMap m n)^[α + β] (ducciBasic m n) = (ducciMap m n)^[α] (ducciBasic m n)) :
    ducciMaxLength m n ≤ α :=
  Nat.sInf_le ⟨β, hβ, h⟩

/-- Characteristic value: `L_5(4) ≤ 1`, from the paper's
example `D^5(0, 0, 0, 1) = D(0, 0, 0, 1)` in `ℤ_5^4`.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
INTEGERS 26 (2026), Article A17, Section 1 (example). -/
theorem ducciMaxLength_five_four_le : ducciMaxLength 5 4 ≤ 1 :=
  ducciMaxLength_le (β := 4) (by decide) (by decide)

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
