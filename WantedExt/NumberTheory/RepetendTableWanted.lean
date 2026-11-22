/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Repetend tables

Statements from R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*,
INTEGERS 25 (2025), Article A26. The `j`-th base-`B` digit of `m/n` is written
`m * B ^ (j + 1) / n % B`; `E(L, n)` is the number of units of order `L` in `ZMod n`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Raising the base by multiples of `n` shifts each repetend digit linearly: for the `j`-th digit
`⌊m B^(j+1) / n⌋ mod B` of `m/n` in base `B`, there is `c < n` with
`digit_j(b + t n) = digit_j(b) + t c` for every `t ≥ 0`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Corollary 3 (`integers-2025-A26-cor-3`). -/
public theorem_wanted digit_add_mul_modulus_eq (m n b j : ℕ) (hn : 0 < n) (hb : 2 ≤ b) :
    ∃ c < n, ∀ t : ℕ,
      m * (b + t * n) ^ (j + 1) / n % (b + t * n) = m * b ^ (j + 1) / n % b + t * c

/-- The number `E(L, n)` of elements of order `L` in `(ℤ/nℤ)ˣ` is a multiple of `φ(L)`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Corollary 4 (`integers-2025-A26-cor-4`). -/
public theorem_wanted totient_dvd_card_orderOf_eq (L n : ℕ) [NeZero n] : L.totient ∣
    (Finset.univ.filter fun u : (ZMod n)ˣ => orderOf u = L).card

/-- If `E(L, n) = φ(L)` and `L ≥ 2` is even, then `n = 4, L = 2`, or `n = t q` with `t ∈ {1, 2}`,
`q` an odd prime power and `L ∣ φ(q)`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Corollary 5 (`integers-2025-A26-cor-5`). -/
public theorem_wanted card_orderOf_eq_totient_classification (L n : ℕ) [NeZero n] (hL0 : 0 < L)
    (hE : (Finset.univ.filter fun u : (ZMod n)ˣ => orderOf u = L).card = L.totient) (hL : 2 ∣ L) :
    (n = 4 ∧ L = 2) ∨
      ∃ t q : ℕ, (t = 1 ∨ t = 2) ∧ n = t * q ∧ Odd q ∧ IsPrimePow q ∧ L ∣ q.totient

/-- The number `E(2, n)` of elements of order `2` in `(ℤ/nℤ)ˣ` is a power of `2` minus `1`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Corollary 6 (`integers-2025-A26-cor-6`). -/
public theorem_wanted card_orderOf_eq_two_eq_two_pow_sub_one (n : ℕ) [NeZero n] :
    ∃ k : ℕ, (Finset.univ.filter fun u : (ZMod n)ˣ => orderOf u = 2).card = 2 ^ k - 1

/-- If `n = p^k` with `p ≡ 1 (mod 6)` prime and `b` has multiplicative order `6` modulo `n`, then
`b ≢ 0, 1/2, ±1, 2 (mod n)`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 16 (`integers-2025-A26-lem-16`). -/
public theorem_wanted orderOf_eq_six_ne_small_residues (p k : ℕ) (hp : p.Prime) (hp6 : p % 6 = 1)
    (hk : 0 < k) (b : ZMod (p ^ k))
    (hb : orderOf b = 6) :
    b ≠ 0 ∧ 2 * b ≠ 1 ∧ b ≠ 1 ∧ b ≠ -1 ∧ b ≠ 2

/-- For `Q = p^j`, `c_i(z) = ((g_i z + f_i) mod Q) + e_i` with `g_1, g_2, g_2 - g_1` prime to `p`,
residues `0 ≤ f_1 ≤ f_2 < Q`, `0 ≤ g_i < Q` and reals `0 < e_1 < e_2 < 1`, the sign of
`d(z) = c_2(z) - c_1(z)` is `+1` and `-1` equally often on (a) `1 ≤ z ≤ Q - 1` and (b)
`1 ≤ z ≤ Q - 1`, `p ∤ z`, the latter when `f_1 ≡ 0` or `f_1 ≡ f_2 (mod p)`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 7 (`integers-2025-A26-thm-7`). -/
public theorem_wanted sign_balance_shifted_linear_residues (p j : ℕ) (hp : p.Prime) (hj : 0 < j)
    (g₁ g₂ f₁ f₂ : ℕ) (hg₁ : g₁ < p ^ j)
    (hg₂ : g₂ < p ^ j) (hf : f₁ ≤ f₂) (hf₂ : f₂ < p ^ j) (hcop₁ : ¬ p ∣ g₁)
    (hcop₂ : ¬ p ∣ g₂) (hcop : ¬ (p : ℤ) ∣ (g₂ : ℤ) - g₁) (e₁ e₂ : ℝ) (he₁ : 0 < e₁)
    (he : e₁ < e₂) (he₂ : e₂ < 1) :
    let d : ℕ → ℝ := fun z =>
      ((((g₂ * z + f₂) % p ^ j : ℕ) : ℝ) + e₂) - ((((g₁ * z + f₁) % p ^ j : ℕ) : ℝ) + e₁)
    ((Finset.Icc 1 (p ^ j - 1)).filter (fun z => 0 < d z)).card =
        ((Finset.Icc 1 (p ^ j - 1)).filter (fun z => d z < 0)).card ∧
      (f₁ % p = 0 ∨ f₁ % p = f₂ % p →
        ((Finset.Icc 1 (p ^ j - 1)).filter (fun z => ¬ p ∣ z ∧ 0 < d z)).card =
          ((Finset.Icc 1 (p ^ j - 1)).filter (fun z => ¬ p ∣ z ∧ d z < 0)).card)

/-- Block sums of a repetend: let `x/N = ∑ a_i B^(-i-1)` be purely periodic with period `e = dk`,
`A_j = ∑_{i<k} a_(jk+i) B^(k-1-i)`, `S_d(x) = ∑_{j<d} A_j`, `x_j = x B^j mod N` and
`R_d(x) = ∑_{j<d} x_(jk)`. Then (a) `S_d(x) = R_d(x)(B^k - 1)/N`, and (b) if
`gcd(B^k - 1, N) = 1` then `S_d(x) ≡ 0 (mod B^k - 1)`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 9 (`integers-2025-A26-thm-9`). -/
public theorem_wanted repetend_block_sum_eq (B N x d k : ℕ) (hB : 2 ≤ B) (hx : x < N) (hd : 0 < d)
    (hk : 0 < k)
    (hper : ∀ i, x * B ^ (i + d * k + 1) / N % B = x * B ^ (i + 1) / N % B) :
    let a : ℕ → ℕ := fun i => x * B ^ (i + 1) / N % B
    let S := ∑ j ∈ Finset.range d, ∑ i ∈ Finset.range k, a (j * k + i) * B ^ (k - 1 - i)
    let R := ∑ j ∈ Finset.range d, x * B ^ (j * k) % N
    S * N = R * (B ^ k - 1) ∧ (Nat.Coprime (B ^ k - 1) N → B ^ k - 1 ∣ S)


/-- Long division of `m/n` in base `b`: with remainders `c_j = m b^j mod n` and digits
`r_j = ⌊b c_j / n⌋`, every truncation satisfies
`m/n = ∑_{i<k} r_i b^{-i-1} + c_k/(n b^k)`, and `r_j = (b c_j - c_{j+1})/n`. Stated for a
proper fraction `m < n` (needed for `k = 0`) and every base `b ≥ 1`; the identity
`r_j = (b c_j - c_{j+1})/n` is stated with the division cleared.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 5 (`integers-2025-A26-lem-5`). -/
public theorem_wanted long_division_remainder_expansion (m n b : ℕ) (hmn : m < n) (hb : 0 < b) :
    let c : ℕ → ℕ := fun j => m * b ^ j % n
    let r : ℕ → ℕ := fun j => b * c j / n
    (∀ k : ℕ, (m : ℚ) / n =
      ∑ i ∈ Finset.range k, (r i : ℚ) / (b : ℚ) ^ (i + 1) + (c k : ℚ) / ((n : ℚ) * (b : ℚ) ^ k)) ∧
    ∀ j : ℕ, r j * n = b * c j - c (j + 1)

/-- The last repetend digit of `1/n` is nonzero: for `n ≥ 2` and a base `b ≥ 2` prime to `n`,
with repetend length `L = ord_n(b)`, the digit `⌊b^((L-1)+1)/n⌋ mod b` at position `L - 1` is
not `0`. Stated for every such base (the paper's table rows are its small bases).

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 25 (`integers-2025-A26-lem-25`). -/
public theorem_wanted repetend_last_digit_ne_zero (n b : ℕ) (hn : 2 ≤ n) (hb : 2 ≤ b)
    (hcop : Nat.Coprime b n) :
    b ^ (orderOf (b : ZMod n) - 1 + 1) / n % b ≠ 0

/-- If `b_2 = b^2 + u n` with `u ∈ ℤ` and `2 ≤ b_2 ≤ n - 2`, then `b ≠ u + 1`. Stated for every
natural `b` (the paper's `b` is a small base).

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 31 (`integers-2025-A26-lem-31`). -/
public theorem_wanted ne_add_one_of_sq_add_mul_mem (n b : ℕ) (u : ℤ)
    (h2 : 2 ≤ (b : ℤ) ^ 2 + u * n) (hn : (b : ℤ) ^ 2 + u * n ≤ n - 2) :
    (b : ℤ) ≠ u + 1

/-- For a prime `n`, a prime `L` and a base `b` of repetend length `L = ord_n(b)`: if `m = 1`
or `m` is a small base `2 ≤ m ≤ n - 1` of length `L`, the long-division remainders
`c_j = m b^j mod n` (`0 ≤ j < L`, one period), with `1` removed, are exactly the small bases
`2 ≤ a ≤ n - 1` of length `L`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Corollary 2 (`integers-2025-A26-cor-2`). -/
public theorem_wanted long_division_remainders_erase_one_eq_small_bases (n L b m : ℕ)
    (hn : n.Prime) (hL : L.Prime) (hb : orderOf (b : ZMod n) = L)
    (hm : m = 1 ∨ (m ∈ Finset.Icc 2 (n - 1) ∧ orderOf (m : ZMod n) = L)) :
    ((Finset.range L).image fun j => m * b ^ j % n).erase 1 =
      (Finset.Icc 2 (n - 1)).filter fun a : ℕ => orderOf (a : ZMod n) = L

/-- For every modulus `n`, the number of small bases `1 ≤ b < n`, `gcd(b, n) = 1`, of repetend
length (multiplicative order) `L > 2` is even. The record's first sentence (Lemma 2: `b^x` has
order `L` iff `gcd(x, L) = 1`) is Mathlib `IsOfFinOrder.orderOf_pow` and is not restated.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 3 (`integers-2025-A26-lem-2`). -/
public theorem_wanted even_card_small_bases_orderOf (n L : ℕ) (hL : 2 < L) :
    Even ((Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L).card

/-- Repetend digit formula symmetry: let `b` have order `L` modulo `n`, `b_x = b^x mod n`, and
`r_{x,j} = ⌊b_x^(j+1)/n⌋ mod b_x` the `j`-th base-`b_x` digit of `1/n`. If `j` is prime to `L` and
`j j' ≡ 1 (mod L)`, then `r_{xj, j'} = r_{x, j}`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 6 (`integers-2025-A26-lem-6`). -/
public theorem_wanted repetend_digit_pow_mul_eq_of_mul_modEq_one (n b L x j j' : ℕ) (hL : 0 < L)
    (hb : orderOf (b : ZMod n) = L) (hj : Nat.Coprime j L) (hjj : j * j' ≡ 1 [MOD L]) :
    (b ^ (x * j) % n) ^ (j' + 1) / n % (b ^ (x * j) % n) = (b ^ x % n) ^ (j + 1) / n % (b ^ x % n)

/-- Class A column matches: in the repetend table of `1/n` whose rows are the small bases
`1 ≤ b < n` of order `L` and whose column `j` holds the digits `⌊b^(j+1)/n⌋ mod b`, if `j` is prime
to `L`, `j^2 ≢ 1 (mod L)` and `j j' ≡ 1 (mod L)`, then columns `j` and `j'` are equal as multisets.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 2 (`integers-2025-A26-thm-2`). -/
public theorem_wanted repetend_column_eq_column_of_mul_modEq_one (n L j j' : ℕ) (hL : 0 < L)
    (hj : Nat.Coprime j L) (hjsq : ¬ j ^ 2 ≡ 1 [MOD L]) (hjj : j * j' ≡ 1 [MOD L]) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L
    (B.val.map fun b => b ^ (j + 1) / n % b) = B.val.map fun b => b ^ (j' + 1) / n % b

/-- The number of Class A columns: if `L = 2^e · (odd part)` with `f` distinct odd prime factors,
the number of `0 ≤ j < L` prime to `L` with `j^2 ≢ 1 (mod L)` is `φ(L) - 2^(f + g(e))`,
`g(e) = max(0, min(2, e - 1))`. These columns pair off as `{j, j⁻¹}`, so this count is `2 P(L)`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 2 (`integers-2025-A26-thm-2`). -/
public theorem_wanted card_coprime_not_sq_modEq_one (L : ℕ) (hL : 0 < L) :
    ((Finset.range L).filter fun j => Nat.Coprime j L ∧ ¬ j ^ 2 ≡ 1 [MOD L]).card =
      L.totient - 2 ^ ((L.primeFactors.filter Odd).card + min 2 (L.factorization 2 - 1))

/-- The final column `L - 1` of the repetend table of `1/n` pairs each small base `b` of order `L`
with `b^(L-1) mod n = b⁻¹`: the two rows have the same digit in column `L - 1`. Here `b < n` is a
small base, as in the table.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 2 (`integers-2025-A26-thm-2`). -/
public theorem_wanted repetend_last_column_inv_eq (n L b : ℕ) (hL : 0 < L) (hbn : b < n)
    (hb : orderOf (b : ZMod n) = L) :
    (b ^ (L - 1) % n) ^ (L - 1 + 1) / n % (b ^ (L - 1) % n) = b ^ (L - 1 + 1) / n % b

/-- Class B column matches: let `L = 12a + 6` with `a > 0`, `n = p^k` with `p ≡ 1 (mod L)` prime,
`b` a small base of order `L`, `b_i = b^i mod n` and `k_i = (b_i + b_(i+L/3) + b_(i+2L/3))/n`.
Then `k_i = 1` for all `i` prime to `L` iff columns `2a + 1, 4a + 2` match and columns
`8a + 4, 10a + 5` match (columns as in Theorem 2). The conjectured proportion is omitted.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 4 (`integers-2025-A26-thm-4`). -/
public theorem_wanted repetend_columns_match_iff_triple_sum_eq (p k a b : ℕ) (hp : p.Prime)
    (hk : 0 < k) (ha : 0 < a) (hpL : p % (12 * a + 6) = 1)
    (hb : orderOf (b : ZMod (p ^ k)) = 12 * a + 6) :
    let n := p ^ k
    let L := 12 * a + 6
    let B := (Finset.Ico 1 n).filter fun c => Nat.Coprime c n ∧ orderOf (c : ZMod n) = L
    let C : ℕ → Multiset ℕ := fun j => B.val.map fun c => c ^ (j + 1) / n % c
    (∀ i < L, Nat.Coprime i L →
        (b ^ i % n + b ^ (i + L / 3) % n + b ^ (i + 2 * L / 3) % n) / n = 1) ↔
      (C (2 * a + 1) = C (4 * a + 2) ∧ C (8 * a + 4) = C (10 * a + 5))

/-- Digit differences: with `b_x = b^x mod n` and `r_{x,j} = ⌊b_x^(j+1)/n⌋ mod b_x`,
`n (r_{ym,e} - r_{y,d}) = b_{ym} b_{yme} - b_{ym(e+1)} - b_y b_{yd} + b_{y(d+1)}`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 7 (`integers-2025-A26-lem-7`). -/
public theorem_wanted repetend_digit_sub_eq (n b y m d e : ℕ) (hn : 0 < n) (hb : Nat.Coprime b n) :
    let r : ℕ → ℕ → ℕ := fun x j => (b ^ x % n) ^ (j + 1) / n % (b ^ x % n)
    (n : ℤ) * ((r (y * m) e : ℤ) - r y d) =
      ((b ^ (y * m) % n : ℕ) : ℤ) * (b ^ (y * m * e) % n : ℕ) - (b ^ (y * m * (e + 1)) % n : ℕ) -
        ((b ^ y % n : ℕ) : ℤ) * (b ^ (y * d) % n : ℕ) + (b ^ (y * (d + 1)) % n : ℕ)

/-- Class C setting (`n = p^i` with `p ≡ 1 (mod 6)` prime, `Q = p^j`, `j ≥ 1`, `i ≥ 2j`, `B` of
order `L = 6Q` mod `n`):
`B^2 - B + 1 = M` with `p`-adic valuation exactly `i - j` (so `M = l p^(i-j)`, `p ∤ l`).

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 8 (`integers-2025-A26-lem-8`). -/
public theorem_wanted padicValNat_sq_sub_add_one_of_orderOf_eq (p i j B : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1)
    (hj : 0 < j) (hij : 2 * j ≤ i) (hB : orderOf (B : ZMod (p ^ i)) = 6 * p ^ j) :
    padicValNat p (B ^ 2 - B + 1) = i - j

/-- Class C setting (`p ≡ 1 (mod 6)`): if `0 ≤ z < 6Q` with `z ≡ 2 (mod 6)` and
`z ≡ B⁻¹ (mod Q)`, or `z ≡ 1 - B (mod Q)`, then `B^z ≡ B - 1 (mod n)`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 9 (`integers-2025-A26-lem-9`). -/
public theorem_wanted pow_mod_eq_sub_one_of_orderOf_eq (p i j B z : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hj : 0 < j)
    (hij : 2 * j ≤ i) (hBn : B < p ^ i) (hB : orderOf (B : ZMod (p ^ i)) = 6 * p ^ j)
    (hzL : z < 6 * p ^ j) (hz6 : z ≡ 2 [MOD 6])
    (hzQ : z * B ≡ 1 [MOD p ^ j] ∨ (z : ℤ) ≡ 1 - B [ZMOD p ^ j]) :
    B ^ z % p ^ i = B - 1

/-- Class C setting: if `y ≡ s (mod 6)` then `b^y ≡ b^s (mod Q)`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 10 (`integers-2025-A26-lem-10`). -/
public theorem_wanted pow_modEq_pow_of_modEq_six (p i j b y s : ℕ) (hp : p.Prime) (hj : 0 < j)
    (hij : 2 * j ≤ i) (hb : orderOf (b : ZMod (p ^ i)) = 6 * p ^ j) (hys : y ≡ s [MOD 6]) :
    b ^ y ≡ b ^ s [MOD p ^ j]

/-- Class C setting (`p ≡ 1 (mod 6)`): let `f = ±1`, `d ≡ 2f (mod 6)`, `B = b^y mod n` with
`y ≡ s = ±1 (mod 6)`, and
`k ∈ [0, 6Q)` with `k ≡ b^(sf) d (mod Q)`, `k ≡ f (mod 6)`. Then `B^k mod n = (B^d mod n) + 1`.
Here `b^(-1) mod Q` is written `b^5` (`b^6 ≡ 1 (mod Q)` by Lemma 10).

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 11 (`integers-2025-A26-lem-11`). -/
public theorem_wanted pow_mod_eq_pow_mod_add_one_of_crt (p i j b y d k : ℕ) (f : ℤ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hj : 0 < j) (hij : 2 * j ≤ i) (hb : orderOf (b : ZMod (p ^ i)) = 6 * p ^ j)
    (hf : f = 1 ∨ f = -1) (hy : y % 6 = 1 ∨ y % 6 = 5) (hd : (d : ℤ) ≡ 2 * f [ZMOD 6])
    (hk : k < 6 * p ^ j) (hk6 : (k : ℤ) ≡ f [ZMOD 6])
    (hkQ : k ≡ b ^ (if (y % 6 = 1 ↔ f = 1) then 1 else 5) * d [MOD p ^ j]) :
    (b ^ y % p ^ i) ^ k % p ^ i = (b ^ y % p ^ i) ^ d % p ^ i + 1

/-- For `n = p^i` (`p ≡ 1 (mod 6)` prime), `Q = p^j` and `B` of order `6Q` mod `n`, with
`B_z = B^z mod n` and
`B_(-Q) = B_(5Q)`: (a) `B_(2Q) = B_Q - 1`, `B_(-2Q) = B_(-Q) - 1`; (b) `B_Q + B_(-Q) = n + 1`;
(c) `B_(3Q) = n - 1`; (d) `Q^2 ≡ Q (mod 6Q)`. Stated for every `i, j` (the paper's `j ≥ 1`,
`i ≥ 2j` are not needed).

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 13 (`integers-2025-A26-lem-13`). -/
public theorem_wanted pow_mod_relations_of_orderOf_eq_six_mul (p i j B : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1)
    (hB : orderOf (B : ZMod (p ^ i)) = 6 * p ^ j) :
    let n := p ^ i
    let Q := p ^ j
    B ^ (2 * Q) % n = B ^ Q % n - 1 ∧ B ^ (4 * Q) % n = B ^ (5 * Q) % n - 1 ∧
      B ^ Q % n + B ^ (5 * Q) % n = n + 1 ∧ B ^ (3 * Q) % n = n - 1 ∧ Q ^ 2 ≡ Q [MOD 6 * Q]

/-- For `n = p^i` (`p ≡ 1 (mod 6)` prime), `Q = p^j`, a small base `B` of order `L = 6Q`,
`f = ±1`, `d ≡ 2fQ` and
`e ≡ fQ (mod L)`: with multiplier `m_s = 1` the digit difference `D = n (r_e - r_d)`
(`r_j = ⌊B^(j+1)/n⌋ mod B`) equals `B + B_(d+1) - B_(e+1)` and lies in `{0, n}`. Stated for every
`i, j`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 14 (`integers-2025-A26-lem-14`). -/
public theorem_wanted repetend_digit_sub_mem_zero_n (p i j B d e : ℕ) (f : ℤ) (hp : p.Prime)
    (hp6 : p % 6 = 1)
    (hBn : B < p ^ i) (hB : orderOf (B : ZMod (p ^ i)) = 6 * p ^ j) (hf : f = 1 ∨ f = -1)
    (hd : (d : ℤ) ≡ 2 * f * p ^ j [ZMOD 6 * p ^ j]) (he : (e : ℤ) ≡ f * p ^ j [ZMOD 6 * p ^ j]) :
    let n := p ^ i
    let D : ℤ := (n : ℤ) * (((B ^ (e + 1) / n % B : ℕ) : ℤ) - (B ^ (d + 1) / n % B : ℕ))
    D = B + (B ^ (d + 1) % n : ℕ) - (B ^ (e + 1) % n : ℕ) ∧ (D = 0 ∨ D = n)

/-- Class C: for `n = p^i` (`p ≡ 1 (mod 6)` prime), `Q = p^j` (`j ≥ 1`, `i ≥ 2j`) and a small
base `b` of order `L = 6Q`,
let `d, e ∈ [0, L)` with `d ≡ b^2`, `e ≡ b^4 (mod Q)` and `d ≡ e ≡ 4 (mod 6)`. Then columns `d`
and `e` of the repetend table of `1/n` are equal as multisets (the sorted columns coincide). The
`D_s = 0` clause, which needs the multiplier `m_s`, is omitted.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 6 (`integers-2025-A26-thm-6`). -/
public theorem_wanted repetend_columns_eq_of_crt_sq (p i j b d e : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hj : 0 < j)
    (hij : 2 * j ≤ i) (hb : orderOf (b : ZMod (p ^ i)) = 6 * p ^ j) (hdL : d < 6 * p ^ j)
    (heL : e < 6 * p ^ j) (hdQ : d ≡ b ^ 2 [MOD p ^ j]) (heQ : e ≡ b ^ 4 [MOD p ^ j])
    (hd6 : d ≡ 4 [MOD 6]) (he6 : e ≡ 4 [MOD 6]) :
    let n := p ^ i
    let B := (Finset.Ico 1 n).filter fun c => Nat.Coprime c n ∧ orderOf (c : ZMod n) = 6 * p ^ j
    (B.val.map fun c => c ^ (d + 1) / n % c) = B.val.map fun c => c ^ (e + 1) / n % c

/-- If the repetend length is `L ≤ 2` (and some small base has that length), no two distinct
columns of the repetend table of `1/n` match.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 26 (`integers-2025-A26-lem-26`). -/
public theorem_wanted repetend_columns_ne_of_le_two (n L : ℕ) (hL : L ≤ 2) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L
    B.Nonempty → ∀ i < L, ∀ j < L, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- If the number of rows `n_r` (small bases of order `L`) is `1` or `3`, no two distinct columns
of the repetend table of `1/n` match.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 27 (`integers-2025-A26-lem-27`). -/
public theorem_wanted repetend_columns_ne_of_card_eq_one_or_three (n L : ℕ) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L
    (B.card = 1 ∨ B.card = 3) → ∀ i < L, ∀ j < L, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- If `n_r = 2`, with rows `b ≠ b'` and `D_i = r_{b',i} - r_{b,i}`, `S_i` the column sum: if
columns `i` and `j` match then `D_i = ±D_j` and `S_i = S_j`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 28 (`integers-2025-A26-lem-28`). -/
public theorem_wanted repetend_digit_diff_of_columns_eq (n L b b' i j : ℕ) :
    let B := (Finset.Ico 1 n).filter fun c => Nat.Coprime c n ∧ orderOf (c : ZMod n) = L
    let C : ℕ → Multiset ℕ := fun k => B.val.map fun c => c ^ (k + 1) / n % c
    let D : ℕ → ℤ := fun k => ((b' ^ (k + 1) / n % b' : ℕ) : ℤ) - (b ^ (k + 1) / n % b : ℕ)
    B.card = 2 → b ∈ B → b' ∈ B → b ≠ b' → C i = C j →
      (D i = D j ∨ D i = -D j) ∧ (C i).sum = (C j).sum

/-- If `L` is even, `(ℤ/nℤ)ˣ` is cyclic and `b` is a small base of order `L`, then
`b_(j+L/2) = n - b_j` (`b_j = b^j mod n`) and the digits `r_j = ⌊b^(j+1)/n⌋ mod b` satisfy
`r_j + r_(j+L/2) = r_(L/2)`; summing over rows gives the column relations
`C_j + C_(j+L/2) = C_(L/2)`, `S_j + S_(j+L/2) = S_(L/2)`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 29 (`integers-2025-A26-lem-29`). -/
public theorem_wanted pow_add_half_mod_eq_and_digit_add (n L b j : ℕ) [IsCyclic (ZMod n)ˣ]
    (hL : Even L) (hL0 : 0 < L) (hbn : b < n) (hb : orderOf (b : ZMod n) = L) :
    b ^ (j + L / 2) % n = n - b ^ j % n ∧
      b ^ (j + 1) / n % b + b ^ (j + L / 2 + 1) / n % b = b ^ (L / 2 + 1) / n % b

/-- If `n_r = 2` and `L = 3`, no two distinct columns of the repetend table of `1/n` match.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 30 (`integers-2025-A26-lem-30`). -/
public theorem_wanted repetend_columns_ne_of_card_two_of_three (n : ℕ) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 3
    B.card = 2 → ∀ i < 3, ∀ j < 3, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- If `n_r = 2` and `L = 4`, no two distinct columns of the repetend table of `1/n` match.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 32 (`integers-2025-A26-lem-32`). -/
public theorem_wanted repetend_columns_ne_of_card_two_of_four (n : ℕ) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 4
    B.card = 2 → ∀ i < 4, ∀ j < 4, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- If exactly two small bases have order `6` modulo `n`, then `n = 3^k t ≥ 9` or `n = p^k t` with
`p ≡ 1 (mod 6)` prime, `k ≥ 1`, and `t ∈ {1, 2}`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 33 (`integers-2025-A26-lem-33`). -/
public theorem_wanted eq_of_card_small_bases_orderOf_six_eq_two (n : ℕ)
    (h : ((Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6).card = 2) :
    (∃ k t : ℕ, (t = 1 ∨ t = 2) ∧ n = 3 ^ k * t ∧ 9 ≤ n) ∨
      ∃ p k t : ℕ, p.Prime ∧ p % 6 = 1 ∧ 0 < k ∧ (t = 1 ∨ t = 2) ∧ n = p ^ k * t

/-- If `n = 3^k t` with `k ≥ 2`, `t ∈ {1, 2}` and `L = 6`, no two distinct columns of the repetend
table of `1/n` match.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 34 (`integers-2025-A26-lem-34`). -/
public theorem_wanted repetend_columns_ne_of_three_pow_of_six (k t : ℕ) (hk : 2 ≤ k)
    (ht : t = 1 ∨ t = 2) :
    let n := 3 ^ k * t
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6
    ∀ i < 6, ∀ j < 6, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- For `n = t p^k` (`t ∈ {1, 2}`, `p ≡ 1 (mod 6)` prime, `k ≥ 1`) and a small base `b_1` of order
`6`, put `hn = 0` if `t = 1`, `hn = p^k` if `t = 2, b_1 < p^k`, `hn = -p^k` if `t = 2, b_1 > p^k`,
and `b_j = b_1^j mod n`. Then for some integer `u`: `b_2 = b_1 - 1 + hn`, `b_3 = n - 1`,
`b_4 = n - b_1`, `b_5 = n - b_1 + 1 - hn`, `b_1^2 = un + b_1 - 1 + hn`,
`b_2^2 = un - b_1 + (hn + 2b_1 - 1) hn`, `b_1 b_2 = un - 1 + (b_1 + 1) hn`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 35 (`integers-2025-A26-lem-35`). -/
public theorem_wanted pow_mod_eqs_of_orderOf_eq_six (p k t b₁ : ℕ) (hp : p.Prime) (hp6 : p % 6 = 1)
    (hk : 0 < k) (ht : t = 1 ∨ t = 2) (hb₁ : b₁ < t * p ^ k)
    (hb : orderOf (b₁ : ZMod (t * p ^ k)) = 6) :
    let n := t * p ^ k
    let H : ℤ := if t = 1 then 0 else if b₁ < p ^ k then (p ^ k : ℕ) else -((p ^ k : ℕ) : ℤ)
    let c : ℕ → ℤ := fun j => ((b₁ ^ j % n : ℕ) : ℤ)
    ∃ u : ℤ, c 2 = b₁ - 1 + H ∧ c 3 = n - 1 ∧ c 4 = n - b₁ ∧ c 5 = n - b₁ + 1 - H ∧
      (b₁ : ℤ) ^ 2 = u * n + b₁ - 1 + H ∧ c 2 ^ 2 = u * n - b₁ + (H + 2 * b₁ - 1) * H ∧
      b₁ * c 2 = u * n - 1 + (b₁ + 1) * H

/-- In the setting of Lemma 35, with rows `b_1` and `b_5` and `D_i = r_{5,i} - r_{1,i}`
(`r_{x,i} = ⌊b_x^(i+1)/n⌋ mod b_x`): `D_0 = D_5 = 0`, `D_2 = n - b_1 - b_2 = 1 - 2b_1 + (1 - h)n`,
`D_1 = (1 - h) D_2`, `D_3 = D_2`, `D_4 = h D_2`; the relations with `h = hn/n` are multiplied
by `n`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 36 (`integers-2025-A26-lem-36`). -/
public theorem_wanted repetend_digit_diffs_of_orderOf_eq_six (p k t b₁ : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hk : 0 < k) (ht : t = 1 ∨ t = 2) (hb₁ : b₁ < t * p ^ k)
    (hb : orderOf (b₁ : ZMod (t * p ^ k)) = 6) :
    let n := t * p ^ k
    let H : ℤ := if t = 1 then 0 else if b₁ < p ^ k then (p ^ k : ℕ) else -((p ^ k : ℕ) : ℤ)
    let b₅ := b₁ ^ 5 % n
    let D : ℕ → ℤ := fun i => ((b₅ ^ (i + 1) / n % b₅ : ℕ) : ℤ) - (b₁ ^ (i + 1) / n % b₁ : ℕ)
    D 0 = 0 ∧ D 5 = 0 ∧ D 2 = n - b₁ - (b₁ ^ 2 % n : ℕ) ∧ D 2 = 1 - 2 * b₁ + n - H ∧
      n * D 1 = (n - H) * D 2 ∧ D 3 = D 2 ∧ n * D 4 = H * D 2

/-- For `n = t p^k` (`t ∈ {1, 2}`, `p ≡ 1 (mod 6)` prime, `k ≥ 1`) and `L = 6`, column `0` of the
repetend table of `1/n` does not match column `5`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 37 (`integers-2025-A26-lem-37`). -/
public theorem_wanted repetend_column_zero_ne_five (p k t : ℕ) (hp : p.Prime) (hp6 : p % 6 = 1)
    (hk : 0 < k) (ht : t = 1 ∨ t = 2) :
    let n := t * p ^ k
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6
    (B.val.map fun b => b ^ (0 + 1) / n % b) ≠ B.val.map fun b => b ^ (5 + 1) / n % b

/-- In the setting of Lemma 37, none of columns `1, 2, 3` matches column `0` or `5`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 38 (`integers-2025-A26-lem-38`). -/
public theorem_wanted repetend_columns_one_to_three_ne_zero_five (p k t : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hk : 0 < k) (ht : t = 1 ∨ t = 2) :
    let n := t * p ^ k
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6
    ∀ i ∈ ({1, 2, 3} : Finset ℕ), ∀ j ∈ ({0, 5} : Finset ℕ),
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- In the setting of Lemma 37, column `4` matches neither column `0` nor column `5`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 39 (`integers-2025-A26-lem-39`). -/
public theorem_wanted repetend_column_four_ne_zero_five (p k t : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hk : 0 < k) (ht : t = 1 ∨ t = 2) :
    let n := t * p ^ k
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6
    ∀ j ∈ ({0, 5} : Finset ℕ),
      (B.val.map fun b => b ^ (4 + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- In the setting of Lemma 37, no two distinct columns among `1, 2, 3, 4` match.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 40 (`integers-2025-A26-lem-40`). -/
public theorem_wanted repetend_columns_one_to_four_pairwise_ne (p k t : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1) (hk : 0 < k) (ht : t = 1 ∨ t = 2) :
    let n := t * p ^ k
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6
    ∀ i ∈ Finset.Icc 1 4, ∀ j ∈ Finset.Icc 1 4, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- If the repetend table of `1/n` for length `L` has `1 ≤ n_r ≤ 3` rows, no two distinct columns
match (for such `L` there are no Class A pairs, so this is "no sporadic matches").

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 12 (`integers-2025-A26-thm-12`). -/
public theorem_wanted repetend_columns_ne_of_card_le_three (n L : ℕ) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L
    1 ≤ B.card → B.card ≤ 3 → ∀ i < L, ∀ j < L, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b

/-- Tail bound: for `m ≥ 2` and `s > 0`, `∑_{n > s} n^(-m) < ((m - 1) s^(m-1))^(-1)`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 42 (`integers-2025-A26-lem-42`). -/
public theorem_wanted tsum_inv_pow_succ_lt (m s : ℕ) (hm : 2 ≤ m) (hs : 0 < s) :
    ∑' k : ℕ, (((k + s + 1 : ℕ) : ℝ) ^ m)⁻¹ < (((m - 1 : ℕ) : ℝ) * (s : ℝ) ^ (m - 1))⁻¹

end

end MetaMathlibExt
