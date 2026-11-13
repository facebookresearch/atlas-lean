/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Farey fractions with equal numerators

Statements from Rogelio Tomás García, "Farey
Fractions with Equal Numerators and the Rank of Unit
Fractions", *INTEGERS* 24 (2024), Article A63
(<https://math.colgate.edu/~integers/vol24.html>).

`fareyNumeratorCount n h` is the paper's `N_n(h)`:
the number of fractions of the Farey sequence `F_n`
with numerator `h`, i.e. denominators `h ≤ b ≤ n`
coprime to `h`. Lemma 1's endpoint conventions and
Theorem 1's formula were pinned by brute force over
small parameters (the count in `(1/k, 1/(k-1)]`
requires the strict lower endpoint as soon as
`n > k*h - 1`).

`fareyNumeratorCountBelow n h x` is the paper's
`N_n^x(h)` (numerator `h`, value below `x`) and
`fareyRank n x` is `I_n(x)`, the number of fractions
of `F_n` (with `0/1` excluded) strictly below `x`.
`Φ(m) = ∑_{j ≤ m} φ(j)` is written out as a sum.
Theorem 2 and Corollaries 1-8 were checked against
the journal PDF and by exact brute force for `n < 26`.
Corollary 7 is false as printed for `k = 1` or
`h ≤ 2` and is stated with the hypotheses `1 < k`,
`2 < h` of Lemma 1, which its proof invokes.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.Farey

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FareyNumeratorWanted

/-- The number of Farey fractions of order `n` with
numerator `h`: denominators `b` with `h ≤ b ≤ n` and
`Nat.Coprime h b`. -/
def fareyNumeratorCount (n h : ℕ) : ℕ :=
  ((Finset.Icc h n).filter (fun b => Nat.Coprime h b)).card

/-- **Lemma 1**: for positive integers `k > 1`, `n`
and `h`, the number of Farey fractions between `1/k`
and `1/(k-1)` in `F_n` with numerator `h` is `φ(h)`
when `n ≥ k*h - 1`; the number between `1/k` and
`2/(2k-1)` with numerator `h` is `φ(h)/2` for
`h > 2` (stated as `2 * count = φ(h)`).

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
Lemma 1. -/
theorem_wanted farey_between_count (k n h : ℕ)
    (hk : 1 < k) (hh : 1 ≤ h) (hn : k * h - 1 ≤ n) :
    ((Finset.Icc 1 n).filter (fun b => Nat.Coprime h b ∧
        (1 : ℚ) / k < (h : ℚ) / b ∧
          (h : ℚ) / b ≤ 1 / ((k : ℚ) - 1))).card =
        Nat.totient h ∧
      (2 < h →
        2 * ((Finset.Icc 1 n).filter (fun b =>
            Nat.Coprime h b ∧ (1 : ℚ) / k < (h : ℚ) / b ∧
              (h : ℚ) / b < 2 / (2 * (k : ℚ) - 1))).card =
          Nat.totient h)

/-- **Theorem 1**: for `0 < h < n`,
`N_n(h) = φ(h) * (n / h) - ∑_{d ∣ h} μ(d) {n / d}
  - φ(h) + δ_{1h}`, where `μ` is the Möbius function,
`{x}` is the fractional part (written `(n % d) / d`)
and `δ_{1h}` is `1` if
`h = 1` and `0` otherwise.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
Theorem 1. -/
theorem_wanted fareyNumeratorCount_formula (h n : ℕ)
    (hh : 0 < h) (hhn : h < n) :
    (fareyNumeratorCount n h : ℚ) =
      (Nat.totient h : ℚ) * (n : ℚ) / h -
        ∑ d ∈ h.divisors,
          (ArithmeticFunction.moebius d : ℚ) *
            ((n % d : ℚ) / d) -
        (Nat.totient h : ℚ) + (if h = 1 then 1 else 0)

/-- The number of Farey fractions of order `n` with
numerator `h` and value strictly below `x`: the
paper's `N_n^x(h)`, i.e. denominators `h ≤ b ≤ n`
coprime to `h` with `h / b < x`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Section 1. -/
def fareyNumeratorCountBelow (n h : ℕ) (x : ℚ) : ℕ :=
  ((Finset.Icc h n).filter (fun b =>
    Nat.Coprime h b ∧ (h : ℚ) / b < x)).card

/-- In `F_5` the fractions with numerator `1` below
`1/2` are `1/5, 1/4, 1/3`, so `N_5^{1/2}(1) = 3`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Section 1. -/
theorem fareyNumeratorCountBelow_five_one_half :
    fareyNumeratorCountBelow 5 1 (1 / 2) = 3 := by
  decide +kernel

/-- Restricting to values below `x` can only lower
the count: `N_n^x(h) ≤ N_n(h)`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Section 1. -/
theorem fareyNumeratorCountBelow_le (n h : ℕ) (x : ℚ) :
    fareyNumeratorCountBelow n h x ≤
      fareyNumeratorCount n h := by
  unfold fareyNumeratorCountBelow fareyNumeratorCount
  exact Finset.card_le_card (fun b hb => by
    simp only [Finset.mem_filter] at hb ⊢
    exact ⟨hb.1, hb.2.1⟩)

/-- The paper's `I_n(x) = |F_n^x|`: the number of
fractions of the Farey sequence `F_n`, with `0/1`
excluded, strictly below `x`. For `x = 1/k` this is
the rank of `1/k` in `F_n`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Sections 1 and 2.1. -/
def fareyRank (n : ℕ) (x : ℚ) : ℕ :=
  ((Farey.fareyFinset n).filter (fun q => 0 < q ∧ q < x)).card

/-- `F_5` has `1/5, 1/4, 1/3, 2/5` below `1/2`, so
`I_5(1/2) = 4`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Section 1 (the
listing of `F_5`). -/
theorem fareyRank_five_half : fareyRank 5 (1 / 2) = 4 := by
  decide +kernel

/-- **Corollary 1**: for a prime `p` and positive `m`
with `p ^ m ≤ n`,
`N_n(p^m) = ⌈(n - p^m)(1 - 1/p)⌉`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Corollary 1. -/
theorem_wanted fareyNumeratorCount_prime_pow (p m n : ℕ)
    (hp : p.Prime) (hm : 0 < m) (hpn : p ^ m ≤ n) :
    (fareyNumeratorCount n (p ^ m) : ℤ) =
      ⌈((n : ℚ) - (p : ℚ) ^ m) * (1 - 1 / (p : ℚ))⌉

/-- **Corollary 2**: for `0 < h < n` and `m ≥ 0`,
`N_{n + m h}(h) = N_n(h) + m φ(h)`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Corollary 2. -/
theorem_wanted fareyNumeratorCount_add_mul (h n m : ℕ)
    (hh : 0 < h) (hhn : h < n) :
    fareyNumeratorCount (n + m * h) h =
      fareyNumeratorCount n h + m * Nat.totient h

/-- **Corollary 3**: for `0 < h < n/2`,
`N_n(2h) = N_n(h) - φ(h)` if `h` is even, and
`N_n(2h) = (N_n(h) - φ(h) - δ_{1h}
  + ∑_{d ∣ h} μ(d) w(n/d)) / 2` if `h` is odd, where
`w(x) = ⌊x⌋ mod 2` (written `(n / d) % 2`; the halved
case is stated for `2 * N_n(2h)`).

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Corollary 3. -/
theorem_wanted fareyNumeratorCount_two_mul (h n : ℕ)
    (hh : 0 < h) (hhn : 2 * h < n) :
    (Even h → (fareyNumeratorCount n (2 * h) : ℤ) =
        fareyNumeratorCount n h - Nat.totient h) ∧
      (Odd h → 2 * (fareyNumeratorCount n (2 * h) : ℤ) =
        fareyNumeratorCount n h - Nat.totient h -
          (if h = 1 then 1 else 0) +
          ∑ d ∈ h.divisors,
            ArithmeticFunction.moebius d * (((n / d) % 2 : ℕ) : ℤ))

/-- **Corollary 4**: for `0 < m < n`, the number of
fractions of `F_n` with numerator at most `m` is
`1 + n ∑_{h ≤ m} φ(h)/h - Φ(m)
  - ∑_{h ≤ m} ∑_{d ∣ h} μ(d) {n/d}`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Corollary 4. -/
theorem_wanted sum_fareyNumeratorCount (m n : ℕ)
    (hm : 0 < m) (hmn : m < n) :
    (∑ h ∈ Finset.Icc 1 m, (fareyNumeratorCount n h : ℚ)) =
      1 + (n : ℚ) * ∑ h ∈ Finset.Icc 1 m, (Nat.totient h : ℚ) / h -
        ∑ h ∈ Finset.Icc 1 m, (Nat.totient h : ℚ) -
        ∑ h ∈ Finset.Icc 1 m, ∑ d ∈ h.divisors,
          (ArithmeticFunction.moebius d : ℚ) * (((n % d : ℕ) : ℚ) / d)

/-- **Corollary 5**: for `0 < h < n` and
`0 < k < n/h` (written `k * h < n`),
`N_n^{1/k}(h) = n φ(h)/h - k φ(h) - ∑_{d ∣ h} μ(d) {n/d}`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Corollary 5. -/
theorem_wanted fareyNumeratorCountBelow_inv_formula (h n k : ℕ)
    (hh : 0 < h) (hhn : h < n) (hk : 0 < k) (hkn : k * h < n) :
    (fareyNumeratorCountBelow n h (1 / (k : ℚ)) : ℚ) =
      (n : ℚ) * Nat.totient h / h - (k : ℚ) * Nat.totient h -
        ∑ d ∈ h.divisors,
          (ArithmeticFunction.moebius d : ℚ) * (((n % d : ℕ) : ℚ) / d)

/-- **Theorem 2**: for `0 < k ≤ n`, with `q = ⌊n/k⌋`,
`I_n(1/k) = n ∑_{j ≤ q} φ(j)/j - k Φ(q)
  - ∑_{j ≤ q} ∑_{d ∣ j} μ(d) {n/d}`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Theorem 2. -/
theorem_wanted fareyRank_inv_formula (k n : ℕ)
    (hk : 0 < k) (hkn : k ≤ n) :
    (fareyRank n (1 / (k : ℚ)) : ℚ) =
      (n : ℚ) * ∑ j ∈ Finset.Icc 1 (n / k), (Nat.totient j : ℚ) / j -
        (k : ℚ) * ∑ j ∈ Finset.Icc 1 (n / k), (Nat.totient j : ℚ) -
        ∑ j ∈ Finset.Icc 1 (n / k), ∑ d ∈ j.divisors,
          (ArithmeticFunction.moebius d : ℚ) * (((n % d : ℕ) : ℚ) / d)

/-- **Corollary 6**: for positive `c`, `k`, `p`, with
`L = lcm(1, …, c)`, `k' = k + p L` and
`A(c) = c ∑_{j ≤ c} φ(j)/j - Φ(c)`:
`I_{ck'}(1/k') = I_{ck}(1/k) + (k' - k) A(c)`,
`I_{ck'}(1/k') - I_{ck}(1/k) = I_{c(k'-k)}(1/(k'-k))`, and
`I_{c(k'-k)}(1/(k'-k)) / (k' - k) = A(c)`
(`k' - k` written `p * L`).

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Corollary 6. -/
theorem_wanted fareyRank_inv_add_lcm (c k p : ℕ)
    (hc : 0 < c) (hk : 0 < k) (hp : 0 < p) :
    let L := (Finset.Icc 1 c).lcm id
    let A : ℚ := (c : ℚ) * ∑ j ∈ Finset.Icc 1 c, (Nat.totient j : ℚ) / j -
      ∑ j ∈ Finset.Icc 1 c, (Nat.totient j : ℚ)
    (fareyRank (c * (k + p * L)) (1 / ((k + p * L : ℕ) : ℚ)) : ℚ) =
        fareyRank (c * k) (1 / (k : ℚ)) + ((p * L : ℕ) : ℚ) * A ∧
      (fareyRank (c * (k + p * L)) (1 / ((k + p * L : ℕ) : ℚ)) : ℚ) -
          fareyRank (c * k) (1 / (k : ℚ)) =
        fareyRank (c * (p * L)) (1 / ((p * L : ℕ) : ℚ)) ∧
      (fareyRank (c * (p * L)) (1 / ((p * L : ℕ) : ℚ)) : ℚ) /
          ((p * L : ℕ) : ℚ) = A

/-- **Corollary 7** (corrected reading): for odd
`k > 1`, `h > 2` and `k < 2n/h - 1` (written
`(k + 1) * h < 2 * n`),
`N_n^{2/k}(h) = n φ(h)/h - (k/2) φ(h) - ∑_{d ∣ h} μ(d) {n/d}`.
As printed (only `h < n`) the formula fails for `k = 1`
or `h ≤ 2`, e.g. `n = 3`, `h = 1`, `k = 3`:
`N_3^{2/3}(1) = 2 ≠ 3/2`; the proof applies Lemma 1,
which needs `k' > 1` and `h > 2`. The printed `h < n`
follows from the other hypotheses.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Corollary 7. -/
theorem_wanted fareyNumeratorCountBelow_two_div_formula (h n k : ℕ)
    (hh : 2 < h) (hk : Odd k) (hk1 : 1 < k)
    (hkn : (k + 1) * h < 2 * n) :
    (fareyNumeratorCountBelow n h (2 / (k : ℚ)) : ℚ) =
      (n : ℚ) * Nat.totient h / h - (k : ℚ) / 2 * Nat.totient h -
        ∑ d ∈ h.divisors,
          (ArithmeticFunction.moebius d : ℚ) * (((n % d : ℕ) : ℚ) / d)

/-- **Corollary 8**, first part: for odd `k` with
`n ≥ k > 2`, with `q = ⌊2n/k⌋`,
`I_n(2/k) = n ∑_{j ≤ q} φ(j)/j - (k/2) Φ(q)
  - ∑_{j ≤ q} ∑_{d ∣ j} μ(d) {n/d}`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Corollary 8. -/
theorem_wanted fareyRank_two_div_formula (k n : ℕ)
    (hk : Odd k) (hk2 : 2 < k) (hkn : k ≤ n) :
    (fareyRank n (2 / (k : ℚ)) : ℚ) =
      (n : ℚ) * ∑ j ∈ Finset.Icc 1 (2 * n / k), (Nat.totient j : ℚ) / j -
        (k : ℚ) / 2 * ∑ j ∈ Finset.Icc 1 (2 * n / k), (Nat.totient j : ℚ) -
        ∑ j ∈ Finset.Icc 1 (2 * n / k), ∑ d ∈ j.divisors,
          (ArithmeticFunction.moebius d : ℚ) * (((n % d : ℕ) : ℚ) / d)

/-- **Corollary 8**, second part: for odd `k > 2`,
positive even `c` and positive `p`, with
`L = lcm(1, …, c)`, `k' = k + p L`, `n = ck/2` and
`n' = ck'/2`,
`I_{n'}(2/k') = I_n(2/k) + ((k' - k)/2) A(c)`, where
`A(c) = c ∑_{j ≤ c} φ(j)/j - Φ(c)` (`k' - k` written
`p * L`).

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Corollary 8. -/
theorem_wanted fareyRank_two_div_add_lcm (c k p : ℕ)
    (hk : Odd k) (hk2 : 2 < k) (hc : Even c) (hc0 : 0 < c)
    (hp : 0 < p) :
    let L := (Finset.Icc 1 c).lcm id
    (fareyRank (c * (k + p * L) / 2) (2 / ((k + p * L : ℕ) : ℚ)) : ℚ) =
      fareyRank (c * k / 2) (2 / (k : ℚ)) +
        ((p * L : ℕ) : ℚ) / 2 *
          ((c : ℚ) * ∑ j ∈ Finset.Icc 1 c, (Nat.totient j : ℚ) / j -
            ∑ j ∈ Finset.Icc 1 c, (Nat.totient j : ℚ))

end MathlibExt.NumberTheory.FareyNumeratorWanted
