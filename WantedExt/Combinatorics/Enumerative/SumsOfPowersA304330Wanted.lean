/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums of powers of integers and the sequence A304330

Statements from José L. Cereceda, "Sums of Powers of Integers and
the Sequence A304330", *Journal of Integer Sequences* 28 (2025),
Article 25.1.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Cereceda/cere9.html>).
Definitions are taken from the publisher TeX.

`S_k(n) = 1^k + ⋯ + n^k` is `powerSum`.  The array `R(k, m)`
(OEIS A304330 rows: `1; 1, 12; 1, 60, 360; …`) is defined by
`R(k, m) = Σ_{j=0}^m (-1)^j C(2m, j) (m - j)^{2k}`, and
`U(k, m) = (2/(2m)!)·R(k, m)`.  The inverse array `u(k, m)`, defined by
`Σ_{m=1}^k u(k, m) x^m = ∏_{i=0}^{k-1} (x - i^2)`, is the
existing specialization `MetaMathlibExt.jacobiStirlingFirst k m
(0 : ℤ)`, and the Legendre-Stirling numbers of the first kind
`Ps_m^{(r)}` (which the paper only names) are the existing
`MetaMathlibExt.legendreStirlingFirst`, i.e. the standard signed
convention `∏_{j=0}^{m-1} (x - j(j+1)) = Σ_r Ps_m^{(r)} x^r`,
which is the convention satisfying Proposition 12 (checked
numerically; the opposite sign fails).  The polynomial
identities below are stated for all `n : ℕ` where they hold at
`n = 0` as well; Lemmas 4 and 7 keep the paper's `n ≥ 1`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.Enumerative.LegendreStirlingFirstKind

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted

/-- `S_k(n) = 1^k + ⋯ + n^k`, as a rational number. -/
def powerSum (k n : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ k

/-- `R(k, m) = Σ_{j=0}^m (-1)^j C(2m, j) (m - j)^{2k}`. -/
def arrayR (k m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℤ) ^ j * (Nat.choose (2 * m) j : ℤ) * ((m : ℤ) - j) ^ (2 * k)

/-- `U(k, m) = (2/(2m)!) Σ_{j=0}^m (-1)^j C(2m, j) (m - j)^{2k}`. -/
def arrayU (k m : ℕ) : ℚ :=
  (2 / (Nat.factorial (2 * m) : ℚ)) *
    ∑ j ∈ Finset.range (m + 1),
      (-1 : ℚ) ^ j * (Nat.choose (2 * m) j : ℚ) * ((m : ℚ) - j) ^ (2 * k)

/-- The Faulhaber coefficient
`b_{k,r} = Σ_{m=r}^k (3·2^r/(2m+1)!)·R(k, m)·Ps_m^{(r)}` of
Proposition 12. -/
noncomputable def faulhaberB (k r : ℕ) : ℚ :=
  ∑ m ∈ Finset.Icc r k,
    (3 * 2 ^ r / (Nat.factorial (2 * m + 1) : ℚ)) *
      (arrayR k m : ℚ) * (MetaMathlibExt.legendreStirlingFirst m r : ℚ)

/-- The Faulhaber coefficient
`c_{k,r} = Σ_{m=r}^k (2^{r+1}/((2m+2)!(m+1)))·R(k+1, m+1)·Ps_{m+1}^{(r+1)}`
of Proposition 12. -/
noncomputable def faulhaberC (k r : ℕ) : ℚ :=
  ∑ m ∈ Finset.Icc r k,
    (2 ^ (r + 1) / ((Nat.factorial (2 * m + 2) : ℚ) * (m + 1))) *
      (arrayR (k + 1) (m + 1) : ℚ) * (MetaMathlibExt.legendreStirlingFirst (m + 1) (r + 1) : ℚ)

/-- The polynomial values `Q_{k,m}(n)` of Theorem 10:
`n^{2k-1}` for `m = 1`, and
`2·Σ_{j=m}^k C(2k-1, 2j-2)·R(j-1, m-1)·n^{2k-2j+1}` for
`m ≥ 2`, evaluated at `n`. -/
def thmQ (k m n : ℕ) : ℚ :=
  if m = 1 then (n : ℚ) ^ (2 * k - 1)
  else 2 * ∑ j ∈ Finset.Icc m k,
    (Nat.choose (2 * k - 1) (2 * j - 2) : ℚ) *
      (arrayR (j - 1) (m - 1) : ℚ) * (n : ℚ) ^ (2 * k - 2 * j + 1)

/-- **Theorem 1**: `2^{2k} S_{2k}(n) =
Σ_{m=1}^k R(k, m)·C(2n + m + 1, 2m + 1)` for `k ≥ 1`.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Theorem 1. -/
theorem_wanted pow_mul_powerSum_even_eq_sum (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) :
    (2 : ℚ) ^ (2 * k) * powerSum (2 * k) n =
      ∑ m ∈ Finset.Icc 1 k,
        (arrayR k m : ℚ) *
          (Nat.choose (2 * n + m + 1) (2 * m + 1) : ℚ)

/-- **Proposition 2 (Knuth, 1993)**: for real coefficients
`a_m`, the identity
`S_{2k}(n)/(2n + 1) = Σ_{m=1}^k a_m·C(n + m, 2m)` (for all `n`)
holds if and only if
`S_{2k-1}(n) = Σ_{m=1}^k ((2m + 1)/m)·a_m·C(n + m, 2m)`
(for all `n`).

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 2. -/
theorem_wanted powerSum_even_div_iff_odd (k : ℕ) (hk : 1 ≤ k)
    (a : ℕ → ℝ) :
    (∀ n : ℕ, (powerSum (2 * k) n : ℝ) / (2 * (n : ℝ) + 1) =
      ∑ m ∈ Finset.Icc 1 k,
        a m * (Nat.choose (n + m) (2 * m) : ℝ)) ↔
    (∀ n : ℕ, (powerSum (2 * k - 1) n : ℝ) =
      ∑ m ∈ Finset.Icc 1 k,
        ((2 * (m : ℝ) + 1) / (m : ℝ)) * a m *
          (Nat.choose (n + m) (2 * m) : ℝ))

/-- **Proposition 3 (Knuth, 1993), even case**:
`S_{2k}(n) = Σ_{m=1}^k R(k, m)·((2n + 1)/(2m + 1))·C(n + m, 2m)`
for `k ≥ 1`.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 3. -/
theorem_wanted powerSum_even_eq_sum (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    powerSum (2 * k) n =
      ∑ m ∈ Finset.Icc 1 k,
        (arrayR k m : ℚ) * ((2 * (n : ℚ) + 1) / (2 * (m : ℚ) + 1)) *
          (Nat.choose (n + m) (2 * m) : ℚ)

/-- **Proposition 3 (Knuth, 1993), odd case**:
`S_{2k-1}(n) = Σ_{m=1}^k R(k, m)·(1/m)·C(n + m, 2m)` for `k ≥ 1`.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 3. -/
theorem_wanted powerSum_odd_eq_sum (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    powerSum (2 * k - 1) n =
      ∑ m ∈ Finset.Icc 1 k,
        (arrayR k m : ℚ) * (1 / (m : ℚ)) *
          (Nat.choose (n + m) (2 * m) : ℚ)

/-- **Lemma 4**: `Σ_{i=1}^n (2i)·C(2i + k - 1, 2k - 1) =
k·C(2n + k + 1, 2k + 1)` for `n ≥ 1` and fixed positive `k`.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Lemma 4. -/
theorem_wanted sum_two_mul_choose_eq (k n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n,
      (2 * i) * Nat.choose (2 * i + k - 1) (2 * k - 1)) =
      k * Nat.choose (2 * n + k + 1) (2 * k + 1)

/-- **Lemma 5 (Butzer et al., Proposition 2.3)**: the inversion
formula `a_k = Σ_{m=1}^k u(k, m)·b_m ⟺
b_k = Σ_{m=1}^k U(k, m)·a_m` for real sequences.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Lemma 5. -/
theorem_wanted inversion_uU (a b : ℕ → ℝ) :
    (∀ k : ℕ, 1 ≤ k → a k =
      ∑ m ∈ Finset.Icc 1 k, (MetaMathlibExt.jacobiStirlingFirst k m (0 : ℤ) : ℝ) * b m) ↔
    (∀ k : ℕ, 1 ≤ k → b k =
      ∑ m ∈ Finset.Icc 1 k, (arrayU k m : ℝ) * a m)

/-- **Corollary 6**: for `1 ≤ m ≤ k`,
`R(k, m) = 2^{2k+m-1}·m!·Σ (2k)!/(b_1!⋯b_k!)·∏_{r=1}^k
(1/(4^r (2r)!))^{b_r}`, summed over the `k`-tuples
`b : Fin k → ℕ` with `Σ (r+1)·b_r = k` and `Σ b_r = m`
(the entry bounds `b_r ≤ k` are automatic from the weighted
sum).

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Corollary 6. -/
theorem_wanted arrayR_eq_closedForm (k m : ℕ) (hm1 : 1 ≤ m)
    (hmk : m ≤ k) :
    (arrayR k m : ℚ) =
      (2 : ℚ) ^ (2 * k + m - 1) * (Nat.factorial m : ℚ) *
        ∑ b ∈ Finset.univ.filter
            (fun b : Fin k → Fin (k + 1) =>
              (∑ r : Fin k, (r.val + 1) * (b r).val) = k ∧
              (∑ r : Fin k, (b r).val) = m),
          ((Nat.factorial (2 * k) : ℚ) /
            ∏ r : Fin k, (Nat.factorial (b r).val : ℚ)) *
            ∏ r : Fin k,
              (1 / ((4 : ℚ) ^ (r.val + 1) *
                (Nat.factorial (2 * (r.val + 1)) : ℚ))) ^ ((b r).val)

/-- **Lemma 7**: `Σ_{i=1}^n i·C(i + k - 1, 2k - 1) =
(k(2n + 1)/(2k + 1))·C(n + k, 2k)` for `n ≥ 1` and fixed
positive `k`.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Lemma 7. -/
theorem_wanted sum_mul_choose_eq (k n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n,
      (i : ℚ) * (Nat.choose (i + k - 1) (2 * k - 1) : ℚ)) =
      ((k : ℚ) * (2 * (n : ℚ) + 1) / (2 * (k : ℚ) + 1)) *
        (Nat.choose (n + k) (2 * k) : ℚ)

/-- **Theorem 10**: `2^{2k-1} S_{2k-1}(n) =
Σ_{m=1}^k Q_{k,m}(n)·C(n + m, 2m - 1)` for `k ≥ 1`, with
`Q_{k,m}` as in `thmQ`.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Theorem 10. -/
theorem_wanted pow_mul_powerSum_odd_eq_sum (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) :
    (2 : ℚ) ^ (2 * k - 1) * powerSum (2 * k - 1) n =
      ∑ m ∈ Finset.Icc 1 k,
        thmQ k m n * (Nat.choose (n + m) (2 * m - 1) : ℚ)

/-- **Proposition 12, even case**: the Faulhaber form
`S_{2k}(n) = S_2(n)·Σ_{r=1}^k b_{k,r}·S_1(n)^{r-1}` with
`b_{k,r}` as in `faulhaberB`, for `k ≥ 1`.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 12. -/
theorem_wanted powerSum_even_faulhaber (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) :
    powerSum (2 * k) n =
      powerSum 2 n * ∑ r ∈ Finset.Icc 1 k,
        faulhaberB k r * (powerSum 1 n) ^ (r - 1)

/-- **Proposition 12, odd case**: the Faulhaber form
`S_{2k+1}(n) = S_1(n)^2·Σ_{r=1}^k c_{k,r}·S_1(n)^{r-1}` with
`c_{k,r}` as in `faulhaberC`, for `k ≥ 1`.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 12. -/
theorem_wanted powerSum_odd_faulhaber (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) :
    powerSum (2 * k + 1) n =
      (powerSum 1 n) ^ 2 * ∑ r ∈ Finset.Icc 1 k,
        faulhaberC k r * (powerSum 1 n) ^ (r - 1)

/-- **Proposition 15**:
`Σ_{m=1}^k (-1)^m·((m-1)!)^2/(2m)!·R(k, m) = 0` for `k ≥ 2`.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 15. -/
theorem_wanted sum_neg_factorial_sq_div_arrayR_eq_zero (k : ℕ)
    (hk : 2 ≤ k) :
    (∑ m ∈ Finset.Icc 1 k,
      (-1 : ℚ) ^ m *
        ((Nat.factorial (m - 1) : ℚ) ^ 2 /
          (Nat.factorial (2 * m) : ℚ)) * (arrayR k m : ℚ)) = 0

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
