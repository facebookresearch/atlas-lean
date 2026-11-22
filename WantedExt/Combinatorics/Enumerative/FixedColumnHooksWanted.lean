/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.GaussianBinomial

namespace MetaMathlibExt

@[expose] public section

open PowerSeries MathlibExt

/-- The column length `λ'_j` of a partition: the number of parts `≥ j` (columns are
1-indexed).

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Section 1 (`λ'`, the conjugate partition). -/
def partitionColLen {n : ℕ} (p : n.Partition) (j : ℕ) : ℕ :=
  (p.parts.filter (j ≤ ·)).card

/-- The row length `λ_s` of a partition: its `s`-th largest part (rows are 1-indexed, and the
value is `0` past the last row), computed as the number of columns `j ∈ [1, n]` of length at
least `s`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Section 1 (`λ = (λ₁, λ₂, …)` weakly decreasing). -/
def partitionRowLen {n : ℕ} (p : n.Partition) (s : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun j => s ≤ partitionColLen p j)).card

/-- The hook length `h_{s,m}(λ) = λ_s + λ'_m - s - m + 1` of the square in row `s` and
column `m` (1-indexed), as an integer.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Section 1. -/
def partitionHookLength {n : ℕ} (p : n.Partition) (s m : ℕ) : ℤ :=
  (partitionRowLen p s : ℤ) + partitionColLen p m - s - m + 1

/-- The partition `p` has an `h`-fixed hook in column `m` at row `s`: the square `(s, m)` lies
in the Young diagram (`1 ≤ s`, `1 ≤ m ≤ λ_s`) and the `s`-th term of the sequence of
`m`th-column hook lengths is an `h`-fixed point, `h_{s,m}(λ) = s + h`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Section 1 (an `h`-fixed point of the sequence
`h_{1,m}(λ), h_{2,m}(λ), …`; Figure 2: `h_{m,s} = s + h` at part `λ_s`). -/
def IsFixedColumnHook {n : ℕ} (p : n.Partition) (m s : ℕ) (h : ℤ) : Prop :=
  1 ≤ s ∧ 1 ≤ m ∧ m ≤ partitionRowLen p s ∧ partitionHookLength p s m = s + h

instance {n : ℕ} (p : n.Partition) (m s : ℕ) (h : ℤ) :
    Decidable (IsFixedColumnHook p m s h) := by
  unfold IsFixedColumnHook; infer_instance

/-- The partition `(4, 4, 3, 1)` of `12` from Figure 1.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Figure 1. -/
def partition4431 : Nat.Partition 12 := ⟨{4, 4, 3, 1}, by decide, by decide⟩

/-- Rows and columns of `(4, 4, 3, 1)`: `λ = (4, 4, 3, 1)` and `λ' = (4, 3, 3, 2)`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Figure 1. -/
theorem partition4431_row_col :
    (partitionRowLen partition4431 1, partitionRowLen partition4431 2,
      partitionRowLen partition4431 3, partitionRowLen partition4431 4,
      partitionRowLen partition4431 5) = (4, 4, 3, 1, 0) ∧
    (partitionColLen partition4431 1, partitionColLen partition4431 2,
      partitionColLen partition4431 3, partitionColLen partition4431 4,
      partitionColLen partition4431 5) = (4, 3, 3, 2, 0) := by
  decide

/-- Hook lengths of `(4, 4, 3, 1)` as labeled in Figure 1: first row `7, 5, 4, 2`, first column
`7, 6, 4, 1`, and the diagonal `7, 4, 1`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Figure 1. -/
theorem partition4431_hookLength :
    partitionHookLength partition4431 1 1 = 7 ∧ partitionHookLength partition4431 1 2 = 5 ∧
      partitionHookLength partition4431 1 3 = 4 ∧ partitionHookLength partition4431 1 4 = 2 ∧
      partitionHookLength partition4431 2 1 = 6 ∧ partitionHookLength partition4431 3 1 = 4 ∧
      partitionHookLength partition4431 4 1 = 1 ∧ partitionHookLength partition4431 2 2 = 4 ∧
      partitionHookLength partition4431 3 3 = 1 := by
  decide

/-- In `(4, 4, 3, 1)`, the first-column hook `h_{3,1} = 4 = 3 + 1` is a `1`-fixed hook, the
first-column hook `h_{4,1} = 1` is not `0`-fixed, and the third-column square `(4, 3)` lies
outside the diagram.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Figure 1. -/
theorem partition4431_isFixedColumnHook :
    IsFixedColumnHook partition4431 1 3 1 ∧ ¬ IsFixedColumnHook partition4431 1 4 0 ∧
      ¬ IsFixedColumnHook partition4431 3 4 (-3) := by
  decide

/-- The number of partitions of `n` having a `0`-fixed hook in the `m`th column equals the sum
over `L` of the number of times, across all partitions of `n` with two colors of parts
`1, …, m - 1`, that a part of size `L` appears exactly `L + m - 1` times in the first color while
`L + 1, …, L + 2m - 2` are not parts in the first color.

A two-colored partition of `n` is a pair `(μ, ν)` of a first-color partition `μ` of `a` and a
second-color partition `ν` of `n - a` with parts `≤ m - 1`; the right side counts triples
`(μ, ν, L)`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 1 (`integers-2025-A28-thm-1`). -/
public theorem_wanted card_zeroFixedColumnHook_eq_twoColor_count (n m : ℕ) (hm : 1 ≤ m) :
    ((Finset.univ : Finset n.Partition).filter
        (fun p =>
          ((Finset.Icc 1 n).filter (fun s => IsFixedColumnHook p m s 0)).Nonempty)).card =
      ∑ a ∈ Finset.range (n + 1), ∑ μ : a.Partition,
        ∑ ν ∈ (Finset.univ : Finset (n - a).Partition).filter (fun ν => ∀ x ∈ ν.parts, x ≤ m - 1),
          (μ.parts.toFinset.filter (fun L => μ.parts.count L = L + m - 1 ∧
            Disjoint (Finset.Icc (L + 1) (L + 2 * m - 2)) μ.parts.toFinset)).card

/-- The number of partitions of `n` with an `h`-fixed hook in the `m`th column arising from a
part of size `m` equals the number of partitions of `n - mh` in which `m` appears as a part
exactly once, there are no parts of sizes `m + 1, …, 2m - 1`, and at least `-h` parts have size
at least `2m`.

`h` ranges over `ℤ`; when `n - mh < 0` the right side is `0`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 2 (`integers-2025-A28-thm-2`). -/
public theorem_wanted card_fixedColumnHook_part_eq_column (n m : ℕ) (h : ℤ) (hm : 1 ≤ m) :
    ((((Finset.univ : Finset n.Partition).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s =>
          IsFixedColumnHook p m s h ∧ partitionRowLen p s = m)).Nonempty)).card : ℕ) : ℤ) =
      if 0 ≤ (n : ℤ) - m * h then
        (((Finset.univ : Finset ((n : ℤ) - m * h).toNat.Partition).filter (fun p =>
          p.parts.count m = 1 ∧ Disjoint (Finset.Icc (m + 1) (2 * m - 1)) p.parts.toFinset ∧
            -h ≤ ((p.parts.filter (2 * m ≤ ·)).card : ℤ))).card : ℤ)
      else 0

/-- The generating function for the number of `m`th-column hooks of size `k` in all partitions
of `n` is
`q^{km}/(q^k; q)_∞ · Σ_{l=1}^{k} q^{-(l-1)(m-1)} (q^m; q)_{l-1}/((q; q)_{l-1} (q; q)_{k-l})
 = q^{m+k-1}/(q^k; q)_∞ · Σ_{l=1}^{k} q^{(m-1)(k-l)} (q^m; q)_{l-1}/((q; q)_{l-1} (q; q)_{k-l})`.

Stated coefficientwise in `ℚ⟦X⟧`: the coefficient of `qⁿ` counts the squares `(s, m)` of
Young diagrams of partitions of `n` with hook length `k`. For that coefficient `(q^k; q)_∞` is
replaced by its first `n + 1` factors, which changes no coefficient below `q^{n+1}`; the
exponent `km - (l-1)(m-1)` is nonnegative. `(q; q)_j` is `qPochFin X j` and
`[a, b]_q` is `gaussBinom X a b`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 4 (`integers-2025-A28-thm-4`). -/
public theorem_wanted columnHook_size_genFun (n m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    let P : ℚ⟦X⟧ := (∏ i ∈ Finset.range (n + 1), (1 - X ^ (k + i)))⁻¹
    let mPoch : ℕ → ℚ⟦X⟧ := fun j => ∏ i ∈ Finset.range j, (1 - X ^ (m + i))
    ((∑ p : n.Partition, ((Finset.Icc 1 n).filter (fun s =>
        m ≤ partitionRowLen p s ∧ partitionHookLength p s m = k)).card : ℕ) : ℚ) =
      coeff n (P * ∑ l ∈ Finset.Icc 1 k, X ^ (k * m - (l - 1) * (m - 1)) * mPoch (l - 1) *
        (qPochFin X (l - 1) * qPochFin X (k - l))⁻¹) ∧
    ((∑ p : n.Partition, ((Finset.Icc 1 n).filter (fun s =>
        m ≤ partitionRowLen p s ∧ partitionHookLength p s m = k)).card : ℕ) : ℚ) =
      coeff n (X ^ (m + k - 1) * P * ∑ l ∈ Finset.Icc 1 k, X ^ ((m - 1) * (k - l)) *
        mPoch (l - 1) * (qPochFin X (l - 1) * qPochFin X (k - l))⁻¹)

/-- For fixed `m ≥ 2`,
`lim_{k → ∞} q^{m-1}/(q^k; q)_∞ ·
 Σ_{l=1}^{k} q^{(m-1)(k-l)} (q^m; q)_{l-1}/((q; q)_{l-1} (q; q)_{k-l})
 = q^{m-1}/((1 - q^{m-1}) (q; q)_∞)`.

The limit is the coefficientwise (`q`-adic) limit in `ℚ⟦X⟧`: for each `n`, the coefficients of
`qⁿ` agree for all large `k`. For the coefficient of `qⁿ`, `(q^k; q)_∞` and `(q; q)_∞` are
replaced by their first `n + 1` factors, which changes no coefficient below `q^{n+1}`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 5 (`integers-2025-A28-thm-5`). -/
public theorem_wanted columnHook_size_genFun_limit (m : ℕ) (hm : 2 ≤ m) (n : ℕ) :
    ∀ᶠ k in Filter.atTop,
      coeff n (X ^ (m - 1) * (∏ i ∈ Finset.range (n + 1), (1 - X ^ (k + i)))⁻¹ *
        ∑ l ∈ Finset.Icc 1 k, X ^ ((m - 1) * (k - l)) *
          (∏ i ∈ Finset.range (l - 1), (1 - X ^ (m + i))) *
          (qPochFin (X : ℚ⟦X⟧) (l - 1) * qPochFin X (k - l))⁻¹) =
      coeff n (X ^ (m - 1) * ((1 - X ^ (m - 1)) * qPochFin (X : ℚ⟦X⟧) (n + 1))⁻¹)

/-- The generating function for the number of partitions of `n` with an `h`-fixed hook in the
first column arising from a part of size `k` is
`Σ_{s ≥ k-h} q^{(k+1)(s-1)+h+1}/(q; q)_{s-1} [s+h-1, k-1]_q
 = Σ_{s ≥ 0} q^{s(k+1)+k(k-h)}/(q; q)_{s+k-h-1} [s+k-1, k-1]_q`.

The two sums agree term by term under `s ↦ s + k - h`; the second is stated, coefficientwise:
the `s`-th term has no monomial below `q^s`, so the coefficient of `qⁿ` is that of the partial
sum over `s ≤ n`. `h ∈ ℤ` with `h < k` (so the lower limit `k - h` of the first sum is a
positive row index).

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 6 (`integers-2025-A28-thm-6`). -/
public theorem_wanted fixedFirstColumnHook_part_genFun (n k : ℕ) (h : ℤ) (hk : 1 ≤ k)
    (hh : h < k) :
    (((Finset.univ : Finset n.Partition).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s =>
          IsFixedColumnHook p 1 s h ∧ partitionRowLen p s = k)).Nonempty)).card : ℚ) =
      coeff n (∑ s ∈ Finset.range (n + 1),
        X ^ ((s : ℤ) * (k + 1) + k * (k - h)).toNat *
          (qPochFin (X : ℚ⟦X⟧) ((s : ℤ) + k - h - 1).toNat)⁻¹ * gaussBinom X (s + k - 1) (k - 1))

/-- The generating function for the number of partitions of `n` with an `h`-fixed hook in the
`m`th column arising from a part of size `k ≥ m` is
`Σ_{s ≥ k-h-m+1} q^{s(k+m)+m(h-k+m-1)}/((q; q)_{s-1} (q; q)_{m-1}) [s+h-1, k-m]_q
 = Σ_{s ≥ 0} q^{s(k+m)+k(k-h-m+1)}/((q; q)_{s+k-h-m} (q; q)_{m-1}) [s+k-m, k-m]_q`.

The two sums agree term by term under `s ↦ s + k - h - m`; the second is stated,
coefficientwise (the `s`-th term has no monomial below `q^s`). `h ∈ ℤ` with `h ≤ k - m`, so the
lower limit `k - h - m + 1` of the first sum is a positive row index.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 7 (`integers-2025-A28-thm-7`). -/
public theorem_wanted fixedColumnHook_part_genFun (n m k : ℕ) (h : ℤ) (hm : 1 ≤ m)
    (hmk : m ≤ k) (hh : h + m ≤ k) :
    (((Finset.univ : Finset n.Partition).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s =>
          IsFixedColumnHook p m s h ∧ partitionRowLen p s = k)).Nonempty)).card : ℚ) =
      coeff n (∑ s ∈ Finset.range (n + 1),
        X ^ ((s : ℤ) * (k + m) + k * (k - h - m + 1)).toNat *
          (qPochFin (X : ℚ⟦X⟧) ((s : ℤ) + k - h - m).toNat * qPochFin X (m - 1))⁻¹ *
          gaussBinom X (s + k - m) (k - m))

/-- The generating function for the number of odd partitions of `n` with an `h`-fixed hook in
the `m`th column arising from a part of size `k ≥ m` (`k` odd) is, with `j = s + h - k + m - 1`,
`Σ_{s ≥ k-h-m+1} q^{s(k+m)+m(m+h-k-1)}/((q²; q²)_{s-1} (q; q²)_{(m-1)/2}) [j + (k-m)/2, j]_{q²}`
for `m` odd and
`Σ_{s ≥ k-h-m+1} q^{s(k+m+1)+(m+1)(h-k)+m²-1}/((q²; q²)_{s-1} (q; q²)_{m/2})
 [j + (k-m-1)/2, j]_{q²}`
for `m` even.

Corrected reading: as printed, the Gaussian binomials are `[s+h-k + (k-m)/2, s+h-k]_{q²}` and
the even-`m` exponent is `s(k+m+1)+m(h-k+m)+h-k+1`, which is larger by `2`. Both are slips in
reindexing `k + m - 1 ↦ k` the `m = 1` formula in the paper's proof (its binomial index
`s + h - k` becomes `s + h - k + m - 1`, and its displayed even-`m` exponent simplifies to the
one stated here). As printed the statement is false: for `m = k = 3`, `h = 0`, the partition
`(3)` of `3` has the `0`-fixed hook `h_{1,3} = 1`, but the printed series has no `q³` term (its
first term is `q^{15}`); for `m = 2`, `k = 3`, `h = 0` the count for `n = 6` is `1` and the
printed series has no `q⁶` term. The sum is stated over `s = k - h - m + 1 + t`, coefficientwise
(the `t`-th term has no monomial below `q^t`); `(q; q²)_j` is `∏_{i<j} (1 - q^{2i+1})`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 8 (`integers-2025-A28-thm-8`), corrected per its proof. -/
public theorem_wanted fixedColumnHook_part_odd_genFun (n m k : ℕ) (h : ℤ) (hm : 1 ≤ m)
    (hmk : m ≤ k) (hk : Odd k) (hh : h + m ≤ k) :
    let oddPoch : ℕ → ℚ⟦X⟧ := fun j => ∏ i ∈ Finset.range j, (1 - X ^ (2 * i + 1))
    (((Nat.Partition.odds n).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s =>
          IsFixedColumnHook p m s h ∧ partitionRowLen p s = k)).Nonempty)).card : ℚ) =
      coeff n (∑ t ∈ Finset.range (n + 1),
        let s : ℤ := k - h - m + 1 + t
        if Odd m then
          X ^ (s * (k + m) + m * (m + h - k - 1)).toNat *
            (qPochFin ((X : ℚ⟦X⟧) ^ 2) (s - 1).toNat * oddPoch ((m - 1) / 2))⁻¹ *
            gaussBinom (X ^ 2) (t + (k - m) / 2) t
        else
          X ^ (s * (k + m + 1) + (m + 1) * (h - k) + m ^ 2 - 1).toNat *
            (qPochFin ((X : ℚ⟦X⟧) ^ 2) (s - 1).toNat * oddPoch (m / 2))⁻¹ *
            gaussBinom (X ^ 2) (t + (k - m - 1) / 2) t)

/-- The generating function for the number of distinct partitions of `n` with an `h`-fixed hook
in the `m`th column arising from a part of size `k ≥ m` is
`Σ_{s=0}^{k-m} q^{s(k+m)+k(k-h-m+1)+C(s+k-m+1-h, 2)+C(s, 2)} (-q; q)_{m-1}/(q; q)_{s+k-h-m}
 [k-m, s]_q`.

The journal denominator `(q; q)_{s+k-h-m}` is followed; the arXiv version (arXiv:2406.08609)
prints `(q; q)_{k-h-1}`, which is false (`m = 1`, `k = 2`, `h = 0`: the count for `n = 12` is
`3`, its coefficient `2`). `h ∈ ℤ` with `h ≤ k - m`; `(-q; q)_j` is `∏_{i<j} (1 + q^{i+1})`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 9 (`integers-2025-A28-thm-9`). -/
public theorem_wanted fixedColumnHook_part_distinct_genFun (n m k : ℕ) (h : ℤ) (hm : 1 ≤ m)
    (hmk : m ≤ k) (hh : h + m ≤ k) :
    (((Nat.Partition.distincts n).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s =>
          IsFixedColumnHook p m s h ∧ partitionRowLen p s = k)).Nonempty)).card : ℚ) =
      coeff n (∑ s ∈ Finset.range (k - m + 1),
        X ^ ((s : ℤ) * (k + m) + k * (k - h - m + 1) +
            (((s : ℤ) + k - m + 1 - h).toNat.choose 2 : ℕ) + (s.choose 2 : ℕ)).toNat *
          (∏ i ∈ Finset.range (m - 1), (1 + (X : ℚ⟦X⟧) ^ (i + 1))) *
          (qPochFin (X : ℚ⟦X⟧) ((s : ℤ) + k - h - m).toNat)⁻¹ * gaussBinom X (k - m) s)

/-- The generating function for the number of partitions of `n` with an `h`-fixed hook in the
first column arising from a hook of size `k` is
`Σ_{l=1}^{k} q^{k+l(k-h-1)}/(q; q)_{k-h-1} [k-1, l-1]_q`.

`h ∈ ℤ` with `h < k` (a fixed hook of size `k` sits in row `k - h ≥ 1`).

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 10 (`integers-2025-A28-thm-10`). -/
public theorem_wanted fixedFirstColumnHook_hook_genFun (n k : ℕ) (h : ℤ) (hk : 1 ≤ k)
    (hh : h < k) :
    (((Finset.univ : Finset n.Partition).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s =>
          IsFixedColumnHook p 1 s h ∧ partitionHookLength p s 1 = k)).Nonempty)).card : ℚ) =
      coeff n (∑ l ∈ Finset.Icc 1 k, X ^ ((k : ℤ) + l * (k - h - 1)).toNat *
        (qPochFin (X : ℚ⟦X⟧) ((k : ℤ) - h - 1).toNat)⁻¹ * gaussBinom X (k - 1) (l - 1))

/-- The generating function for the number of partitions of `n` with an `h`-fixed hook in the
`m`th column arising from a hook of size `k` is
`Σ_{l=1}^{k} q^{(m-1)(2k-h-l)+k+l(k-h-1)}/((q; q)_{k-h-1} (q; q)_{m-1}) [k-1, l-1]_q`.

`h ∈ ℤ` with `h < k`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 11 (`integers-2025-A28-thm-11`). -/
public theorem_wanted fixedColumnHook_hook_genFun (n m k : ℕ) (h : ℤ) (hm : 1 ≤ m)
    (hk : 1 ≤ k) (hh : h < k) :
    (((Finset.univ : Finset n.Partition).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s =>
          IsFixedColumnHook p m s h ∧ partitionHookLength p s m = k)).Nonempty)).card : ℚ) =
      coeff n (∑ l ∈ Finset.Icc 1 k,
        X ^ (((m : ℤ) - 1) * (2 * k - h - l) + k + l * (k - h - 1)).toNat *
          (qPochFin (X : ℚ⟦X⟧) ((k : ℤ) - h - 1).toNat * qPochFin X (m - 1))⁻¹ *
          gaussBinom X (k - 1) (l - 1))

/-- The generating function for the number of odd partitions of `n` with an `h`-fixed hook in
the `m`th column arising from a hook of size `k` is
`Σ_{l ≤ k, l odd} q^{k+l(k-h-1)+(m-1)(2k-h-l)}/((q²; q²)_{k-h-1} (q; q²)_{(m-1)/2})
 [k-l+(l-1)/2, k-l]_{q²}` for `m` odd and
`Σ_{l ≤ k, l even} q^{k+l(k-h-1)+(m-1)(2k-h-l)+(k-l)}/((q²; q²)_{k-h-1} (q; q²)_{m/2})
 [k-l+(l-2)/2, k-l]_{q²}` for `m` even (sums over `1 ≤ l ≤ k`).

`h ∈ ℤ` with `h < k`; `(q; q²)_j` is `∏_{i<j} (1 - q^{2i+1})`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 12 (`integers-2025-A28-thm-12`). -/
public theorem_wanted fixedColumnHook_hook_odd_genFun (n m k : ℕ) (h : ℤ) (hm : 1 ≤ m)
    (hk : 1 ≤ k) (hh : h < k) :
    let oddPoch : ℕ → ℚ⟦X⟧ := fun j => ∏ i ∈ Finset.range j, (1 - X ^ (2 * i + 1))
    (((Nat.Partition.odds n).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s =>
          IsFixedColumnHook p m s h ∧ partitionHookLength p s m = k)).Nonempty)).card : ℚ) =
      coeff n (if Odd m then
        ∑ l ∈ (Finset.Icc 1 k).filter Odd,
          X ^ ((k : ℤ) + l * (k - h - 1) + (m - 1) * (2 * k - h - l)).toNat *
            (qPochFin ((X : ℚ⟦X⟧) ^ 2) ((k : ℤ) - h - 1).toNat * oddPoch ((m - 1) / 2))⁻¹ *
            gaussBinom (X ^ 2) (k - l + (l - 1) / 2) (k - l)
      else
        ∑ l ∈ (Finset.Icc 1 k).filter Even,
          X ^ ((k : ℤ) + l * (k - h - 1) + (m - 1) * (2 * k - h - l) + (k - l)).toNat *
            (qPochFin ((X : ℚ⟦X⟧) ^ 2) ((k : ℤ) - h - 1).toNat * oddPoch (m / 2))⁻¹ *
            gaussBinom (X ^ 2) (k - l + (l - 2) / 2) (k - l))

/-- The generating function for the number of distinct partitions of `n` with an `h`-fixed hook
in the `m`th column arising from a hook of size `k` is
`Σ_{l=⌈(k+1)/2⌉}^{k} q^{k+l(k-h-1)+(m-1)(2k-h-l)+C(k-h, 2)+C(k-l, 2)} (-q; q)_{m-1}/(q; q)_{k-h-1}
 [l-1, k-l]_q`.

`h ∈ ℤ` with `h < k`; `⌈(k+1)/2⌉ = (k + 2)/2` in `ℕ`; `(-q; q)_j` is `∏_{i<j} (1 + q^{i+1})`.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 13 (`integers-2025-A28-thm-13`). -/
public theorem_wanted fixedColumnHook_hook_distinct_genFun (n m k : ℕ) (h : ℤ) (hm : 1 ≤ m)
    (hk : 1 ≤ k) (hh : h < k) :
    (((Nat.Partition.distincts n).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s =>
          IsFixedColumnHook p m s h ∧ partitionHookLength p s m = k)).Nonempty)).card : ℚ) =
      coeff n (∑ l ∈ Finset.Icc ((k + 2) / 2) k,
        X ^ ((k : ℤ) + l * (k - h - 1) + (m - 1) * (2 * k - h - l) +
            (((k : ℤ) - h).toNat.choose 2 : ℕ) + ((k - l).choose 2 : ℕ)).toNat *
          (∏ i ∈ Finset.range (m - 1), (1 + (X : ℚ⟦X⟧) ^ (i + 1))) *
          (qPochFin (X : ℚ⟦X⟧) ((k : ℤ) - h - 1).toNat)⁻¹ * gaussBinom X (l - 1) (k - l))

/-- For even `m`, the generating function for the number of odd distinct partitions of `n` with
an `h`-fixed hook in the `m`th column arising from a hook of size `k` is
`Σ_{l=⌈2k/3⌉, l even}^{k} q^{k-l+(m-1)(2k-h-l)+k+l(k-h-1)+2C(k-h, 2)+2C(k-l, 2)}
 (-q; q²)_{m/2}/(q²; q²)_{k-h-1} [k-l+(3l-2k-2)/2, k-l]_{q²}`.

Only the even-`m` case is stated: the odd-`m` case prints the binomial top index
`k - l + (3l - 2k)/2` over odd `l`, which is not an integer. `h ∈ ℤ` with `h < k`;
`⌈2k/3⌉ = (2k + 2)/3` in `ℕ`; `(-q; q²)_j` is `∏_{i<j} (1 + q^{2i+1})`; the top index is
computed in `ℤ` (it is `≥ 0` on the range).

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 14 (`integers-2025-A28-thm-14`), even `m`. -/
public theorem_wanted fixedColumnHook_hook_oddDistinct_genFun_even (n m k : ℕ) (h : ℤ)
    (hm : 1 ≤ m) (hme : Even m) (hk : 1 ≤ k) (hh : h < k) :
    (((Nat.Partition.odds n ∩ Nat.Partition.distincts n).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s =>
          IsFixedColumnHook p m s h ∧ partitionHookLength p s m = k)).Nonempty)).card : ℚ) =
      coeff n (∑ l ∈ (Finset.Icc ((2 * k + 2) / 3) k).filter Even,
        X ^ ((k : ℤ) - l + (m - 1) * (2 * k - h - l) + k + l * (k - h - 1) +
            2 * (((k : ℤ) - h).toNat.choose 2 : ℕ) + 2 * ((k - l).choose 2 : ℕ)).toNat *
          (∏ i ∈ Finset.range (m / 2), (1 + (X : ℚ⟦X⟧) ^ (2 * i + 1))) *
          (qPochFin ((X : ℚ⟦X⟧) ^ 2) ((k : ℤ) - h - 1).toNat)⁻¹ *
          gaussBinom (X ^ 2) ((k : ℤ) - l + (3 * l - 2 * k - 2) / 2).toNat (k - l))

end

end MetaMathlibExt
