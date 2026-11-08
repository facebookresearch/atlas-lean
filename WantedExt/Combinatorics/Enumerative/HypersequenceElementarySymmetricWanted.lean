/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import WantedExt.Combinatorics.Enumerative.HypersequenceWeightedSumsWanted

namespace MetaMathlibExt

@[expose] public section

/-! # Elementary symmetric coefficients from Parisse's hypersequence paper

Parisse writes `e_{j,k}(n)` for the elementary symmetric polynomial of degree `k` in
`x_1(n) = n + 1, …, x_j(n) = n + j` (Theorem 1, Equation (2.2)); here it is
`((Finset.Icc 1 j).val.map (n + ·)).esymm k` over `ℕ`. Unsigned Stirling numbers of the first
kind are `Nat.stirlingFirst`, and the rising factorial power `n^(j̄) = n (n + 1) ⋯ (n + j - 1)`
is `Nat.ascFactorial n j`.

The signed entries `b_{j,k}(n) = (-1)^k e_{j,j-k}(n)` of `B(n)` are `hyperseqB`; the entries
`c_{ℓ,m}(n)` of `C(n)` are `alternatingBinomialPowerSum ℓ m 1 (n + 1)` and the hypersequence
`a^{(r)}_n` is `hypersequence a r n`, both from the first paper's module; Mitrinović's numbers
`R^k_j(a, b)` (Section 4) are `mitrinovicR`.
-/

/-- The coefficients `e_{j,k}(n)` satisfy `e_{0,k}(n) = δ_{0,k}` and the recurrence
`e_{j,k}(n) = e_{j-1,k}(n) + (n + j) e_{j-1,k-1}(n)` (3.1), have the closed form
`e_{j,k}(n) = ∑_{ℓ=0}^{k} binom(j-k+ℓ, ℓ) [j, j-k+ℓ] (n + 1)^ℓ` for `k ≤ j` (3.2), row sums
`∑_k e_{j,k}(n) = (n + 2)^(j̄)` (3.3) and alternating row sums
`∑_k (-1)^k e_{j,k}(n) = (-1)^j n^(j̄)` (3.4).

The recurrence is stated for `j, k ≥ 1` (shifted indices), and the closed form for `k ≤ j`
(for `k > j` both `e_{j,k}(n)` and the paper's empty-range conventions give `0`).

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36, Proposition 1 (`integers-2026-A36-prop-1`). -/
public theorem_wanted hyperseq_esymm_recurrence_closed_form_row_sums (n : ℕ) :
    (∀ k : ℕ, ((Finset.Icc 1 0).val.map (n + ·)).esymm k = if k = 0 then 1 else 0) ∧
    (∀ j k : ℕ, ((Finset.Icc 1 (j + 1)).val.map (n + ·)).esymm (k + 1) =
      ((Finset.Icc 1 j).val.map (n + ·)).esymm (k + 1) +
        (n + (j + 1)) * ((Finset.Icc 1 j).val.map (n + ·)).esymm k) ∧
    (∀ j k : ℕ, k ≤ j → ((Finset.Icc 1 j).val.map (n + ·)).esymm k =
      ∑ ℓ ∈ Finset.range (k + 1),
        (j - k + ℓ).choose ℓ * Nat.stirlingFirst j (j - k + ℓ) * (n + 1) ^ ℓ) ∧
    (∀ j : ℕ, ∑ k ∈ Finset.range (j + 1), ((Finset.Icc 1 j).val.map (n + ·)).esymm k =
      (n + 2).ascFactorial j) ∧
    ∀ j : ℕ, ∑ k ∈ Finset.range (j + 1),
        (-1 : ℤ) ^ k * (((Finset.Icc 1 j).val.map (n + ·)).esymm k : ℕ) =
      (-1 : ℤ) ^ j * (n.ascFactorial j : ℕ)

/-- At `n = 0`: `e_{0,k}(0) = δ_{0,k}`, `e_{j,k}(0) = e_{j-1,k}(0) + j e_{j-1,k-1}(0)` (3.6),
and for `k ≤ j`, `e_{j,k}(0) = ∑_{ℓ=0}^{k} binom(j-k+ℓ, ℓ) [j, j-k+ℓ] = [j + 1, j + 1 - k]`
(3.7).

At `n = 0` the variables are `1, …, j`, so `e_{j,k}(0)` is `((Finset.Icc 1 j).val).esymm k`.
The recurrence is stated for `j, k ≥ 1` (shifted indices) and the closed form for `k ≤ j`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36, Corollary 3 (`integers-2026-A36-cor-3`). -/
public theorem_wanted hyperseq_esymm_zero_recurrence_stirling :
    (∀ k : ℕ, ((Finset.Icc 1 0).val).esymm k = if k = 0 then 1 else 0) ∧
    (∀ j k : ℕ, ((Finset.Icc 1 (j + 1)).val).esymm (k + 1) =
      ((Finset.Icc 1 j).val).esymm (k + 1) +
        (j + 1) * ((Finset.Icc 1 j).val).esymm k) ∧
    ∀ j k : ℕ, k ≤ j →
      ((Finset.Icc 1 j).val).esymm k =
          ∑ ℓ ∈ Finset.range (k + 1), (j - k + ℓ).choose ℓ * Nat.stirlingFirst j (j - k + ℓ) ∧
        ((Finset.Icc 1 j).val).esymm k = Nat.stirlingFirst (j + 1) (j + 1 - k)


/-- Parisse's `b_{j,k}(n) := (-1)^k e_{j,j-k}(n)` (Equation (2.5)), zero for `k > j`, where
`e_{j,i}(n)` is the elementary symmetric polynomial of degree `i` in `n + 1, …, n + j`. The
argument `n` is an integer because the source also uses `n ∈ ℤ` (Proposition 3, after
Remark 1). See `hyperseqB_one` and `hyperseqB_row_three`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 2, Equation (2.5). -/
public def hyperseqB (n : ℤ) (j k : ℕ) : ℤ :=
  if k ≤ j then (-1) ^ k * ((Finset.Icc 1 j).val.map fun i : ℕ => n + i).esymm (j - k) else 0

/-- Row one of `B(n)` is `n + 1, -1`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 2, display of `B(n)`. -/
public theorem hyperseqB_one (n : ℤ) : hyperseqB n 1 0 = n + 1 ∧ hyperseqB n 1 1 = -1 := by
  simp [hyperseqB, Multiset.esymm, Multiset.powersetCard_one]

/-- Row three of `B(1)` is `24, -26, 9, -1`, matching the display
`(n + 1)(n + 2)(n + 3), -(3n² + 12n + 11), 3n + 6, -1` at `n = 1`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 2, display of `B(n)`. -/
public theorem hyperseqB_row_three :
    (List.range 4).map (hyperseqB 1 3) = [24, -26, 9, -1] := by
  decide +kernel

/-- Mitrinović's numbers `R^k_j(a, b)` (lower index `j`, upper index `k`), given by
`R^k_0 = δ_{0,k}` and the recurrence (4.2)
`R^k_j(a, b) = R^{k-1}_{j-1}(a, b) - (a - b + b j) R^k_{j-1}(a, b)`, with `R = 0` at negative
indices. The start value `R^k_0 = δ_{0,k}` is the source's Corollary 5 at `a = 0` and its
solution (4.3) at `j = 0` for every `a`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 4, Equation (4.2). -/
public def mitrinovicR (a b : ℂ) : ℕ → ℕ → ℂ
  | 0, k => if k = 0 then 1 else 0
  | j + 1, 0 => -(a + b * j) * mitrinovicR a b j 0
  | j + 1, k + 1 => mitrinovicR a b j k - (a + b * j) * mitrinovicR a b j (k + 1)

/-- `R^0_1(a, b) = -a` and `R^1_1(a, b) = 1`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 4, Equation (4.2). -/
public theorem mitrinovicR_one (a b : ℂ) :
    mitrinovicR a b 1 0 = -a ∧ mitrinovicR a b 1 1 = 1 := by
  simp [mitrinovicR]

/-- Theorem 1: for every complex sequence `a` and `j, n ∈ ℕ`, with
`t_i(n) = ∑_{k=0}^{n} k^i a_k` (`0^0 = 1`),
`j! a^{(j+1)}_n = (-1)^j ∑_{k=0}^{j} (-1)^k e_{j,k}(n) t_{j-k}(n)
  = ∑_{k=0}^{j} (-1)^k e_{j,j-k}(n) t_k(n)`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Theorem 1, Equation (2.1) (`integers-2026-A36-thm-1`). -/
public theorem_wanted factorial_mul_hypersequence_eq_sum_esymm (a : ℕ → ℂ) (j n : ℕ) :
    (j.factorial : ℂ) * hypersequence a (j + 1) n =
        (-1) ^ j * ∑ k ∈ Finset.range (j + 1), (-1) ^ k *
          (((Finset.Icc 1 j).val.map (n + ·)).esymm k : ℕ) *
            ∑ i ∈ Finset.range (n + 1), (i : ℂ) ^ (j - k) * a i ∧
      (j.factorial : ℂ) * hypersequence a (j + 1) n =
        ∑ k ∈ Finset.range (j + 1), (-1) ^ k *
          (((Finset.Icc 1 j).val.map (n + ·)).esymm (j - k) : ℕ) *
            ∑ i ∈ Finset.range (n + 1), (i : ℂ) ^ k * a i

/-- Theorem 2: `C(n)⁻¹ = D⁻¹ B(n)`, i.e. the lower triangular matrix with entries
`b_{j,k}(n) / j!` is a two-sided inverse of `C(n) = (c_{ℓ,m}(n))`, where
`c_{ℓ,m}(n) = ∑_{k=0}^{m} (-1)^k C(m, k) (k + n + 1)^ℓ = p_{ℓ,m}(1, n + 1)`. Both matrices are
lower triangular, so the products are finite sums over `k ≤ j`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Theorem 2 (`integers-2026-A36-thm-2`). -/
public theorem_wanted hyperseqC_inv_eq_hyperseqB_div_factorial (n j m : ℕ) :
    ∑ k ∈ Finset.range (j + 1), (hyperseqB n j k : ℂ) / j.factorial *
        alternatingBinomialPowerSum k m 1 (n + 1) = (if j = m then 1 else 0) ∧
      ∑ k ∈ Finset.range (j + 1), alternatingBinomialPowerSum j k 1 (n + 1) *
        ((hyperseqB n k m : ℂ) / k.factorial) = if j = m then 1 else 0

/-- Corollary 1: `B(n)⁻¹ = C(n) D⁻¹`, i.e. the lower triangular matrix with entries
`c_{ℓ,m}(n) / m!` is a two-sided inverse of `B(n)`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Corollary 1, Equation (2.9) (`integers-2026-A36-cor-1`). -/
public theorem_wanted hyperseqB_inv_eq_hyperseqC_div_factorial (n j m : ℕ) :
    ∑ k ∈ Finset.range (j + 1), (hyperseqB n j k : ℂ) *
        (alternatingBinomialPowerSum k m 1 (n + 1) / m.factorial) = (if j = m then 1 else 0) ∧
      ∑ k ∈ Finset.range (j + 1), alternatingBinomialPowerSum j k 1 (n + 1) / k.factorial *
        (hyperseqB n k m : ℂ) = if j = m then 1 else 0

/-- Corollary 2: `∑_{i=0}^{j} b_{j,i}(n) c_{i,m}(n) = j! δ_{j,m}` for all `j, m, n ∈ ℕ`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Corollary 2 (`integers-2026-A36-cor-2`). -/
public theorem_wanted sum_hyperseqB_mul_hyperseqC (n j m : ℕ) :
    ∑ i ∈ Finset.range (j + 1), (hyperseqB n j i : ℂ) * alternatingBinomialPowerSum i m 1 (n + 1) =
      if j = m then (j.factorial : ℂ) else 0

/-- Proposition 2: for `n ∈ ℕ`, `b_{0,k}(n) = δ_{0,k}` and
`b_{j,k}(n) = (n + j) b_{j-1,k}(n) - b_{j-1,k-1}(n)` (3.8) (stated with shifted indices, the
`k = 0` case using `b_{j-1,-1} = 0`); the solution
`b_{j,k}(n) = (-1)^k ∑_{ℓ=k}^{j} C(ℓ, k) [j, ℓ] (n + 1)^{ℓ-k}` (3.9) with `[j, ℓ]` the unsigned
Stirling numbers of the first kind; the row sums `∑_k b_{j,k}(n) = n^(j̄)` (3.10) and the
alternating row sums `∑_k (-1)^k b_{j,k}(n) = (n + 2)^(j̄)` (3.11), with the rising factorial
`Nat.ascFactorial`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Proposition 2 (`integers-2026-A36-prop-2`). -/
public theorem_wanted hyperseqB_recurrence_closed_form_row_sums (n : ℕ) :
    (∀ k : ℕ, hyperseqB n 0 k = if k = 0 then 1 else 0) ∧
    (∀ j : ℕ, hyperseqB n (j + 1) 0 = (n + (j + 1)) * hyperseqB n j 0) ∧
    (∀ j k : ℕ, hyperseqB n (j + 1) (k + 1) =
      (n + (j + 1)) * hyperseqB n j (k + 1) - hyperseqB n j k) ∧
    (∀ j k : ℕ, hyperseqB n j k = (-1) ^ k * ∑ ℓ ∈ Finset.Icc k j,
      (ℓ.choose k * Nat.stirlingFirst j ℓ : ℤ) * ((n : ℤ) + 1) ^ (ℓ - k)) ∧
    (∀ j : ℕ, ∑ k ∈ Finset.range (j + 1), hyperseqB n j k = (n.ascFactorial j : ℤ)) ∧
    ∀ j : ℕ, ∑ k ∈ Finset.range (j + 1), (-1) ^ k * hyperseqB n j k =
      ((n + 2).ascFactorial j : ℤ)

/-- Corollary 4: `b_{0,k}(0) = δ_{0,k}`, `b_{j,k}(0) = j b_{j-1,k}(0) - b_{j-1,k-1}(0)` (3.13)
(shifted indices), and `b_{j,k}(0) = (-1)^k ∑_{ℓ=k}^{j} C(ℓ, k) [j, ℓ] = (-1)^k [j + 1, k + 1]`
(3.14).

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Corollary 4 (`integers-2026-A36-cor-4`). -/
public theorem_wanted hyperseqB_zero_recurrence_stirling :
    (∀ k : ℕ, hyperseqB 0 0 k = if k = 0 then 1 else 0) ∧
    (∀ j : ℕ, hyperseqB 0 (j + 1) 0 = (j + 1) * hyperseqB 0 j 0) ∧
    (∀ j k : ℕ, hyperseqB 0 (j + 1) (k + 1) = (j + 1) * hyperseqB 0 j (k + 1) - hyperseqB 0 j k) ∧
    ∀ j k : ℕ,
      hyperseqB 0 j k = (-1) ^ k * ∑ ℓ ∈ Finset.Icc k j, (ℓ.choose k * Nat.stirlingFirst j ℓ : ℤ) ∧
        hyperseqB 0 j k = (-1) ^ k * Nat.stirlingFirst (j + 1) (k + 1)

/-- Proposition 3: for all `n ∈ ℤ` and `j, k, ℓ, m ∈ ℕ`,
`e_{j,k}(n) = ∑_{i=0}^{k} C(j - k + i, i) (n + 1)^i e_{j,k-i}(-1)` (3.20) (for `k ≤ j`),
`b_{j,k}(n) = ∑_{i=k}^{j} (-1)^{i-k} C(i, k) (n + 1)^{i-k} b_{j,i}(-1)` (3.21), and
`c_{ℓ,m}(n) = ∑_{i=m}^{ℓ} C(ℓ, i) (n + 1)^{ℓ-i} c_{i,m}(-1)` (3.22). Here `e_{j,k}(n)` is the
elementary symmetric polynomial of degree `k` in `n + 1, …, n + j` over `ℤ`. Equation (3.20) is
stated for `k ≤ j` (for `k > j` the natural-number binomial `C(j - k + i, i)` misreads the
source's index `j - k + i`).

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Proposition 3 (`integers-2026-A36-prop-3`). -/
public theorem_wanted hyperseq_entries_eq_sum_at_neg_one (n : ℤ) :
    (∀ j k : ℕ, k ≤ j → ((Finset.Icc 1 j).val.map fun i : ℕ => n + i).esymm k =
      ∑ i ∈ Finset.range (k + 1), ((j - k + i).choose i : ℤ) * (n + 1) ^ i *
        ((Finset.Icc 1 j).val.map fun i : ℕ => (-1 : ℤ) + i).esymm (k - i)) ∧
    (∀ j k : ℕ, hyperseqB n j k =
      ∑ i ∈ Finset.Icc k j, (-1) ^ (i - k) * (i.choose k : ℤ) * (n + 1) ^ (i - k) *
        hyperseqB (-1) j i) ∧
    ∀ ℓ m : ℕ, alternatingBinomialPowerSum ℓ m 1 (n + 1) =
      ∑ i ∈ Finset.Icc m ℓ, (ℓ.choose i : ℂ) * ((n : ℂ) + 1) ^ (ℓ - i) *
        alternatingBinomialPowerSum i m 1 0

/-- Corollary 5: `R^k_0(0, b) = δ_{0,k}`, `R^k_j(0, b) = R^{k-1}_{j-1}(0, b) + (b - b j)
R^k_{j-1}(0, b)` (shifted indices), and `R^k_j(0, b) = (-b)^{j-k} [j, k]` (4.5), with `[j, k]`
the unsigned Stirling numbers of the first kind (`0` for `k > j`). The source prints the last
factor of the recurrence as `R^k_{j-1}(a, b)`; it is `R^k_{j-1}(0, b)`, the case `a = 0` of
(4.2). The source's hypothesis `b ≠ 0` is dropped: at `b = 0` both sides are `δ_{j,k}`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Corollary 5 (`integers-2026-A36-cor-5`). -/
public theorem_wanted mitrinovicR_zero_eq (b : ℂ) :
    (∀ k : ℕ, mitrinovicR 0 b 0 k = if k = 0 then 1 else 0) ∧
    (∀ j k : ℕ, mitrinovicR 0 b (j + 1) (k + 1) =
      mitrinovicR 0 b j k + (b - b * (j + 1)) * mitrinovicR 0 b j (k + 1)) ∧
    ∀ j k : ℕ, mitrinovicR 0 b j k = (-b) ^ (j - k) * Nat.stirlingFirst j k

/-- Proposition 4: `R^k_j(a, b) = ∑_{ℓ=0}^{j-k} (-1)^ℓ C(k + ℓ, ℓ) a^ℓ R^{k+ℓ}_j(0, b)` for all
`j, k ∈ ℕ` (for `k > j` both sides are `0`). The source's hypothesis `b ≠ 0` is dropped: the
identity also holds at `b = 0`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Proposition 4, Equation (4.6) (`integers-2026-A36-prop-4`). -/
public theorem_wanted mitrinovicR_eq_sum_mitrinovicR_zero (a b : ℂ) (j k : ℕ) :
    mitrinovicR a b j k =
      ∑ ℓ ∈ Finset.range (j - k + 1), (-1) ^ ℓ * ((k + ℓ).choose ℓ : ℂ) * a ^ ℓ *
        mitrinovicR 0 b j (k + ℓ)

end

end MetaMathlibExt
