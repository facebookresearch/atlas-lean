/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.GaussianBinomial
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Limit of the fixed-hook generating functions

The normalized generating functions for hooks in a fixed column stabilize coefficientwise.
The proof uses the Pascal recursion for Gaussian binomials after clearing the denominators.
-/

namespace MetaMathlibExt

section

open Finset PowerSeries MathlibExt

namespace columnHook_size_genFun_limit

variable {R : Type*} [CommRing R]

/-- Pascal recursion summed against an arbitrary function of the lower index. -/
private theorem sum_gauss_succ (q : R) (f : ℕ → R) (d : ℕ) :
    ∑ j ∈ range (d + 2), gaussBinom q (d + 1) j * f j =
      ∑ j ∈ range (d + 1), gaussBinom q d j * (f (j + 1) + q ^ j * f j) := by
  have hshift : (∑ j ∈ range (d + 1), q ^ (j + 1) * gaussBinom q d (j + 1) * f (j + 1)) +
      f 0 = ∑ j ∈ range (d + 1), q ^ j * gaussBinom q d j * f j := by
    let g (j : ℕ) := q ^ j * gaussBinom q d j * f j
    have h := (sum_range_succ' g (d + 1)).symm.trans (sum_range_succ g (d + 1))
    simpa [g, gaussBinom_eq_zero_of_lt q d (d + 1) (by omega)] using h
  rw [sum_range_succ']
  simp only [gaussBinom_succ_succ, gaussBinom_zero_right, one_mul, add_mul,
    mul_add, sum_add_distrib, add_assoc, hshift]
  congr 1
  apply sum_congr rfl
  intro j _
  ring

private def poch (q z : R) (j : ℕ) : R := ∏ i ∈ range j, (1 - z * q ^ i)

/-- The two terms from the Pascal recursion cancel the last factor of the product. -/
private theorem sum_gauss_poch (q z : R) (d : ℕ) :
    ∑ j ∈ range (d + 1), gaussBinom q d j * (z ^ (d - j) * poch q z j) = 1 := by
  induction d with
  | zero => simp [poch]
  | succ d ih =>
    rw [sum_gauss_succ, ← ih]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [show d + 1 - j = d - j + 1 by omega, Nat.add_sub_add_right, pow_succ]
    simp only [poch, prod_range_succ]
    ring

private theorem poch_shift (a j : ℕ) (q : R) :
    (1 - q ^ a) * (∏ i ∈ range j, (1 - q ^ (a + 1 + i))) =
      poch q (q ^ a) j * (1 - q ^ (a + j)) := by
  have h := (prod_range_succ' (fun i => 1 - q ^ (a + i)) j).symm.trans
    (prod_range_succ (fun i => 1 - q ^ (a + i)) j)
  simpa only [poch, ← pow_add, Nat.add_zero, Nat.add_right_comm a 1, Nat.add_assoc,
    Nat.add_comm 1, mul_comm (1 - q ^ a)] using h

private theorem constantCoeff_qPoch (j : ℕ) :
    constantCoeff (qPochFin (X : ℚ⟦X⟧) j) = 1 := by
  simp [qPochFin, map_prod]

/-- Multiply the sum by its limiting denominator. In degree at most `d`, each summand
then agrees with the corresponding term of `sum_gauss_poch`. -/
private theorem cleared_sum (F : ℚ⟦X⟧ →+* R) (a d : ℕ) (ha : 1 ≤ a)
    (hd : F X ^ (d + 1) = 0) :
    F (((1 - X ^ a) * qPochFin X d) *
      ∑ j ∈ range (d + 1), X ^ (a * (d - j)) *
        (∏ i ∈ range j, (1 - X ^ (a + 1 + i))) *
        (qPochFin X j * qPochFin X (d - j))⁻¹) = 1 := by
  conv_rhs => rw [← map_one F, ← sum_gauss_poch X (X ^ a) d]
  simp only [mul_sum, map_sum]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ d := by simpa using hj
  have hgauss : gaussBinom (X : ℚ⟦X⟧) d j =
      qPochFin X d * (qPochFin X j * qPochFin X (d - j))⁻¹ := by
    apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp [constantCoeff_qPoch])).2
    simpa only [← mul_assoc] using gaussBinom_mul_qPochFin_mul_qPochFin (X : ℚ⟦X⟧) d j hj'
  have hkill : F (X ^ (a * (d - j))) * F (X ^ (a + j)) = 0 := by
    rw [← map_mul, ← pow_add, map_pow]
    have hle := Nat.mul_le_mul_right (d - j) ha
    exact pow_eq_zero_of_le (by omega) hd
  rw [← pow_mul]
  calc
    _ = F ((qPochFin X d * (qPochFin X j * qPochFin X (d - j))⁻¹) *
        (X ^ (a * (d - j)) * ((1 - X ^ a) * ∏ i ∈ range j, (1 - X ^ (a + 1 + i))))) := by
      congr 1
      ring
    _ = _ := by
      rw [← hgauss, poch_shift]
      simp only [map_mul, map_sub, map_one]
      linear_combination -F (gaussBinom X d j) * F (poch X (X ^ a) j) * hkill

private theorem sum_Icc_one (f : ℕ → ℚ⟦X⟧) (d : ℕ) :
    ∑ l ∈ Icc 1 (d + 1), f l = ∑ j ∈ range (d + 1), f (j + 1) := by
  rw [← Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

end columnHook_size_genFun_limit

open columnHook_size_genFun_limit

/-- **Limit of the fixed-hook generating functions.** Let $m \ge 2$ be a natural number and work
in $\mathbb{Q}[[q]]$. For $j \in \mathbb{N}$ write $(q;q)_j = \prod_{i=1}^{j} (1 - q^i)$ and
$(q^m;q)_j = \prod_{i=0}^{j-1} (1 - q^{m+i})$. Then for every natural number $n$ there is a $K$
such that for every $k \ge K$ the coefficient of $q^n$ in
$$
\frac{q^{m-1}}{\prod_{i=0}^{n} (1 - q^{k+i})}
\sum_{l=1}^{k} \frac{q^{(m-1)(k-l)} (q^m;q)_{l-1}}{(q;q)_{l-1} (q;q)_{k-l}}
$$
equals the coefficient of $q^n$ in
$$
\frac{q^{m-1}}{(1 - q^{m-1}) (q;q)_{n+1}}.
$$

This is the coefficientwise ($q$-adic) form of the limit
$$
\lim_{k \to \infty} \frac{q^{m-1}}{(q^k;q)_\infty}
\sum_{l=1}^{k} \frac{q^{(m-1)(k-l)} (q^m;q)_{l-1}}{(q;q)_{l-1} (q;q)_{k-l}}
= \frac{q^{m-1}}{(1 - q^{m-1}) (q;q)_\infty},
$$
where $(a;q)_\infty = \prod_{i \ge 0} (1 - a q^i)$: for the coefficient of $q^n$, the products
$(q^k;q)_\infty$ and $(q;q)_\infty$ are replaced by their first $n + 1$ factors, which changes no
coefficient below $q^{n+1}$.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 5 (`integers-2025-A28-thm-5`). -/
public theorem columnHook_size_genFun_limit (m : ℕ) (hm : 2 ≤ m) (n : ℕ) :
    ∀ᶠ k in Filter.atTop,
      coeff n (X ^ (m - 1) * (∏ i ∈ Finset.range (n + 1), (1 - X ^ (k + i)))⁻¹ *
        ∑ l ∈ Finset.Icc 1 k, X ^ ((m - 1) * (k - l)) *
          (∏ i ∈ Finset.range (l - 1), (1 - X ^ (m + i))) *
          (qPochFin (X : ℚ⟦X⟧) (l - 1) * qPochFin X (k - l))⁻¹) =
      coeff n (X ^ (m - 1) * ((1 - X ^ (m - 1)) * qPochFin (X : ℚ⟦X⟧) (n + 1))⁻¹) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  have ha : 1 ≤ a := by omega
  apply Filter.eventually_atTop.2
  refine ⟨n + 2, ?_⟩
  rintro (_ | d) hk
  · omega
  let I : Ideal ℚ⟦X⟧ := Ideal.span {(X : ℚ⟦X⟧) ^ (n + 1)}
  let F := Ideal.Quotient.mk I
  have hX : F X ^ (n + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have low_coeff (x y : ℚ⟦X⟧) (h : F x = F y) : coeff n x = coeff n y := by
    have hdvd : X ^ (n + 1) ∣ x - y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
    simpa only [map_sub, sub_eq_zero] using X_pow_dvd_iff.mp hdvd n (by omega)
  apply low_coeff
  rw [sum_Icc_one]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_sub_add_right]
  -- Beyond degree n the prefactor is one, and all longer Pochhammer products agree.
  have hpref : F ((∏ i ∈ range (n + 1), (1 - X ^ (d + 1 + i)))⁻¹) = 1 := by
    have hp : F (∏ i ∈ range (n + 1), (1 - X ^ (d + 1 + i))) = 1 := by
      rw [map_prod]
      apply prod_eq_one
      intro i _
      simp [pow_eq_zero_of_le (show n + 1 ≤ d + 1 + i by omega) hX]
    have hunit := PowerSeries.mul_inv_cancel
      (∏ i ∈ range (n + 1), (1 - (X : ℚ⟦X⟧) ^ (d + 1 + i)))
      (by simp [map_prod])
    simpa only [hp, one_mul] using map_mul_eq_one F hunit
  have hpoch : F (qPochFin X d) = F (qPochFin X (n + 1)) := by
    simp only [qPochFin, map_prod, map_sub, map_one, map_pow]
    apply eventually_constant_prod _ (by omega)
    intro i hi
    simp [pow_eq_zero_of_le (show n + 1 ≤ i + 1 by omega) hX]
  have hsum := cleared_sum F a d ha (pow_eq_zero_of_le (by omega) hX)
  rw [map_mul, map_mul, hpoch, ← map_mul, mul_comm] at hsum
  rw [map_mul, map_mul, hpref, mul_one, map_mul]
  congr 1
  apply left_inv_eq_right_inv hsum
  apply map_mul_eq_one
  apply PowerSeries.mul_inv_cancel
  simp [constantCoeff_qPoch, Nat.ne_of_gt ha]

end

@[expose] public section

/-- **Column lengths of a partition.** For a partition $\lambda$ of $n$ and a natural number $j$,
the column length $\lambda'_j$ is the number of parts of $\lambda$, counted with multiplicity, that
are at least $j$. For $j \ge 1$ this is the length of the $j$-th column of the Young diagram of
$\lambda$, with columns numbered from $1$.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Section 1 (`λ'`, the conjugate partition). -/
def partitionColLen {n : ℕ} (p : n.Partition) (j : ℕ) : ℕ :=
  (p.parts.filter (j ≤ ·)).card

/-- **Row lengths of a partition.** For a partition $\lambda$ of $n$ and a natural number $s$, the
row length $\lambda_s$ is the number of $j \in \{1, \dots, n\}$ whose column length $\lambda'_j$ is
at least $s$. For $s \ge 1$ this is the $s$-th largest part of $\lambda$ (rows are numbered from
$1$), and it is $0$ when $\lambda$ has fewer than $s$ parts.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Section 1 (`λ = (λ₁, λ₂, …)` weakly decreasing). -/
def partitionRowLen {n : ℕ} (p : n.Partition) (s : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun j => s ≤ partitionColLen p j)).card

/-- **Hook length of a square of a partition.** For a partition $\lambda$ of $n$ and natural numbers
$s$ and $m$, the hook length of the square in row $s$ and column $m$ is the integer
$h_{s,m}(\lambda) = \lambda_s + \lambda'_m - s - m + 1$, where $\lambda_s$ is the row length and
$\lambda'_m$ the column length defined above: for $s, m \ge 1$ they are the lengths of the $s$-th
row and the $m$-th column of the Young diagram (numbered from $1$), and at index $0$ they take the
values $\lambda_0 = n$ and $\lambda'_0$ = the number of parts of $\lambda$. The integer is given by
this formula for all $s$ and $m$, also when $(s, m)$ is not a square of the Young diagram.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Section 1. -/
def partitionHookLength {n : ℕ} (p : n.Partition) (s m : ℕ) : ℤ :=
  (partitionRowLen p s : ℤ) + partitionColLen p m - s - m + 1

/-- **Fixed hooks in a column of a partition.** Let $\lambda$ be a partition of $n$, let $m$ and $s$
be natural numbers and let $h$ be an integer. The partition $\lambda$ has an $h$-fixed hook in
column $m$ at row $s$ if the square $(s, m)$ lies in the Young diagram of $\lambda$, that is,
$s \ge 1$ and $1 \le m \le \lambda_s$, and its hook length is $h_{s,m}(\lambda) = s + h$. In other
words, the $s$-th term of the sequence $h_{1,m}(\lambda), h_{2,m}(\lambda), \dots$ of hook lengths
in column $m$ is an $h$-fixed point.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Section 1 (an `h`-fixed point of the sequence
`h_{1,m}(λ), h_{2,m}(λ), …`; Figure 2: `h_{m,s} = s + h` at part `λ_s`). -/
def IsFixedColumnHook {n : ℕ} (p : n.Partition) (m s : ℕ) (h : ℤ) : Prop :=
  1 ≤ s ∧ 1 ≤ m ∧ m ≤ partitionRowLen p s ∧ partitionHookLength p s m = s + h

instance {n : ℕ} (p : n.Partition) (m s : ℕ) (h : ℤ) :
    Decidable (IsFixedColumnHook p m s h) := by
  unfold IsFixedColumnHook; infer_instance

end

namespace FixedColumnHookBijection

open Multiset

private theorem col_antitone {n : ℕ} (p : n.Partition) : Antitone (partitionColLen p) := by
  intro i j hij
  exact card_le_card (monotone_filter_right _ fun _ hx => hij.trans hx)

private theorem le_row_iff {n r j : ℕ} (p : n.Partition) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    j ≤ partitionRowLen p r ↔ r ≤ partitionColLen p j := by
  constructor
  · intro hrow
    by_contra! hcol
    have hs : ((Finset.Icc 1 n).filter (fun i => r ≤ partitionColLen p i)) ⊆
        Finset.Icc 1 (j - 1) := by
      intro i hi
      obtain ⟨hi, hri⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, ?_⟩
      by_contra! hij
      exact (hcol.not_ge (hri.trans (col_antitone p (show j ≤ i by omega))))
    have hc := Finset.card_le_card hs
    rw [Nat.card_Icc] at hc
    unfold partitionRowLen at hrow
    omega
  · intro hcol
    have hjn : j ≤ n := by
      by_contra! hjn
      have hz : p.parts.filter (j ≤ ·) = 0 := filter_eq_nil.mpr fun _ hx h =>
        hjn.not_ge (h.trans (Nat.Partition.le_of_mem_parts hx))
      simp [partitionColLen, hz] at hcol
      omega
    have hs : Finset.Icc 1 j ⊆
        (Finset.Icc 1 n).filter (fun i => r ≤ partitionColLen p i) := by
      intro i hi
      obtain ⟨hi, hij⟩ := Finset.mem_Icc.mp hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hi, hij.trans hjn⟩, hcol.trans (col_antitone p hij)⟩
    simpa [Nat.card_Icc, partitionRowLen] using Finset.card_le_card hs

/-- The common data for the two partitions: rows above the hook, and parts shorter than `m`.
The rows strictly below the hook and still in the column all have length `m`; their number is
`above.card + h`. -/
@[ext] private structure Split (m : ℕ) (h : ℤ) where
  above : Multiset ℕ
  small : Multiset ℕ
  above_ge : ∀ x ∈ above, m ≤ x
  small_lt : ∀ x ∈ small, x < m
  small_pos : ∀ x ∈ small, 0 < x
  height : -h ≤ (above.card : ℤ)

private def Split.leftParts {m : ℕ} {h : ℤ} (s : Split m h) : Multiset ℕ :=
  s.above + replicate (((s.above.card : ℤ) + h).toNat + 1) m + s.small

private def Split.rightParts {m : ℕ} {h : ℤ} (s : Split m h) : Multiset ℕ :=
  s.above.map (· + m) + {m} + s.small

private theorem Split.left_ge {m : ℕ} {h : ℤ} (s : Split m h) :
    s.leftParts.filter (m ≤ ·) = s.above + replicate (((s.above.card : ℤ) + h).toNat + 1) m := by
  simp [Split.leftParts, filter_add, filter_eq_self.mpr s.above_ge,
    filter_eq_self.mpr (fun _ hx => (eq_of_mem_replicate hx).symm.le),
    filter_eq_nil.mpr (fun x hx => (s.small_lt x hx).not_ge)]

private theorem Split.left_lt {m : ℕ} {h : ℤ} (s : Split m h) :
    s.leftParts.filter (· < m) = s.small := by
  simp [Split.leftParts, filter_add, filter_eq_self.mpr s.small_lt,
    filter_eq_nil.mpr (fun x hx => (s.above_ge x hx).not_gt),
    filter_eq_nil.mpr (fun _ hx => (eq_of_mem_replicate hx).symm.not_gt)]

private theorem Split.shift_ge {m : ℕ} {h : ℤ} (s : Split m h) {x : ℕ}
    (hx : x ∈ s.above.map (· + m)) : 2 * m ≤ x := by
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  have := s.above_ge y hy
  omega

private theorem Split.right_ge {m : ℕ} {h : ℤ} (s : Split m h) (hm : 1 ≤ m) :
    s.rightParts.filter (2 * m ≤ ·) = s.above.map (· + m) := by
  have hsmall : s.small.filter (2 * m ≤ ·) = 0 :=
    filter_eq_nil.mpr (fun x hx => by have := s.small_lt x hx; omega)
  simp [Split.rightParts, filter_add, filter_singleton, hsmall,
    filter_eq_self.mpr (fun _ hx => s.shift_ge hx), show ¬ 2 * m ≤ m by omega]

private theorem Split.right_lt {m : ℕ} {h : ℤ} (s : Split m h) :
    s.rightParts.filter (· < m) = s.small := by
  have hlarge : (s.above.map (· + m)).filter (· < m) = 0 :=
    filter_eq_nil.mpr (fun _ hx => by have := s.shift_ge hx; omega)
  simp [Split.rightParts, filter_add, filter_singleton, filter_eq_self.mpr s.small_lt, hlarge]

private theorem Split.left_pos {m : ℕ} {h : ℤ} (s : Split m h) (hm : 1 ≤ m) :
    ∀ x ∈ s.leftParts, 0 < x := by
  intro x hx
  rcases mem_add.mp hx with hx | hx
  · rcases mem_add.mp hx with ha | hr
    · exact hm.trans (s.above_ge x ha)
    · rw [eq_of_mem_replicate hr]
      exact hm
  · exact s.small_pos x hx

private theorem Split.right_pos {m : ℕ} {h : ℤ} (s : Split m h) (hm : 1 ≤ m) :
    ∀ x ∈ s.rightParts, 0 < x := by
  intro x hx
  rcases mem_add.mp hx with hx | hx
  · rcases mem_add.mp hx with hx | hx
    · have := s.shift_ge hx
      omega
    · rw [mem_singleton.mp hx]
      exact hm
  · exact s.small_pos x hx

private theorem Split.left_injective {m : ℕ} {h : ℤ} :
    Function.Injective (@Split.leftParts m h) := by
  intro s t e
  have hg := congrArg (Multiset.filter (m ≤ ·)) e
  rw [s.left_ge, t.left_ge] at hg
  have hc := congrArg Multiset.card hg
  simp only [card_add, card_replicate] at hc
  have hs := Int.toNat_of_nonneg (show 0 ≤ (s.above.card : ℤ) + h by have := s.height; omega)
  have ht := Int.toNat_of_nonneg (show 0 ≤ (t.above.card : ℤ) + h by have := t.height; omega)
  have he : s.above.card = t.above.card := by omega
  apply Split.ext
  · rw [he] at hg
    exact add_right_cancel hg
  · simpa only [s.left_lt, t.left_lt] using congrArg (Multiset.filter (· < m)) e

private theorem Split.right_injective {m : ℕ} {h : ℤ} (hm : 1 ≤ m) :
    Function.Injective (@Split.rightParts m h) := by
  intro s t e
  apply Split.ext
  · exact Multiset.map_injective (f := (· + m)) (fun _ _ e => Nat.add_right_cancel e)
      (by simpa only [s.right_ge hm, t.right_ge hm] using
        congrArg (Multiset.filter (2 * m ≤ ·)) e)
  · simpa only [s.right_lt, t.right_lt] using congrArg (Multiset.filter (· < m)) e

private theorem Split.sum_balance {m : ℕ} {h : ℤ} (s : Split m h) :
    (s.rightParts.sum : ℤ) = (s.leftParts.sum : ℤ) - (m : ℤ) * h := by
  have hshift : (s.above.map (· + m)).sum = s.above.sum + s.above.card * m := by
    simp [sum_map_add, map_id', map_const', sum_replicate]
  simp only [Split.rightParts, Split.leftParts, sum_add, sum_replicate, sum_singleton,
    nsmul_eq_mul, hshift]
  push_cast
  rw [Int.toNat_of_nonneg (show 0 ≤ (s.above.card : ℤ) + h by have := s.height; omega)]
  ring

private theorem left_iff {n m : ℕ} {h : ℤ} (hm : 1 ≤ m) (p : n.Partition) :
    ((Finset.Icc 1 n).filter (fun r =>
      IsFixedColumnHook p m r h ∧ partitionRowLen p r = m)).Nonempty ↔
        ∃ s : Split m h, s.leftParts = p.parts := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨_, ⟨hr, _, _, hhook⟩, hrow⟩ := Finset.mem_filter.mp hr
    have hl := (le_row_iff p hr hm).mp hrow.ge
    have hu : partitionColLen p (m + 1) < r := by
      by_contra! hu
      have := (le_row_iff p hr (show 1 ≤ m + 1 by omega)).mpr hu
      omega
    simp only [partitionHookLength, hrow] at hhook
    -- The hook equation now reads `partitionColLen p m - 2*r + 1 = h`,
    -- so the column height and `h` uniquely determine `r`.
    let L := p.parts.filter (m ≤ ·)
    let C := p.parts.filter (· < m)
    -- The `b` rows below the hook in this column all have length `m`.
    let b := L.card - r
    have hL : L.card = partitionColLen p m := rfl
    have hparts : L + C = p.parts := by
      simpa only [not_le] using filter_add_not (m ≤ ·) p.parts
    have hgreater : L.filter (m + 1 ≤ ·) = p.parts.filter (m + 1 ≤ ·) := by
      rw [filter_filter]
      exact filter_congr fun _ _ => by omega
    have hequal : L.filter (fun x => ¬ m + 1 ≤ x) = replicate (L.count m) m := by
      rw [← filter_eq']
      exact filter_congr (fun _ hx => by have := of_mem_filter hx; omega)
    have hcount := congrArg Multiset.card (filter_add_not (m + 1 ≤ ·) L)
    rw [hgreater, hequal, card_add, card_replicate] at hcount
    change partitionColLen p (m + 1) + L.count m = L.card at hcount
    have hrep : replicate (b + 1) m ≤ L := le_count_iff_replicate_le.mp (by dsimp [b]; omega)
    let A := L - replicate (b + 1) m
    have hA : A.card = r - 1 := by
      change (L - replicate (b + 1) m).card = r - 1
      rw [card_sub hrep, card_replicate]
      omega
    have hb : (b : ℤ) = (A.card : ℤ) + h := by dsimp [b]; omega
    have hAge : ∀ x ∈ A, m ≤ x := by
      intro x hx
      have hxL := mem_of_le (Multiset.sub_le_self L (replicate (b + 1) m)) hx
      exact (mem_filter.mp hxL).2
    let s : Split m h := ⟨A, C, hAge, fun _ hx => (mem_filter.mp hx).2,
      fun _ hx => p.parts_pos (mem_of_mem_filter hx), by omega⟩
    refine ⟨s, ?_⟩
    change (L - replicate (b + 1) m) + replicate (((A.card : ℤ) + h).toNat + 1) m + C = p.parts
    rw [← hb, Int.toNat_natCast, Multiset.sub_add_cancel hrep, hparts]
  · rintro ⟨s, hs⟩
    let r := s.above.card + 1
    have hr : 1 ≤ r := by dsimp [r]; omega
    have hmcol : partitionColLen p m = r + ((s.above.card : ℤ) + h).toNat := by
      rw [partitionColLen, ← hs, s.left_ge, card_add, card_replicate]
      dsimp [r]; omega
    have hgt : partitionColLen p (m + 1) ≤ s.above.card := by
      have hrp : (replicate (((s.above.card : ℤ) + h).toNat + 1) m).filter (m + 1 ≤ ·) = 0 :=
        filter_eq_nil.mpr (fun _ hx => by have := eq_of_mem_replicate hx; omega)
      have hsmall : s.small.filter (m + 1 ≤ ·) = 0 :=
        filter_eq_nil.mpr (fun x hx => by have := s.small_lt x hx; omega)
      rw [partitionColLen, ← hs, Split.leftParts, filter_add, filter_add, hrp, hsmall,
        add_zero, add_zero]
      exact card_le_card (filter_le _ _)
    have hrow : partitionRowLen p r = m := by
      have hlo := (le_row_iff p hr hm).mpr (by omega)
      by_contra! hn
      have hhi := (le_row_iff p hr (show 1 ≤ m + 1 by omega)).mp (show m + 1 ≤ _ by omega)
      dsimp [r] at hhi
      omega
    have hcard : p.parts.card ≤ n := by
      simpa [p.parts_sum] using
        (card_nsmul_le_sum (s := p.parts) (a := 1) (fun _ hx => p.parts_pos hx))
    have hcolle : partitionColLen p m ≤ p.parts.card := card_le_card (filter_le _ _)
    refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr, by omega⟩, ?_⟩⟩
    refine ⟨⟨hr, hm, hrow.ge, ?_⟩, hrow⟩
    have hh := Int.toNat_of_nonneg (show 0 ≤ (s.above.card : ℤ) + h by have := s.height; omega)
    simp only [partitionHookLength, hrow]
    dsimp [r] at hmcol ⊢
    omega

private theorem right_iff {n m : ℕ} {h : ℤ} (hm : 1 ≤ m) (p : n.Partition) :
    p.parts.count m = 1 ∧ Disjoint (Finset.Icc (m + 1) (2 * m - 1)) p.parts.toFinset ∧
      -h ≤ ((p.parts.filter (2 * m ≤ ·)).card : ℤ) ↔
        ∃ s : Split m h, s.rightParts = p.parts := by
  constructor
  · rintro ⟨hc, hgap, hh⟩
    let B := p.parts.filter (2 * m ≤ ·)
    let C := p.parts.filter (· < m)
    -- Reverse the shift on the long parts; the short parts stay unchanged.
    let A := B.map (· - m)
    have hB : ∀ x ∈ B, 2 * m ≤ x := fun _ hx => of_mem_filter hx
    have hA : ∀ x ∈ A, m ≤ x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      have := hB y hy
      omega
    have hs : A.map (· + m) = B := by
      calc
        _ = B.map (fun x => x) := by
          rw [map_map]
          exact map_congr rfl (fun x hx => by have := hB x hx; dsimp; omega)
        _ = B := map_id' B
    have hparts : B + {m} + C = p.parts := by
      have he : p.parts.filter (· = m) = {m} := by rw [filter_eq', hc, replicate_one]
      rw [← he]
      ext x
      have hx : x ∈ p.parts → x < m ∨ x = m ∨ 2 * m ≤ x := by
        intro hx
        by_contra! hn
        exact Finset.disjoint_left.mp hgap (Finset.mem_Icc.mpr (by omega))
          (mem_toFinset.mpr hx)
      simp only [B, C, count_add, count_filter]
      by_cases hb : x ∈ p.parts
      · have := hx hb
        split_ifs <;> omega
      · simp [count_eq_zero.mpr hb]
    refine ⟨⟨A, C, hA, fun _ hx => (mem_filter.mp hx).2,
      fun _ hx => p.parts_pos (mem_of_mem_filter hx), by simpa [A, B] using hh⟩, ?_⟩
    change A.map (· + m) + {m} + C = p.parts
    rwa [hs]
  · rintro ⟨s, hs⟩
    rw [← hs]
    refine ⟨?_, ?_, by simpa only [s.right_ge hm, card_map] using s.height⟩
    · simp [Split.rightParts, count_add, count_eq_zero.mpr (fun hx => by
        have := s.shift_ge hx; omega : m ∉ s.above.map (· + m)),
        count_eq_zero.mpr (fun hx => (s.small_lt m hx).false : m ∉ s.small)]
    · apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hx
      rcases mem_add.mp (mem_toFinset.mp hx') with ht | ht
      · rcases mem_add.mp ht with ht | ht
        · have := s.shift_ge ht
          omega
        · have := mem_singleton.mp ht
          omega
      · have := s.small_lt x ht
        omega

end FixedColumnHookBijection

open FixedColumnHookBijection

/-- **Fixed hooks in column $m$ arising from parts of size $m$.** Let $n$ and $m \ge 1$ be
natural numbers and let $h$ be an integer.
For a partition $\lambda$, write $\lambda_r$ for its $r$-th largest part ($0$ if it has fewer
than $r$ parts), $\lambda'_m$ for the number of its parts that are at least $m$, and
$h_{r,m}(\lambda) = \lambda_r + \lambda'_m - r - m + 1$ for the hook length of the square $(r, m)$.
The partition $\lambda$ has an $h$-fixed hook in column $m$ at row $r$ when $r \ge 1$,
$m \le \lambda_r$ and $h_{r,m}(\lambda) = r + h$.
Count the partitions $\lambda$ of $n$ that have an $h$-fixed hook in column $m$ at some row
$r \le n$ with $\lambda_r = m$. If $n - mh \ge 0$, this number equals the number of partitions of
$n - mh$ in which $m$ occurs as a part exactly once, none of $m + 1, \dots, 2m - 1$ is a part,
and at least $-h$ parts, counted with multiplicity, are at least $2m$. If $n - mh < 0$, the
number is $0$.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 2 (`integers-2025-A28-thm-2`). -/
public theorem card_fixedColumnHook_part_eq_column (n m : ℕ) (h : ℤ) (hm : 1 ≤ m) :
    ((((Finset.univ : Finset n.Partition).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s =>
          IsFixedColumnHook p m s h ∧ partitionRowLen p s = m)).Nonempty)).card : ℕ) : ℤ) =
      if 0 ≤ (n : ℤ) - m * h then
        (((Finset.univ : Finset ((n : ℤ) - m * h).toNat.Partition).filter (fun p =>
          p.parts.count m = 1 ∧ Disjoint (Finset.Icc (m + 1) (2 * m - 1)) p.parts.toFinset ∧
            -h ≤ ((p.parts.filter (2 * m ≤ ·)).card : ℤ))).card : ℤ)
      else 0 := by
  split_ifs with hn
  · congr 1
    let k := ((n : ℤ) - m * h).toNat
    have hk : (k : ℤ) = n - m * h := Int.toNat_of_nonneg hn
    let S := (Finset.univ : Finset n.Partition).filter (fun p =>
      ((Finset.Icc 1 n).filter (fun r =>
        IsFixedColumnHook p m r h ∧ partitionRowLen p r = m)).Nonempty)
    let T := (Finset.univ : Finset k.Partition).filter (fun p =>
      p.parts.count m = 1 ∧ Disjoint (Finset.Icc (m + 1) (2 * m - 1)) p.parts.toFinset ∧
        -h ≤ ((p.parts.filter (2 * m ≤ ·)).card : ℤ))
    change S.card = T.card
    have left (p : n.Partition) (hp : p ∈ S) : ∃ s : Split m h, s.leftParts = p.parts :=
      (left_iff hm p).mp (Finset.mem_filter.mp hp).2
    have right (q : k.Partition) (hq : q ∈ T) : ∃ s : Split m h, s.rightParts = q.parts :=
      (right_iff hm q).mp (Finset.mem_filter.mp hq).2
    let f (p : n.Partition) (hp : p ∈ S) : k.Partition := by
      let s := (left p hp).choose
      refine ⟨s.rightParts, fun hx => s.right_pos hm _ hx, ?_⟩
      have hb := s.sum_balance
      rw [(left p hp).choose_spec, p.parts_sum, ← hk] at hb
      exact_mod_cast hb
    let g (q : k.Partition) (hq : q ∈ T) : n.Partition := by
      let s := (right q hq).choose
      refine ⟨s.leftParts, fun hx => s.left_pos hm _ hx, ?_⟩
      have hb := s.sum_balance
      rw [(right q hq).choose_spec, q.parts_sum, hk] at hb
      omega
    have hf (p : n.Partition) (hp : p ∈ S) : f p hp ∈ T :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (right_iff hm _).mpr ⟨(left p hp).choose, rfl⟩⟩
    have hg (q : k.Partition) (hq : q ∈ T) : g q hq ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (left_iff hm _).mpr ⟨(right q hq).choose, rfl⟩⟩
    apply Finset.card_bij' f g hf hg
    · intro p hp
      have e : (right (f p hp) (hf p hp)).choose = (left p hp).choose :=
        Split.right_injective hm (right (f p hp) (hf p hp)).choose_spec
      apply Nat.Partition.ext
      change (right (f p hp) (hf p hp)).choose.leftParts = p.parts
      rw [e, (left p hp).choose_spec]
    · intro q hq
      have e : (left (g q hq) (hg q hq)).choose = (right q hq).choose :=
        Split.left_injective (left (g q hq) (hg q hq)).choose_spec
      apply Nat.Partition.ext
      change (left (g q hq) (hg q hq)).choose.rightParts = q.parts
      rw [e, (right q hq).choose_spec]
  · rw [show ((Finset.univ : Finset n.Partition).filter (fun p =>
        ((Finset.Icc 1 n).filter (fun s => IsFixedColumnHook p m s h ∧
          partitionRowLen p s = m)).Nonempty)) = ∅ by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨s, hs⟩ := (left_iff hm p).mp (Finset.mem_filter.mp hp).2
        have he := s.sum_balance
        rw [hs, p.parts_sum] at he
        omega]
    simp

end MetaMathlibExt
