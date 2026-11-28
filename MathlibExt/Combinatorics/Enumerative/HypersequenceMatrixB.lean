/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.HypersequenceElementarySymmetric
import MathlibExt.Combinatorics.Enumerative.StirlingAscPochhammer

/-!
# Parisse's hypersequence matrix B

The entries of `hyperseqB` are signed elementary symmetric functions, or equivalently signed
coefficients of a product of linear factors, for every integer parameter. At zero,
`hyperseqB_zero_recurrence_stirling` gives their recurrence and two closed forms in
unsigned Stirling numbers of the first kind. For nonnegative parameters,
`hyperseqB_recurrence_closed_form_row_sums` transfers the elementary symmetric formulas to the
matrix entries by reversing degrees and accounting for the signs.

## References

* Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums II*,
  INTEGERS 26 (2026), Article A36, pp. 1–15, Section 2, Equations (2.4) and (2.5), and
  Section 3, Propositions 1 and 2.
-/

namespace MetaMathlibExt

/-- **Parisse's matrix $B(n)$.** For an integer $n$ and $j, k \in \mathbb{N}$, let $e_{j,i}(n)$ be
the elementary symmetric polynomial of degree $i$ in $n + 1, \dots, n + j$. The entry
$b_{j,k}(n)$ of $B(n)$ is $(-1)^k e_{j,j-k}(n)$ for $k \le j$ and $0$ for $k > j$; it is an
integer.

The source also uses this for $n \in \mathbb{Z}$ (Proposition 3, after Remark 1), which is why
$n$ ranges over the integers.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 2, Equation (2.5). -/
@[expose] public def hyperseqB (n : ℤ) (j k : ℕ) : ℤ :=
  if k ≤ j then (-1) ^ k * ((Finset.Icc 1 j).val.map fun i : ℕ => n + i).esymm (j - k) else 0

open Finset Polynomial in
/-- **Parisse's matrix entries as polynomial coefficients.** For any integer `n` and natural
indices `j, k`, the entry `hyperseqB n j k` is `(-1)^k` times the coefficient of degree `k` in
$\prod_{i=1}^j (X + n + i)$. Above the diagonal, the polynomial has no coefficient of that degree.
This is the coefficient form of Equations (2.4) and (2.5) of Parisse's paper. -/
public theorem hyperseqB_eq_neg_one_pow_mul_coeff (n : ℤ) (j k : ℕ) :
    hyperseqB n j k = (-1) ^ k * (∏ i ∈ Icc 1 j, (X + C (n + (i : ℤ)))).coeff k := by
  by_cases hk : k ≤ j
  · rw [hyperseqB, ite_eq_left hk]
    congr 1
    have h := Multiset.prod_X_add_C_coeff' (Icc 1 j).val (fun i : ℕ => n + (i : ℤ))
      (k := k) (by simpa using hk)
    simpa [prod_map_val] using h.symm
  · have hdeg : (∏ i ∈ Icc 1 j, (X + C (n + (i : ℤ)))).natDegree = j := by
      simpa [sub_eq_add_neg] using
        natDegree_finsetProd_X_sub_C_eq_card (Icc 1 j) (fun i : ℕ => -(n + (i : ℤ)))
    have hlt : (∏ i ∈ Icc 1 j, (X + C (n + (i : ℤ)))).natDegree < k :=
      hdeg.trans_lt (Nat.lt_of_not_ge hk)
    rw [hyperseqB, ite_eq_right hk, coeff_eq_zero_of_natDegree_lt hlt, mul_zero]

/-- **Row one of Parisse's matrix $B(n)$.** For every integer $n$, the entries $b_{j,k}(n)$ of
$B(n)$ satisfy $b_{1,0}(n) = n + 1$ and $b_{1,1}(n) = -1$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 2, display of `B(n)`. -/
public theorem hyperseqB_one (n : ℤ) : hyperseqB n 1 0 = n + 1 ∧ hyperseqB n 1 1 = -1 := by
  simp [hyperseqB, Multiset.esymm, Multiset.powersetCard_one]

/-- **Row three of Parisse's matrix $B(1)$.** The entries $b_{3,0}(1), b_{3,1}(1), b_{3,2}(1),
b_{3,3}(1)$ of $B(1)$ are $24, -26, 9, -1$.

This matches the source's display of row three of $B(n)$,
$(n + 1)(n + 2)(n + 3), -(3n^2 + 12n + 11), 3n + 6, -1$, at $n = 1$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 2, display of `B(n)`. -/
public theorem hyperseqB_row_three :
    (List.range 4).map (hyperseqB 1 3) = [24, -26, 9, -1] := by
  decide +kernel

namespace hyperseqB_zero_recurrence_stirling

open Finset Polynomial

/-- The rising factorial at `X + 1` has linear factors indexed by `1, …, j`. -/
private theorem prod_X_add_C_eq_shifted_ascPochhammer (j : ℕ) :
    ∏ i ∈ Icc 1 j, (X + C (i : ℤ)) = (ascPochhammer ℤ j).comp (X + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_Icc_succ_top (by omega), ih, ascPochhammer_succ_right]
    simp [mul_comp, add_comp, add_assoc, add_comm (1 : ℤ[X])]

/-- Read the same coefficient before and after the shift in the rising factorial. -/
private theorem closed_forms (j k : ℕ) :
    hyperseqB 0 j k = (-1) ^ k * ∑ ℓ ∈ Icc k j, (ℓ.choose k * Nat.stirlingFirst j ℓ : ℤ) ∧
      hyperseqB 0 j k = (-1) ^ k * Nat.stirlingFirst (j + 1) (k + 1) := by
  by_cases hk : k ≤ j
  · rw [hyperseqB_eq_neg_one_pow_mul_coeff]
    simp only [zero_add, prod_X_add_C_eq_shifted_ascPochhammer]
    constructor <;> congr 1
    · rw [← Nat.sum_stirlingFirst_mul_X_pow]
      simp only [Polynomial.sum_comp, mul_comp, natCast_comp, pow_comp, X_comp, finsetSum_coeff,
        coeff_natCast_mul, coeff_X_add_one_pow]
      simp_rw [mul_comm (Nat.stirlingFirst j _ : ℤ)]
      symm
      apply sum_subset fun i hi => mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hi).2)
      intro i hi hki
      have hij := Nat.le_of_lt_succ (mem_range.mp hi)
      have hik : i < k := lt_of_not_ge fun h => hki (mem_Icc.mpr ⟨h, hij⟩)
      simp [Nat.choose_eq_zero_of_lt hik]
    · rw [← coeff_X_mul, ← ascPochhammer_succ_left, ← Nat.sum_stirlingFirst_mul_X_pow]
      simp [coeff_X_pow, mul_ite, hk]
  · simp [hyperseqB, hk, Icc_eq_empty_of_lt (Nat.lt_of_not_ge hk),
      Nat.stirlingFirst_eq_zero_of_lt (show j + 1 < k + 1 by omega)]

end hyperseqB_zero_recurrence_stirling

open hyperseqB_zero_recurrence_stirling in
/-- **Parisse's $b_{j,k}(0)$ and Stirling numbers of the first kind.** Let $b_{j,k}(0)$ be the
entries of Parisse's matrix $B(0)$ and write $[j, \ell]$ for the unsigned Stirling numbers of the
first kind. Then $b_{0,k}(0) = \delta_{0,k}$ for all $k$; for all $j, k \in \mathbb{N}$,
$b_{j+1,0}(0) = (j + 1) \, b_{j,0}(0)$ and $b_{j+1,k+1}(0) = (j + 1) \, b_{j,k+1}(0) - b_{j,k}(0)$;
and for all $j, k \in \mathbb{N}$,
$b_{j,k}(0) = (-1)^k \sum_{\ell=k}^{j} \binom{\ell}{k} [j, \ell] = (-1)^k [j + 1, k + 1]$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Corollary 4 (`integers-2026-A36-cor-4`). -/
public theorem hyperseqB_zero_recurrence_stirling :
    (∀ k : ℕ, hyperseqB 0 0 k = if k = 0 then 1 else 0) ∧
    (∀ j : ℕ, hyperseqB 0 (j + 1) 0 = (j + 1) * hyperseqB 0 j 0) ∧
    (∀ j k : ℕ, hyperseqB 0 (j + 1) (k + 1) = (j + 1) * hyperseqB 0 j (k + 1) - hyperseqB 0 j k) ∧
    ∀ j k : ℕ,
      hyperseqB 0 j k = (-1) ^ k * ∑ ℓ ∈ Finset.Icc k j, (ℓ.choose k * Nat.stirlingFirst j ℓ : ℤ) ∧
        hyperseqB 0 j k = (-1) ^ k * Nat.stirlingFirst (j + 1) (k + 1) := by
  have entry (j k : ℕ) := (closed_forms j k).2
  refine ⟨?_, ?_, ?_, closed_forms⟩
  · intro k
    cases k <;> simp [hyperseqB]
  · intro j
    simp [entry, Nat.stirlingFirst_one_right, Nat.factorial_succ]
  · intro j k
    rw [entry, entry, entry, Nat.stirlingFirst_succ_succ (j + 1) (k + 1), pow_succ]
    push_cast
    ring

section

open Finset

private abbrev rowEsymm (n j k : ℕ) : ℕ := ((Icc 1 j).val.map (n + ·)).esymm k

/-- In the lower triangle, an entry is a signed complementary-degree coefficient over `ℕ`,
cast to `ℤ`. -/
private theorem hyperseqB_eq_signed_esymm (n j k : ℕ) (hk : k ≤ j) :
    hyperseqB n j k = (-1) ^ k * (rowEsymm n j (j - k) : ℤ) := by
  simp only [hyperseqB, ite_eq_left hk, rowEsymm, Multiset.esymm, Multiset.powersetCard_map,
    Function.comp_def, Multiset.map_map, Nat.cast_multiset_sum, Nat.cast_multiset_prod,
    Nat.cast_add]

/-- **Recurrence, closed form and row sums of Parisse's $b_{j,k}(n)$.** Let $n \in \mathbb{N}$ and
let $b_{j,k}(n)$ be the entries of Parisse's matrix $B(n)$. Write $[j, \ell]$ for the unsigned
Stirling numbers of the first kind and $x^{\overline{j}} = x (x + 1) \cdots (x + j - 1)$ for the
rising factorial. Then $b_{0,k}(n) = \delta_{0,k}$ for all $k$; for all $j, k \in \mathbb{N}$,
$b_{j+1,0}(n) = (n + j + 1) \, b_{j,0}(n)$ and
$b_{j+1,k+1}(n) = (n + j + 1) \, b_{j,k+1}(n) - b_{j,k}(n)$;
$b_{j,k}(n) = (-1)^k \sum_{\ell=k}^{j} \binom{\ell}{k} [j, \ell] \, (n + 1)^{\ell-k}$ for all
$j, k$ (an empty sum for $k > j$); and for all $j$,
$\sum_{k=0}^{j} b_{j,k}(n) = n^{\overline{j}}$ and
$\sum_{k=0}^{j} (-1)^k b_{j,k}(n) = (n + 2)^{\overline{j}}$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Proposition 2 (`integers-2026-A36-prop-2`). -/
public theorem hyperseqB_recurrence_closed_form_row_sums (n : ℕ) :
    (∀ k : ℕ, hyperseqB n 0 k = if k = 0 then 1 else 0) ∧
    (∀ j : ℕ, hyperseqB n (j + 1) 0 = (n + (j + 1)) * hyperseqB n j 0) ∧
    (∀ j k : ℕ, hyperseqB n (j + 1) (k + 1) =
      (n + (j + 1)) * hyperseqB n j (k + 1) - hyperseqB n j k) ∧
    (∀ j k : ℕ, hyperseqB n j k = (-1) ^ k * ∑ ℓ ∈ Finset.Icc k j,
      (ℓ.choose k * Nat.stirlingFirst j ℓ : ℤ) * ((n : ℤ) + 1) ^ (ℓ - k)) ∧
    (∀ j : ℕ, ∑ k ∈ Finset.range (j + 1), hyperseqB n j k = (n.ascFactorial j : ℤ)) ∧
    ∀ j : ℕ, ∑ k ∈ Finset.range (j + 1), (-1) ^ k * hyperseqB n j k =
      ((n + 2).ascFactorial j : ℤ) := by
  obtain ⟨_, hstep, hclosed, hplain, halt⟩ := hyperseq_esymm_recurrence_closed_form_row_sums n
  have step (j d : ℕ) : (rowEsymm n (j + 1) (d + 1) : ℤ) =
      (rowEsymm n j (d + 1) : ℤ) + (n + (j + 1)) * (rowEsymm n j d : ℤ) := by
    exact_mod_cast hstep j d
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    cases k <;> simp [hyperseqB]
  · intro j
    have hzero : rowEsymm n j (j + 1) = 0 :=
      Multiset.esymm_of_card_lt (by simp)
    simp only [hyperseqB_eq_signed_esymm n _ 0 (Nat.zero_le _), Nat.sub_zero, pow_zero, one_mul]
    rw [step, hzero, Nat.cast_zero, zero_add]
  · intro j k
    rcases lt_trichotomy k j with hk | rfl | hk
    · obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (show j - k ≠ 0 by omega)
      rw [hyperseqB_eq_signed_esymm n (j + 1) (k + 1) (by omega),
        hyperseqB_eq_signed_esymm n j (k + 1) (by omega),
        hyperseqB_eq_signed_esymm n j k hk.le,
        show j + 1 - (k + 1) = d + 1 by omega, show j - (k + 1) = d by omega,
        hd, step, pow_succ]
      ring
    · simp [hyperseqB, pow_succ]
    · simp [hyperseqB, hk.not_ge, show ¬ k + 1 ≤ j by omega,
        show ¬ k + 1 ≤ j + 1 by omega]
  · intro j k
    by_cases hk : k ≤ j
    · have hinterval : Icc k j = Ico k (j + 1) := by
        ext ℓ
        simp only [mem_Icc, mem_Ico]
        omega
      -- Shift the Stirling index by `k` and use the complementary binomial coefficient.
      rw [hyperseqB_eq_signed_esymm n j k hk, rowEsymm, hclosed j (j - k) (Nat.sub_le _ _),
        Nat.sub_sub_self hk, hinterval, sum_Ico_eq_sum_range, show j + 1 - k = j - k + 1 by omega]
      push_cast
      congr 1
      refine sum_congr rfl fun ℓ _ => ?_
      rw [Nat.add_sub_cancel_left, Nat.choose_symm_add]
    · simp [hyperseqB, hk, Icc_eq_empty_of_lt (Nat.lt_of_not_ge hk)]
  · intro j
    rw [← sum_range_reflect (hyperseqB n j) (j + 1)]
    calc
      _ = ∑ k ∈ range (j + 1), (-1 : ℤ) ^ j * ((-1) ^ k * (rowEsymm n j k : ℤ)) := by
        refine sum_congr rfl fun k hk => ?_
        have hkj : k ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hk)
        rw [Nat.add_sub_cancel, hyperseqB_eq_signed_esymm n j _ (Nat.sub_le _ _),
          Nat.sub_sub_self hkj, ← mul_assoc, ← pow_add,
          show j + k = j - k + 2 * k by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
      _ = _ := by
        rw [← mul_sum, halt, ← mul_assoc, ← mul_pow]
        simp
  · intro j
    calc
      _ = ∑ k ∈ range (j + 1), (rowEsymm n j (j - k) : ℤ) := by
        refine sum_congr rfl fun k hk => ?_
        rw [hyperseqB_eq_signed_esymm n j k (Nat.lt_succ_iff.mp (mem_range.mp hk)),
          ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
      _ = ∑ k ∈ range (j + 1), (rowEsymm n j k : ℤ) := by
        simpa using sum_range_reflect (fun k => (rowEsymm n j k : ℤ)) (j + 1)
      _ = _ := by exact_mod_cast hplain j

end

end MetaMathlibExt
