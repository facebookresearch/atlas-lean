/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.StirlingAscPochhammer

/-!
# Parisse's hypersequence matrix B

The entries of `hyperseqB` are signed elementary symmetric functions. At zero,
`hyperseqB_zero_recurrence_stirling` gives their recurrence and two closed forms in
unsigned Stirling numbers of the first kind.
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
  · have hc := Multiset.prod_X_add_C_coeff' (Icc 1 j).val (fun i : ℕ => (i : ℤ))
        (k := k) (by simpa using hk)
    rw [prod_map_val, prod_X_add_C_eq_shifted_ascPochhammer] at hc
    have hB : hyperseqB 0 j k = (-1) ^ k * ((ascPochhammer ℤ j).comp (X + 1)).coeff k := by
      simp [hyperseqB, hk, hc]
    rw [hB]
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

end MetaMathlibExt
