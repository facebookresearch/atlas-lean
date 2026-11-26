/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import MathlibExt.Combinatorics.Enumerative.Hypersequence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.StirlingAscPochhammer

/-! # Hypersequences through elementary symmetric polynomials

Iterating partial sums `j + 1` times weights `a_i` by the binomial coefficient
`binom(n - i + j, j)`, and `j!` times this coefficient is the product
`(n - i + 1) ⋯ (n - i + j)`. Vieta's formula expands that product in the elementary symmetric
polynomials of `n + 1, …, n + j`. The first result, `factorial_mul_hypersequence_eq_sum_esymm`,
expresses `j! a^{(j+1)}_n` through the weighted sums `t_k(n) = ∑_{i=0}^{n} i^k a_i`, in two
forms that differ by reversing the summation index.

The second result, `hyperseq_esymm_recurrence_closed_form_row_sums`, describes the elementary
symmetric polynomial `e_{j,k}(n)` of degree `k` in `n + 1, …, n + j`. Adding the variable
`n + j + 1` gives a Pascal-type recurrence. The product `(X + n + 1) ⋯ (X + n + j)` is the rising
factorial at `X + n + 1`; expanding it in unsigned Stirling numbers of the first kind and then by
the binomial theorem gives `e_{j,k}(n)` in closed form. Evaluating `∏ (X + r)` and `∏ (X - r)`,
over the variables `r`, at `X = 1` gives the plain and alternating row sums as rising factorials.
-/

namespace MetaMathlibExt

open Finset

namespace factorial_mul_hypersequence_eq_sum_esymm

/-- Iterated partial sums are binomially weighted sums of the sequence. -/
private theorem hypersequence_succ_eq_sum (a : ℕ → ℂ) (r n : ℕ) :
    hypersequence a (r + 1) n = ∑ i ∈ range (n + 1), ((n - i + r).choose r : ℂ) * a i := by
  induction r generalizing n with
  | zero => simp [hypersequence]
  | succ r ih =>
    rw [hypersequence_succ]
    simp_rw [ih]
    rw [sum_comm' (t' := range (n + 1)) (s' := fun i => Ico i (n + 1))
      (fun k i => by simp only [mem_range, mem_Ico]; omega)]
    refine sum_congr rfl fun i hi => ?_
    have hi : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [← sum_mul, ← Nat.cast_sum, sum_Ico_eq_sum_range, show n + 1 - i = n - i + 1 by omega]
    simp only [Nat.add_sub_cancel_left]
    rw [Nat.sum_range_add_choose, Nat.add_assoc]

/-- `j!` times a binomial coefficient is a rising factorial. -/
private theorem factorial_mul_choose_eq_prod (j m : ℕ) :
    (j.factorial : ℂ) * ((m + j).choose j : ℂ) = ∏ x ∈ Icc 1 j, ((m : ℂ) + x) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_Icc_succ_top (by omega), ← ih, ← Nat.cast_mul, ← Nat.cast_mul,
      ← Nat.ascFactorial_eq_factorial_mul_choose, ← Nat.ascFactorial_eq_factorial_mul_choose,
      Nat.ascFactorial_succ]
    push_cast
    ring

/-- Vieta's formula evaluated at a point. -/
private theorem prod_add_eq_sum_esymm {R : Type*} [CommSemiring R] (s : Multiset R) (x : R) :
    (s.map fun r => x + r).prod =
      ∑ k ∈ range (Multiset.card s + 1), s.esymm k * x ^ (Multiset.card s - k) := by
  have h := congrArg (Polynomial.eval x) (Multiset.prod_X_add_C_eq_sum_esymm s)
  simpa only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_pow] using h

/-- Elementary symmetric polynomials commute with the cast from `ℕ` to a commutative semiring. -/
private theorem cast_esymm {R : Type*} [CommSemiring R] (s : Multiset ℕ) (k : ℕ) :
    ((s.esymm k : ℕ) : R) = (s.map (Nat.cast : ℕ → R)).esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def,
    Nat.cast_multiset_sum, Nat.cast_multiset_prod]

/-- The weight `j! binom(n - i + j, j)` expanded in the elementary symmetric polynomials of
`n + 1, …, n + j`. -/
private theorem factorial_mul_choose_eq_sum_esymm (j n i : ℕ) (hi : i ≤ n) :
    (j.factorial : ℂ) * ((n - i + j).choose j : ℂ) =
      ∑ k ∈ range (j + 1),
        (((Icc 1 j).val.map (n + ·)).esymm k : ℕ) * (-(i : ℂ)) ^ (j - k) := by
  have hcard : Multiset.card (((Icc 1 j).val.map (n + ·)).map (Nat.cast : ℕ → ℂ)) = j := by
    simp
  have h := prod_add_eq_sum_esymm (((Icc 1 j).val.map (n + ·)).map (Nat.cast : ℕ → ℂ))
    (-(i : ℂ))
  rw [hcard] at h
  simp_rw [cast_esymm]
  rw [← h, factorial_mul_choose_eq_prod, Multiset.map_map, Multiset.map_map, prod_map_val]
  refine prod_congr rfl fun x _ => ?_
  simp only [Function.comp_apply]
  push_cast [hi]
  ring

end factorial_mul_hypersequence_eq_sum_esymm

open factorial_mul_hypersequence_eq_sum_esymm in
/-- **Hypersequences through elementary symmetric polynomials.** Let $a$ be a sequence of complex
numbers and let $j, n \in \mathbb{N}$. Write $a^{(r)}_n$ for the hypersequence of generation $r$
of $a$, write $e_{j,k}(n)$ for the elementary symmetric polynomial of degree $k$ in
$n + 1, \dots, n + j$, and put $t_i(n) = \sum_{k=0}^{n} k^i a_k$, with $0^0 = 1$. Then
$j! \, a^{(j+1)}_n = (-1)^j \sum_{k=0}^{j} (-1)^k e_{j,k}(n) \, t_{j-k}(n)$ and
$j! \, a^{(j+1)}_n = \sum_{k=0}^{j} (-1)^k e_{j,j-k}(n) \, t_k(n)$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Theorem 1, Equation (2.1) (`integers-2026-A36-thm-1`). -/
public theorem factorial_mul_hypersequence_eq_sum_esymm (a : ℕ → ℂ) (j n : ℕ) :
    (j.factorial : ℂ) * hypersequence a (j + 1) n =
        (-1) ^ j * ∑ k ∈ Finset.range (j + 1), (-1) ^ k *
          (((Finset.Icc 1 j).val.map (n + ·)).esymm k : ℕ) *
            ∑ i ∈ Finset.range (n + 1), (i : ℂ) ^ (j - k) * a i ∧
      (j.factorial : ℂ) * hypersequence a (j + 1) n =
        ∑ k ∈ Finset.range (j + 1), (-1) ^ k *
          (((Finset.Icc 1 j).val.map (n + ·)).esymm (j - k) : ℕ) *
            ∑ i ∈ Finset.range (n + 1), (i : ℂ) ^ k * a i := by
  -- Both forms are reindexings of the expansion with signs `(-1) ^ (j - k)`.
  have key : (j.factorial : ℂ) * hypersequence a (j + 1) n =
      ∑ k ∈ range (j + 1), (-1) ^ (j - k) * (((Icc 1 j).val.map (n + ·)).esymm k : ℕ) *
        ∑ i ∈ range (n + 1), (i : ℂ) ^ (j - k) * a i := by
    rw [hypersequence_succ_eq_sum, mul_sum]
    trans ∑ i ∈ range (n + 1), ∑ k ∈ range (j + 1),
      (-1) ^ (j - k) * (((Icc 1 j).val.map (n + ·)).esymm k : ℕ) * ((i : ℂ) ^ (j - k) * a i)
    · refine sum_congr rfl fun i hi => ?_
      rw [← mul_assoc, factorial_mul_choose_eq_sum_esymm j n i
        (Nat.lt_succ_iff.mp (mem_range.mp hi)), sum_mul]
      refine sum_congr rfl fun k _ => ?_
      rw [neg_pow]
      ring
    · rw [sum_comm]
      exact sum_congr rfl fun k _ => (mul_sum _ _ _).symm
  refine ⟨?_, ?_⟩
  · rw [key, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk : k ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hsign : (-1 : ℂ) ^ (j - k) = (-1) ^ j * (-1) ^ k := by
      rw [← pow_add, show j + k = j - k + 2 * k by omega, pow_add, pow_mul, neg_one_sq,
        one_pow, mul_one]
    rw [hsign]
    ring
  · have hrefl := sum_range_reflect (fun k => (-1 : ℂ) ^ k *
      (((Icc 1 j).val.map (n + ·)).esymm (j - k) : ℕ) *
        ∑ i ∈ range (n + 1), (i : ℂ) ^ k * a i) (j + 1)
    rw [key, ← hrefl]
    refine sum_congr rfl fun k hk => ?_
    have hk : k ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [show j + 1 - 1 - k = j - k by omega, show j - (j - k) = k by omega]

namespace hyperseq_esymm_recurrence_closed_form_row_sums

open Polynomial factorial_mul_hypersequence_eq_sum_esymm

/-- Adding `a` to a multiset adds `a` times the elementary symmetric polynomial of one degree
less. -/
private theorem esymm_cons {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

/-- The interval `[1, j + 1]` is the interval `[1, j]` together with `j + 1`. -/
private theorem Icc_one_succ_val (j : ℕ) : (Icc 1 (j + 1)).val = (j + 1) ::ₘ (Icc 1 j).val := by
  have h : Icc 1 (j + 1) = insert (j + 1) (Icc 1 j) := by
    ext x
    simp only [mem_Icc, mem_insert]
    omega
  rw [h, insert_val_of_notMem (by simp)]

/-- The product of the `X + n + i` for `1 ≤ i ≤ j` is the rising factorial at `X + n + 1`,
expanded in unsigned Stirling numbers of the first kind. -/
private theorem prod_X_add_C_eq_sum_stirlingFirst (n j : ℕ) :
    ∏ i ∈ Icc 1 j, (X + C (n + i) : ℕ[X]) =
      ∑ m ∈ range (j + 1), (Nat.stirlingFirst j m : ℕ[X]) * (X + C (n + 1)) ^ m := by
  rw [Nat.sum_stirlingFirst_mul_pow]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_Icc_succ_top (by omega), ih, ascPochhammer_succ_eval, ← C_eq_natCast, add_assoc,
      ← C_add]
    congr 3
    rw [Nat.cast_id]
    omega

/-- Vieta's formula: `e_{j,k}(n)` is the coefficient of `X ^ (j - k)` in the product of the
`X + n + i` for `1 ≤ i ≤ j`. -/
private theorem esymm_eq_coeff (n j k : ℕ) (hk : k ≤ j) :
    ((Icc 1 j).val.map (n + ·)).esymm k =
      (∏ i ∈ Icc 1 j, (X + C (n + i) : ℕ[X])).coeff (j - k) := by
  have h := Multiset.prod_X_add_C_coeff ((Icc 1 j).val.map (n + ·)) (k := j - k) (by simp)
  rw [Multiset.card_map, card_val, Nat.card_Icc, Nat.add_sub_cancel, Nat.sub_sub_self hk,
    Multiset.map_map] at h
  rw [← h, ← prod_map_val]
  rfl

/-- The Stirling number is the same Vieta coefficient after inserting the factor `X`. -/
private theorem esymm_eq_stirlingFirst (j k : ℕ) (hk : k ≤ j) :
    (Icc 1 j).val.esymm k = Nat.stirlingFirst (j + 1) (j + 1 - k) := by
  have hprod (m : ℕ) :
      X * (∏ i ∈ Icc 1 m, (X + C i : ℕ[X])) = ascPochhammer ℕ (m + 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [prod_Icc_succ_top (by omega), ← mul_assoc, ih]
      simpa only [← C_eq_natCast, Nat.cast_id] using (ascPochhammer_succ_right ℕ (m + 1)).symm
  have hvieta := esymm_eq_coeff 0 j k hk
  simp only [Nat.zero_add, Multiset.map_id'] at hvieta
  have hindex : j + 1 - k = (j - k) + 1 := by omega
  have hle : j + 1 - k ≤ j + 1 := Nat.sub_le _ _
  rw [hvieta, ← coeff_X_mul, ← hindex, hprod, ← Nat.sum_stirlingFirst_mul_X_pow, finsetSum_coeff]
  simp [coeff_X_pow, mul_ite, hle]

/-- The closed form of `e_{j,k}(n)` through unsigned Stirling numbers of the first kind. -/
private theorem esymm_eq_sum (n j k : ℕ) (hk : k ≤ j) :
    ((Icc 1 j).val.map (n + ·)).esymm k =
      ∑ ℓ ∈ range (k + 1),
        (j - k + ℓ).choose ℓ * Nat.stirlingFirst j (j - k + ℓ) * (n + 1) ^ ℓ := by
  rw [esymm_eq_coeff n j k hk, prod_X_add_C_eq_sum_stirlingFirst, finsetSum_coeff]
  simp_rw [← C_eq_natCast, coeff_C_mul, coeff_X_add_C_pow, Nat.cast_id]
  rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le (j - k)) (by omega : j - k ≤ j + 1),
    sum_eq_zero fun m hm => by simp [Nat.choose_eq_zero_of_lt (mem_Ico.mp hm).2], zero_add,
    sum_Ico_eq_sum_range, show j + 1 - (j - k) = k + 1 by omega]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [Nat.add_sub_cancel_left, Nat.choose_symm_add]
  ring

/-- The product of the `1 + (n + i)` for `1 ≤ i ≤ j` is the rising factorial `(n + 2)^{(j)}`. -/
private theorem prod_one_add (n j : ℕ) :
    ∏ i ∈ Icc 1 j, (1 + (n + i)) = (n + 2).ascFactorial j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_Icc_succ_top (by omega), ih, Nat.ascFactorial_succ]
    ring

/-- The product of the `1 - (n + i)` for `1 ≤ i ≤ j` is `(-1)^j n^{(j)}`. -/
private theorem prod_one_sub (n j : ℕ) :
    ∏ i ∈ Icc 1 j, (1 - ((n + i : ℕ) : ℤ)) = (-1) ^ j * (n.ascFactorial j : ℕ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_Icc_succ_top (by omega), ih, Nat.ascFactorial_succ]
    push_cast
    ring

/-- The row sums of `e_{j,k}(n)`: Vieta's formula at the point `1`. -/
private theorem sum_esymm (n j : ℕ) :
    ∑ k ∈ range (j + 1), ((Icc 1 j).val.map (n + ·)).esymm k = (n + 2).ascFactorial j := by
  have h := prod_add_eq_sum_esymm ((Icc 1 j).val.map (n + ·)) 1
  simp only [Multiset.map_map, Function.comp_def, prod_map_val, one_pow, mul_one,
    Multiset.card_map, card_val, Nat.card_Icc, Nat.add_sub_cancel] at h
  rw [← h, prod_one_add]

/-- The alternating row sums of `e_{j,k}(n)`: Vieta's formula for `∏ (X - r)` at `X = 1`. -/
private theorem sum_neg_one_pow_mul_esymm (n j : ℕ) :
    ∑ k ∈ range (j + 1), (-1 : ℤ) ^ k * (((Icc 1 j).val.map (n + ·)).esymm k : ℕ) =
      (-1 : ℤ) ^ j * (n.ascFactorial j : ℕ) := by
  have h := congrArg (eval 1) (Multiset.prod_X_sub_X_eq_sum_esymm
    (((Icc 1 j).val.map (n + ·)).map (Nat.cast : ℕ → ℤ)))
  rw [Multiset.card_map, Multiset.card_map, card_val, Nat.card_Icc, Nat.add_sub_cancel] at h
  simp only [Multiset.map_map, Function.comp_def, prod_map_val, eval_prod, eval_sub, eval_X,
    eval_C, eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one, one_pow, mul_one] at h
  simp only [cast_esymm, Multiset.map_map, Function.comp_def]
  rw [← h, prod_one_sub]

end hyperseq_esymm_recurrence_closed_form_row_sums

open hyperseq_esymm_recurrence_closed_form_row_sums in
/-- **Recurrence, closed form and row sums of $e_{j,k}(n)$.** Let $n \in \mathbb{N}$ and let
$e_{j,k}(n)$ be the elementary symmetric polynomial of degree $k$ in $n + 1, \dots, n + j$.
Write $[j, \ell]$ for the unsigned Stirling numbers of the first kind and
$x^{\overline{j}} = x (x + 1) \cdots (x + j - 1)$ for the rising factorial. Then
$e_{0,k}(n) = \delta_{0,k}$ for all $k$;
$e_{j+1,k+1}(n) = e_{j,k+1}(n) + (n + j + 1) \, e_{j,k}(n)$ for all $j, k \in \mathbb{N}$;
$e_{j,k}(n) = \sum_{\ell=0}^{k} \binom{j-k+\ell}{\ell} [j, j-k+\ell] \, (n + 1)^\ell$ for all
$k \le j$; and for all $j$, $\sum_{k=0}^{j} e_{j,k}(n) = (n + 2)^{\overline{j}}$ and
$\sum_{k=0}^{j} (-1)^k e_{j,k}(n) = (-1)^j n^{\overline{j}}$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36, Proposition 1 (`integers-2026-A36-prop-1`). -/
public theorem hyperseq_esymm_recurrence_closed_form_row_sums (n : ℕ) :
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
      (-1 : ℤ) ^ j * (n.ascFactorial j : ℕ) := by
  refine ⟨fun k => ?_, fun j k => ?_, esymm_eq_sum n, sum_esymm n, sum_neg_one_pow_mul_esymm n⟩
  · rcases k with _ | k
    · simp
    · rw [Multiset.esymm_of_card_lt (by simp)]
      simp
  · rw [Icc_one_succ_val, Multiset.map_cons, esymm_cons]

open hyperseq_esymm_recurrence_closed_form_row_sums in
/-- **Elementary symmetric functions of the first integers via Stirling numbers.** For
$j, k \in \mathbb{N}$ let $e_{j,k}$ be the elementary symmetric polynomial of degree $k$ evaluated
at $1, 2, \dots, j$ (the source's $e_{j,k}(0)$), and let $c(j, i)$ be the unsigned Stirling number
of the first kind. Then $e_{0,k} = 1$ if $k = 0$ and $e_{0,k} = 0$ otherwise; for all $j, k$,
$e_{j+1,k+1} = e_{j,k+1} + (j + 1)\, e_{j,k}$; and for all $k \le j$,
$$e_{j,k} = \sum_{\ell=0}^{k} \binom{j-k+\ell}{\ell}\, c(j, j-k+\ell) = c(j + 1, j + 1 - k).$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36, Corollary 3 (`integers-2026-A36-cor-3`). -/
public theorem hyperseq_esymm_zero_recurrence_stirling :
    (∀ k : ℕ, ((Finset.Icc 1 0).val).esymm k = if k = 0 then 1 else 0) ∧
    (∀ j k : ℕ, ((Finset.Icc 1 (j + 1)).val).esymm (k + 1) =
      ((Finset.Icc 1 j).val).esymm (k + 1) +
        (j + 1) * ((Finset.Icc 1 j).val).esymm k) ∧
    ∀ j k : ℕ, k ≤ j →
      ((Finset.Icc 1 j).val).esymm k =
          ∑ ℓ ∈ Finset.range (k + 1), (j - k + ℓ).choose ℓ * Nat.stirlingFirst j (j - k + ℓ) ∧
        ((Finset.Icc 1 j).val).esymm k = Nat.stirlingFirst (j + 1) (j + 1 - k) := by
  obtain ⟨hbase, hstep, hsum, _, _⟩ := hyperseq_esymm_recurrence_closed_form_row_sums 0
  simp only [Nat.zero_add, Multiset.map_id', one_pow, mul_one] at hbase hstep hsum
  exact ⟨hbase, hstep, fun j k hk => ⟨hsum j k hk, esymm_eq_stirlingFirst j k hk⟩⟩

end MetaMathlibExt
