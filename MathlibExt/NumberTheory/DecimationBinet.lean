/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Lagrange
public import MathlibExt.NumberTheory.GeneralConditionalSequence

/-!
# Binet formula for decimated linear recurrences

For a recurrence with distinct characteristic roots, `decimation_binet` expresses each
term as a sum of powers of those roots, using the initial values in its residue class.
-/

namespace MetaMathlibExt

open Polynomial Finset

namespace decimation_binet

variable {m r : ℕ} {A s : ℕ → ℂ}

private noncomputable abbrev characteristic (A : ℕ → ℂ) (m : ℕ) : ℂ[X] :=
  X ^ m - ∑ j ∈ range m, C (A j) * X ^ j

/-- The monic characteristic polynomial is the nodal polynomial of the given roots. -/
private theorem characteristic_eq_nodal {α : Fin m → ℂ} (hα : Function.Injective α)
    (hroot : ∀ t, (characteristic A m).eval (α t) = 0) :
    characteristic A m = Lagrange.nodal univ α := by
  have hdeg : (∑ j ∈ range m, C (A j) * X ^ j).degree < (m : WithBot ℕ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ C (A j) * X ^ j)]
    exact degree_sum_fin_lt _
  have hlt : (∑ j ∈ range m, C (A j) * X ^ j).degree < (X ^ m : ℂ[X]).degree := by
    simpa using hdeg
  apply eq_of_degree_le_of_eval_index_eq univ hα.injOn
  · simp [characteristic, degree_sub_eq_left_of_degree_lt hlt]
  · simp [characteristic, degree_sub_eq_left_of_degree_lt hlt]
  · exact (monic_X_pow_sub hdeg).trans Lagrange.nodal_monic.symm
  · intro t ht
    rw [hroot, Lagrange.eval_nodal_at_node ht]

/-- Lagrange interpolation extracts the coefficient of degree `m - 1` in a monomial. -/
private theorem moment {α : Fin m → ℂ} (hα : Function.Injective α)
    (hroot : ∀ t, (characteristic A m).eval (α t) = 0) {l : ℕ} (hl : l < m) :
    ∑ t, α t ^ (m - 1 - l) / (derivative (characteristic A m)).eval (α t) =
      if l = 0 then 1 else 0 := by
  rw [characteristic_eq_nodal hα hroot]
  simp_rw [Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ _), Lagrange.eval_nodal]
  have hdeg : (X ^ (m - 1 - l) : ℂ[X]).degree < #(univ : Finset (Fin m)) := by
    simp only [degree_X_pow, card_univ, Fintype.card_fin, Nat.cast_lt]
    omega
  have h := Lagrange.coeff_eq_sum hα.injOn hdeg
  simpa only [card_univ, Fintype.card_fin, coeff_X_pow, eval_pow, eval_X,
    show m - 1 = m - 1 - l ↔ l = 0 by omega] using h.symm

/-- The polynomial numerator evaluated at a characteristic root, starting at index `i`. -/
private noncomputable def numerator (A s : ℕ → ℂ) (m r i : ℕ) (x : ℂ) : ℂ :=
  ∑ l ∈ range m, decimationCoeff A s m r l i * x ^ (m - 1 - l)

/-- Shifting the starting index removes the last summand in the next coefficient. -/
private theorem coeff_shift (A s : ℕ → ℂ) (m r l i : ℕ) :
    decimationCoeff A s m r l (i + r) =
      decimationCoeff A s m r (l + 1) i + A (m - 1 - l) * s i := by
  simp only [decimationCoeff, sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, zero_mul,
    zero_add, Nat.add_mul, one_mul]
  have heq : ∀ j ∈ range l, s ((l - 1 - j) * r + (i + r)) = s ((l - j) * r + i) := by
    intro j hj
    have hjl := mem_range.mp hj
    rw [show l - j = l - 1 - j + 1 by omega, Nat.add_mul, one_mul]
    congr 1
    omega
  rw [sum_congr rfl (fun j hj ↦ congrArg (A (m - 1 - j) * ·) (heq j hj))]
  rw [show l * r + (i + r) = l * r + r + i by omega]
  ring

/-- At a root, a stride multiplies the numerator by the root. -/
private theorem numerator_shift
    (hs : ∀ n, s (n + m * r) = ∑ j ∈ range m, A j * s (n + j * r))
    {x : ℂ} (hx : (characteristic A m).eval x = 0) (i : ℕ) :
    numerator A s m r (i + r) x = numerator A s m r i x * x := by
  have hlast : decimationCoeff A s m r m i = 0 := by
    rw [decimationCoeff, sum_range_reflect (fun j ↦ A j * s (j * r + i)), sub_eq_zero]
    simpa only [Nat.add_comm i] using hs i
  have hpow : ∑ j ∈ range m, A j * x ^ j = x ^ m := by
    symm
    simpa [characteristic, eval_finsetSum, sub_eq_zero] using hx
  have hA : ∑ l ∈ range m, A (m - 1 - l) * s i * x ^ (m - 1 - l) = s i * x ^ m := by
    rw [sum_range_reflect (fun j ↦ A j * s i * x ^ j), ← hpow, mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring
  let term (l : ℕ) := decimationCoeff A s m r l i * x ^ (m - l)
  have hsplit := sum_range_succ' term m
  rw [sum_range_succ, show term m = 0 by simp [term, hlast], add_zero] at hsplit
  have hterms : numerator A s m r i x * x = ∑ l ∈ range m, term l := by
    unfold numerator
    rw [sum_mul]
    apply sum_congr rfl
    intro l hl
    have hlt := mem_range.mp hl
    simp only [term, show m - l = m - 1 - l + 1 by omega, pow_succ, mul_assoc]
  rw [hterms, hsplit, numerator]
  simp_rw [coeff_shift, add_mul, sum_add_distrib, hA]
  simp [term, Nat.sub_sub, Nat.add_comm 1, decimationCoeff_zero]

/-- Collect the Binet sum by root so that advancing along the recurrence acts diagonally. -/
private theorem sum_by_root (A s : ℕ → ℂ) (m r i q : ℕ) (α d : Fin m → ℂ) :
    (∑ l ∈ range m, decimationCoeff A s m r l i *
      ∑ t, α t ^ (m - 1 - l + q) / d t) =
      ∑ t, numerator A s m r i (α t) * α t ^ q / d t := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  simp only [numerator, div_eq_mul_inv, sum_mul, pow_add, mul_assoc]

end decimation_binet

open decimation_binet

/-- **Binet formula for decimated linear recurrences.** Let $m$ and $r$ be natural numbers and
let $(A_j)_{j \ge 0}$ and $(s_n)_{n \ge 0}$ be sequences of complex numbers such that
$s_{n+mr} = \sum_{j<m} A_j s_{n+jr}$ for all $n \ge 0$. Let $f(x) = x^m - \sum_{j<m} A_j x^j$
and let $\alpha_1, \ldots, \alpha_m$ be pairwise distinct roots of $f$ in $\mathbb{C}$. Then
for every $n \ge 0$
$$
s_n = \sum_{l<m} v_l^{(n \bmod r)}
\sum_{t=1}^{m} \frac{\alpha_t^{m-1-l+\lfloor n/r \rfloor}}{f'(\alpha_t)},
$$
where $v_l^{(i)} = s_{lr+i} - \sum_{j<l} A_{m-1-j} s_{(l-1-j)r+i}$ are the decimation
coefficients. For $r = 0$ the formula is read with $n \bmod 0 = n$ and
$\lfloor n/0 \rfloor = 0$.

Source: Emre Güday and Murat Sahin, *Linear Recurrence Relations Satisfied by the General
Conditional Sequences*, INTEGERS 26 (2026), Article A5, Theorem 2 (`integers-2026-A5-thm-2`). -/
public theorem decimation_binet {m r : ℕ} {A s : ℕ → ℂ}
    (hs : ∀ n, s (n + m * r) = ∑ j ∈ Finset.range m, A j * s (n + j * r))
    {α : Fin m → ℂ} (hα : Function.Injective α)
    (hroot : ∀ t, (X ^ m - ∑ j ∈ Finset.range m, C (A j) * X ^ j : ℂ[X]).eval (α t) = 0)
    (n : ℕ) :
    s n = ∑ l ∈ Finset.range m, decimationCoeff A s m r l (n % r) *
      ∑ t, α t ^ (m - 1 - l + n / r) /
        (derivative (X ^ m - ∑ j ∈ Finset.range m, C (A j) * X ^ j : ℂ[X])).eval (α t) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hs n
  let d (t : Fin m) := (derivative (characteristic A m)).eval (α t)
  have initial (i : ℕ) : s i = ∑ t, numerator A s m r i (α t) / d t := by
    have h := sum_by_root A s m r i 0 α d
    simp only [Nat.add_zero, pow_zero, mul_one] at h
    rw [← h]
    calc
      s i = ∑ l ∈ range m, decimationCoeff A s m r l i * (if l = 0 then 1 else 0) := by
        simp [mul_ite, hm, decimationCoeff_zero]
      _ = _ := sum_congr rfl fun l hl ↦
        congrArg (decimationCoeff A s m r l i * ·) (moment hα hroot (mem_range.mp hl)).symm
  have advance (q i : ℕ) : s (q * r + i) =
      ∑ t, numerator A s m r i (α t) * α t ^ q / d t := by
    induction q generalizing i with
    | zero => simpa using initial i
    | succ q ih =>
      rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm r i, ih]
      apply sum_congr rfl
      intro t _
      rw [numerator_shift hs (hroot t), pow_succ]
      ring
  rw [sum_by_root]
  simpa only [Nat.div_add_mod'] using advance (n / r) (n % r)

end MetaMathlibExt
