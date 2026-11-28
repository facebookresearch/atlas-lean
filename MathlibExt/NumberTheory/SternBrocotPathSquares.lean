/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import all MathlibExt.NumberTheory.PerronPalindrome

/-!
# Sums of two squares from the Stern–Brocot tree

The matrix product of the supplied palindromic continued fraction is the product of its
first half with its transpose. The top-left entry is the squared norm of the first row of
the half product, whose entries are, up to order, the column sums of the path matrix.
-/

namespace MetaMathlibExt

local notation "R" => (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℕ)
local notation "L" => (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℕ)
local notation "J" => (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ)

namespace sq_add_sq_of_sternBrocot_path

open exists_palindrome_continuedFraction_div (step)

private theorem palindrome_eq_append_reverse (q : ℕ → ℕ) (n : ℕ) :
    ((List.range (2 * n + 2)).map fun i => q (min i (2 * n + 1 - i))) =
      (List.range (n + 1)).map q ++ ((List.range (n + 1)).map q).reverse := by
  apply List.ext_getElem (by simp; omega)
  intro i hi₁ hi₂
  by_cases hi : i < n + 1
  · rw [List.getElem_append_left (by simpa using hi)]
    simp [Nat.min_eq_left (show i ≤ 2 * n + 1 - i by omega)]
  · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hi)]
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_map,
      List.length_range]
    congr 1
    omega

private theorem prod_reverse_step (qs : List ℕ) :
    (qs.reverse.map step).prod = (qs.map step).prod.transpose := by
  have hsymm (a : ℕ) : (step a).transpose = step a := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  induction qs with
  | nil => simp
  | cons a qs ih =>
    rw [List.reverse_cons, List.map_append, List.prod_append, ih]
    simp [Matrix.transpose_mul, hsymm]

private theorem det_prod_step (qs : List ℕ) :
    (((qs.map step).prod).map (Nat.castRingHom ℤ)).det = (-1 : ℤ) ^ qs.length := by
  induction qs with
  | nil => simp
  | cons a qs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Matrix.map_mul (f := Nat.castRingHom ℤ), Matrix.det_mul, ih, pow_succ']
    simp [Matrix.det_fin_two, step]

private theorem right_pow (a : ℕ) : R ^ a = !![1, a; 0, 1] := by
  induction a with
  | zero => exact Matrix.one_fin_two
  | succ a ih => simp [pow_succ, ih, Nat.add_comm]

private theorem left_pow (a : ℕ) : L ^ a = !![1, 0; a, 1] := by
  induction a with
  | zero => exact Matrix.one_fin_two
  | succ a ih => simp [pow_succ, ih]

/-- Switching columns after each continued-fraction step produces the alternating move product. -/
private theorem half_eq_path (q : ℕ → ℕ) (k : ℕ) :
    (((List.range k).map q).map step).prod =
      ((List.range k).map fun i => (if Even i then R else L) ^ q i).prod *
        (if Even k then 1 else J) := by
  have hR (a : ℕ) : step a = R ^ a * J := by rw [right_pow]; simp [step]
  have hL (a : ℕ) : J * step a = L ^ a := by rw [left_pow]; simp [step]
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, ih, Nat.even_add_one]
    by_cases hk : Even k
    · simp [hk, hR, mul_assoc]
    · simp [hk, mul_assoc, hL]

private theorem eq_num_of_det_eq_one {p x : ℕ} {P : Matrix (Fin 2) (Fin 2) ℕ}
    (hp : p.Prime) (hx : 0 < x) (hxp : x < p)
    (hfrac : (p : ℚ) / x = (P 0 0 : ℚ) / P 1 0)
    (hdet : (P.map (Nat.cast : ℕ → ℤ)).det = 1) : p = P 0 0 := by
  have hden : 0 < P 1 0 := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, Nat.cast_zero, div_zero] at hfrac
    exact div_ne_zero (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hx.ne') hfrac
  have hcop : p.Coprime x :=
    hp.coprime_iff_not_dvd.mpr (fun h => (Nat.le_of_dvd hx h).not_gt hxp)
  have hdet' : (P 0 0 : ℤ) * P 1 1 - (P 0 1 : ℤ) * P 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdet
  have hprim : IsCoprime (P 0 0 : ℤ) (P 1 0 : ℤ) := by
    refine ⟨P 1 1, -(P 0 1 : ℤ), ?_⟩
    linear_combination hdet'
  have hinj := Rat.div_int_inj (a := (p : ℤ)) (b := (x : ℤ)) (c := (P 0 0 : ℤ))
    (d := (P 1 0 : ℤ)) (by exact_mod_cast hx) (by exact_mod_cast hden)
    (by simpa using hcop) (by simpa using hprim.natCoprime) (by simpa using hfrac)
  exact_mod_cast hinj.1

end sq_add_sq_of_sternBrocot_path

open exists_palindrome_continuedFraction_div (step eval_product)

-- The congruences are used to obtain the palindrome, which is already supplied here.
set_option linter.unusedVariables false in
open sq_add_sq_of_sternBrocot_path in
/-- **Sums of two squares from the Stern–Brocot tree.** Let $p$ be a prime with
$p \equiv 1 \pmod 4$, and let $x_0$ be an integer with $0 < x_0 < p/2$ and
$x_0^2 \equiv -1 \pmod p$. Let $n \ge 0$ and let $q_0, q_1, \dots, q_n$ be positive integers with
$p / x_0 = [q_0; q_1, \dots, q_n, q_n, \dots, q_1, q_0]$, where
$[a_0; a_1, \dots, a_m] = a_0 + 1/(a_1 + 1/(\cdots + 1/a_m))$. With
$R = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ and
$L = \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$, let
$M = R^{q_0 - 1} M_1^{q_1} M_2^{q_2} \cdots M_n^{q_n}$, where $M_i = R$ for even $i$ and
$M_i = L$ for odd $i$. If $(x, y)^{\mathsf T} = M^{\mathsf T} (1, 1)^{\mathsf T}$, then
$p = x^2 + y^2$.

The fraction $x / y$ is the label of the path $M^{\mathsf T}$ in the Stern–Brocot tree.

Source: Hongshen Chua, *Binary Trees and Sum of Two Squares*, INTEGERS 26 (2026), Article A76,
Theorem 3 (`integers-2026-A76-thm-3`). -/
public theorem sq_add_sq_of_sternBrocot_path {p x₀ : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hx : (x₀ ^ 2 + 1) % p = 0) (hx₀ : 0 < x₀) (hxp : 2 * x₀ < p) (n : ℕ) (q : ℕ → ℕ)
    (hq : ∀ i ≤ n, 1 ≤ q i)
    (hcf : (p : ℚ) / x₀ = ((List.range (2 * n + 2)).map fun i => q (min i (2 * n + 1 - i))).foldr
      (fun a acc => (a : ℚ) + acc⁻¹) 0) :
    let M : Matrix (Fin 2) (Fin 2) ℕ := !![1, 1; 0, 1] ^ (q 0 - 1) *
      ((List.range n).map fun i =>
        (if Even (i + 1) then !![1, 1; 0, 1] else !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℕ) ^
          q (i + 1)).prod
    p = (M.transpose.mulVec ![1, 1] 0) ^ 2 + (M.transpose.mulVec ![1, 1] 1) ^ 2 := by
  intro M
  let half := (List.range (n + 1)).map q
  let qs := half ++ half.reverse
  let H := (half.map step).prod
  let P := (qs.map step).prod
  rw [palindrome_eq_append_reverse] at hcf
  have hpos : ∀ a ∈ qs, 1 ≤ a := by
    simp only [qs, List.forall_mem_append, List.mem_reverse, and_self]
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact hq i (by simpa [Nat.lt_succ_iff] using hi)
  have heval := (eval_product qs hpos).2
  have hP : P = H * H.transpose := by
    simp only [P, qs, H, List.map_append, List.prod_append, prod_reverse_step]
  have hdet : (P.map (Nat.castRingHom ℤ)).det = 1 := by
    rw [hP, Matrix.map_mul (f := Nat.castRingHom ℤ), Matrix.transpose_map,
      Matrix.det_mul, Matrix.det_transpose]
    change (((half.map step).prod).map (Nat.castRingHom ℤ)).det *
      (((half.map step).prod).map (Nat.castRingHom ℤ)).det = 1
    rw [det_prod_step, ← mul_pow]
    simp
  have hpP : p = P 0 0 := eq_num_of_det_eq_one hp hx₀ (by omega) (hcf.trans heval) hdet
  -- Restoring the leading right move makes the first row the column sums of `M`.
  have hpath :
      ((List.range (n + 1)).map fun i => (if Even i then R else L) ^ q i).prod = R * M := by
    have hq₀ : q 0 - 1 + 1 = q 0 := Nat.sub_add_cancel (hq 0 (Nat.zero_le n))
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.prod_cons]
    simp only [show Even (0 : ℕ) by decide, ite_true]
    rw [← hq₀, pow_succ', mul_assoc]
    rfl
  let C := if Even (n + 1) then (1 : Matrix (Fin 2) (Fin 2) ℕ) else J
  have hH : H = (R * M) * C := (half_eq_path q (n + 1)).trans (by rw [hpath])
  have hC : C * C.transpose = 1 := by
    by_cases hc : Even (n + 1)
    · simp [C, hc]
    · simpa [C, hc] using (show J * Matrix.transpose J = 1 by decide)
  have hGram : P = (R * M) * (R * M).transpose := by
    rw [hP, hH, Matrix.transpose_mul, mul_assoc, ← mul_assoc C, hC, one_mul]
  rw [hpP, hGram]
  simp [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two, pow_two]

end MetaMathlibExt
