/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.SternBrocotSumTwoSquares

/-!
# Binary trees, continued fractions and sums of two squares

Statements from Hongshen Chua, *Binary Trees and Sum of Two Squares*, INTEGERS 26 (2026),
Article A76. A path in the matrix binary tree is a product of the moves
`R = !![1, 1; 0, 1]` and `L = !![1, 0; 1, 1]` (post-multiplication, starting from the identity);
the Stern–Brocot fraction of a path matrix `P` is the column vector `P (1, 1)ᵀ`. A finite
continued fraction `[q₀; q₁, …, q_m]` is evaluated as the right fold
`q₀ + (q₁ + ⋯ + (q_m + 0⁻¹)⁻¹ ⋯)⁻¹` (with `0⁻¹ = 0`). Theorem 2 (Fermat's two squares theorem)
is Mathlib's `Nat.Prime.sq_add_sq`.

The main result, `MetaMathlibExt.sq_add_sq_of_sternBrocot_path`, reads the two squares of a
prime `p ≡ 1 (mod 4)` off the Stern–Brocot path given by the palindromic continued fraction of
`p / x₀`, where `x₀² ≡ -1 (mod p)`. As in the source, the matrix of the palindrome is a matrix
times its transpose. The proof writes each partial quotient `q` as the symmetric matrix
`!![q, 1; 1, 0]`: if `U` is the product over the first half `q₀, …, qₙ`, the palindrome gives
`U Uᵀ`, which has determinant one. Its first column `(a, b)` therefore has coprime entries and
`a / b = p / x₀`, hence equals `(p, x₀)`, so `p` is the sum of the squares of the first row of
`U`. That row consists of two consecutive convergent numerators, and the matrix path theorem
`MetaMathlibExt.continuedFraction_path_eq_convergents` identifies them, up to order, with the
column sums of the path matrix.
-/

namespace MetaMathlibExt

namespace sq_add_sq_of_sternBrocot_path

/-- A partial quotient `a` as the symmetric matrix `!![a, 1; 1, 0]`. -/
private def step (a : ℕ) : Matrix (Fin 2) (Fin 2) ℕ := !![a, 1; 1, 0]

/-- Shifted convergent numerators: `num q (k + 1)` is the numerator of `[q₀; q₁, …, qₖ]` when
every `q i` is positive. -/
private def num (q : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => q 0
  | k + 2 => q (k + 1) * num q (k + 1) + num q k

/-- Shifted convergent denominators: `den q (k + 1)` is the denominator of `[q₀; q₁, …, qₖ]`
when every `q i` is positive. -/
private def den (q : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 => q (k + 1) * den q (k + 1) + den q k

/-- The first column of the product of the step matrices gives the numerator and the
denominator of the fold. -/
private theorem eval_product (qs : List ℕ) (hqs : ∀ a ∈ qs, 1 ≤ a) :
    0 < (qs.map step).prod 0 0 ∧
      qs.foldr (fun a acc => (a : ℚ) + acc⁻¹) 0 =
        ((qs.map step).prod 0 0 : ℚ) / (qs.map step).prod 1 0 := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    obtain ⟨hnum, hval⟩ := ih (fun a ha => hqs a (List.mem_cons_of_mem q ha))
    have hq := hqs q List.mem_cons_self
    simp only [List.bind_eq_flatMap, List.pure_def] at hval
    constructor
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, step] using
        Nat.add_pos_left (Nat.mul_pos hq hnum) ((qs.map step).prod 1 0)
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, step, List.pure_def, hval, inv_div] using
        add_div' ((qs.map step).prod 1 0 : ℚ) q ((qs.map step).prod 0 0)
          (by exact_mod_cast hnum.ne')

/-- The step matrices are symmetric, so reversing the list transposes the product. -/
private theorem prod_reverse (l : List ℕ) :
    (l.reverse.map step).prod = (l.map step).prod.transpose := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hs : (step a).transpose = step a := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [List.reverse_cons, List.map_append, List.prod_append, ih]
    simp [Matrix.transpose_mul, hs]

/-- A product of step matrices has determinant `(-1) ^ length`. -/
private theorem det_prod (l : List ℕ) :
    ((l.map step).prod 0 0 * (l.map step).prod 1 1 : ℤ) -
        (l.map step).prod 0 1 * (l.map step).prod 1 0 = (-1) ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, step,
      List.length_cons, pow_succ]
    simp
    linear_combination (-1 : ℤ) * ih

/-- The product of the first `n + 1` step matrices has the convergents as columns. -/
private theorem prod_range (q : ℕ → ℕ) (n : ℕ) :
    ((List.range (n + 1)).map fun i => step (q i)).prod =
      !![num q (n + 1), num q n; den q (n + 1), den q n] := by
  induction n with
  | zero => simp [step, num, den]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [step, num, den, Matrix.mul_apply, Nat.mul_comm]

/-- The palindromic list of partial quotients is a list followed by its reverse. -/
private theorem palindrome_list (q : ℕ → ℕ) (n : ℕ) :
    (List.range (2 * n + 2)).map (fun i => q (min i (2 * n + 1 - i))) =
      (List.range (n + 1)).map q ++ ((List.range (n + 1)).map q).reverse := by
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_append, List.length_map,
    List.length_range, List.getElem_reverse]
  split_ifs with h
  · congr 1; omega
  · congr 1; omega

end sq_add_sq_of_sternBrocot_path

open sq_add_sq_of_sternBrocot_path in
set_option linter.unusedVariables false in
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
  -- The palindrome is `l ++ l.reverse`, so its product of step matrices is `U * Uᵀ`.
  set l := (List.range (n + 1)).map q with hl
  have hpos : ∀ a ∈ l ++ l.reverse, 1 ≤ a := by
    intro a ha
    rw [List.mem_append, List.mem_reverse, or_self, hl, List.mem_map] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact hq i (Nat.lt_succ_iff.mp (List.mem_range.mp hi))
  set U := (l.map step).prod with hU
  have hprod : ((l ++ l.reverse).map step).prod = U * U.transpose := by
    rw [List.map_append, List.prod_append, prod_reverse]
  obtain ⟨-, hval⟩ := eval_product (l ++ l.reverse) hpos
  rw [palindrome_list, ← hl, hval, hprod] at hcf
  set a := U 0 0 ^ 2 + U 0 1 ^ 2 with ha
  set b := U 1 0 * U 0 0 + U 1 1 * U 0 1 with hb
  set c := U 1 0 ^ 2 + U 1 1 ^ 2 with hc
  have h00 : (U * U.transpose) 0 0 = a := by simp [Matrix.mul_apply, Fin.sum_univ_two, a, sq]
  have h10 : (U * U.transpose) 1 0 = b := by simp [Matrix.mul_apply, Fin.sum_univ_two, b]
  rw [h00, h10] at hcf
  -- `U` has determinant `±1`, so `a * c = b ^ 2 + 1` and `a / b` is in lowest terms.
  have hdet : ((U 0 0 : ℤ) * U 1 1 - U 0 1 * U 1 0) ^ 2 = 1 := by
    rw [hU, det_prod, ← pow_mul, pow_mul', neg_one_sq, one_pow]
  have hacZ : (a * c : ℤ) = b ^ 2 + 1 := by
    simp only [a, b, c]
    push_cast
    linear_combination hdet
  have hac : a * c = b ^ 2 + 1 := by exact_mod_cast hacZ
  have hab : Nat.Coprime a b := by
    have h1 : Nat.gcd a b ∣ b ^ 2 + 1 := hac ▸ (Nat.gcd_dvd_left a b).mul_right c
    exact Nat.dvd_one.mp ((Nat.dvd_add_right ((Nat.gcd_dvd_right a b).pow two_ne_zero)).mp h1)
  -- Since `p / x₀` is in lowest terms too, `p = a`.
  have hb0 : b ≠ 0 := by
    rintro hb0
    rw [hb0, Nat.cast_zero, div_zero, div_eq_zero_iff] at hcf
    rcases hcf with h | h <;> norm_cast at h <;> omega
  have hcross : p * b = a * x₀ := by
    rw [div_eq_div_iff (by exact_mod_cast hx₀.ne') (by exact_mod_cast hb0)] at hcf
    exact_mod_cast hcf
  have hpx : Nat.Coprime p x₀ :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hx₀ (by omega))
  have hpa : p = a := Nat.dvd_antisymm
    (hpx.dvd_of_dvd_mul_right ⟨b, by rw [← hcross]⟩)
    (hab.dvd_of_dvd_mul_right ⟨x₀, by rw [hcross]⟩)
  -- The first row of `U` and the column sums of `M` are the same two convergent numerators.
  have hU' : U = !![num q (n + 1), num q n; den q (n + 1), den q n] := by
    rw [hU, hl, List.map_map]
    exact prod_range q n
  have hT := continuedFraction_path_eq_convergents q (num q) (den q) rfl rfl (fun _ => rfl)
    rfl rfl (fun _ => rfl) n
  have hRM : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℕ) * M =
      ((List.range (n + 1)).map fun i =>
        (if Even i then !![1, 1; 0, 1] else !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℕ) ^
          q i).prod := by
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
    simp only [M, ← mul_assoc, ← pow_succ']
    rw [Nat.sub_add_cancel (hq 0 (Nat.zero_le n))]
    simp [Function.comp_def]
  have hcol₀ : M.transpose.mulVec ![1, 1] 0 =
      ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℕ) * M) 0 0 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
  have hcol₁ : M.transpose.mulVec ![1, 1] 1 =
      ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℕ) * M) 0 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
  rw [hcol₀, hcol₁, hRM, hT, hpa, ha, hU']
  split_ifs <;> simp [add_comm]

end MetaMathlibExt
