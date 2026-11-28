/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.LinearAlgebra.Matrix.TrudiBrioschiDeterminant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Generating function of Toeplitz–Hessenberg determinants

The theorem `toeplitzHessenbergDet_genFun` shows that, for a sequence $a_0, a_1, a_2, \dots$ in a
commutative ring, the generating function $f(x) = \sum_{n \ge 1} \det(a_0; a_1, \dots, a_n)\, x^n$
of its Toeplitz–Hessenberg determinants satisfies $f = H + H f$ with
$H(x) = \sum_{i \ge 1} a_i (-a_0)^{i-1} x^i$.

The proof expands the determinant along its first column. Deleting row $i$ and column $0$ of the
matrix of size $n + 1$ leaves a block lower triangular minor whose diagonal blocks are a lower
triangular matrix with $a_0$ on its diagonal and the Toeplitz–Hessenberg matrix of size $n - i$;
this gives the recurrence
$\det(a_0; a_1, \dots, a_{n+1}) = \sum_{i=0}^{n} a_{i+1} (-a_0)^i \det(a_0; a_1, \dots, a_{n-i})$,
which is the coefficientwise form of the identity.
-/

namespace MetaMathlibExt
namespace toeplitzHessenbergDet_genFun

variable {R : Type*} [CommRing R] (a : ℕ → R)

-- The minor of the Toeplitz–Hessenberg matrix of size `n + 1` that deletes row `i` and column `0`:
-- its rows above `i` are lower triangular with `a 0` on the diagonal and vanish from column `i`
-- on, and its rows from `i` on form the Toeplitz–Hessenberg matrix of size `n - i`.
private lemma det_minor (n i : ℕ) (hi : i ≤ n) :
    (Matrix.of fun r c : Fin n =>
      if (r : ℕ) < i then (if (c : ℕ) ≤ r then a (r - c) else 0)
      else if (c : ℕ) ≤ r + 1 then a (r + 1 - c) else 0).det =
      a 0 ^ i * toeplitzHessenbergDet a (n - i) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Nat.add_sub_cancel_left, ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  set M := (Matrix.of fun r c : Fin (i + k) =>
      if (r : ℕ) < i then (if (c : ℕ) ≤ r then a (r - c) else 0)
      else if (c : ℕ) ≤ r + 1 then a (r + 1 - c) else 0).submatrix finSumFinEquiv finSumFinEquiv
  have h12 : M.toBlocks₁₂ = 0 := by
    ext r c
    simp only [M, Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.of_apply,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
      Matrix.zero_apply]
    rw [ite_eq_left r.is_lt, ite_eq_right (by omega)]
  rw [← Matrix.fromBlocks_toBlocks M, h12, Matrix.det_fromBlocks_zero₁₂]
  congr 1
  · rw [Matrix.det_of_isLowerTriangular]
    · simp only [M, Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.of_apply,
        finSumFinEquiv_apply_left, Fin.val_castAdd, Fin.is_lt, ite_true, le_refl, Nat.sub_self,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · intro r c hrc
      simp only [M, Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.of_apply,
        finSumFinEquiv_apply_left, Fin.val_castAdd, Fin.is_lt, ite_true]
      have : (r : ℕ) < c := hrc
      rw [ite_eq_right (by omega)]
  · unfold toeplitzHessenbergDet
    congr 1
    ext r c
    simp only [M, Matrix.toBlocks₂₂, Matrix.submatrix_apply, Matrix.of_apply,
      finSumFinEquiv_apply_right, Fin.val_natAdd]
    rw [ite_eq_right (by omega)]
    by_cases h : (c : ℕ) ≤ r + 1
    · rw [ite_eq_left (by omega), ite_eq_left h]
      congr 1
      omega
    · rw [ite_eq_right (by omega), ite_eq_right h]

-- Expansion along the first column.
private lemma det_succ (n : ℕ) :
    toeplitzHessenbergDet a (n + 1) =
      ∑ i ∈ Finset.range (n + 1), a (i + 1) * (-a 0) ^ i * toeplitzHessenbergDet a (n - i) := by
  rw [toeplitzHessenbergDet, Matrix.det_succ_column_zero,
    ← Fin.sum_univ_eq_sum_range
      (fun i => a (i + 1) * (-a 0) ^ i * toeplitzHessenbergDet a (n - i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.is_lt
  have hsub : (Matrix.of fun r c : Fin (n + 1) =>
        if (c : ℕ) ≤ (r : ℕ) + 1 then a ((r : ℕ) + 1 - (c : ℕ)) else 0).submatrix
        i.succAbove Fin.succ =
      Matrix.of fun r c : Fin n =>
        if (r : ℕ) < i then (if (c : ℕ) ≤ r then a (r - c) else 0)
        else if (c : ℕ) ≤ r + 1 then a (r + 1 - c) else 0 := by
    ext r c
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ]
    by_cases hr : (r : ℕ) < i
    · rw [Fin.succAbove_of_castSucc_lt _ _ hr, Fin.val_castSucc, ite_eq_left hr]
      by_cases hc : (c : ℕ) ≤ r
      · rw [ite_eq_left (by omega), ite_eq_left hc]
        congr 1
        omega
      · rw [ite_eq_right (by omega), ite_eq_right hc]
    · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def, Fin.val_castSucc]; omega),
        Fin.val_succ, ite_eq_right hr]
      by_cases hc : (c : ℕ) ≤ r + 1
      · rw [ite_eq_left (by omega), ite_eq_left hc]
        congr 1
        omega
      · rw [ite_eq_right (by omega), ite_eq_right hc]
  rw [hsub, det_minor a n i hi, Matrix.of_apply, Fin.val_zero, ite_eq_left (Nat.zero_le _),
    Nat.sub_zero, neg_pow]
  ring

end toeplitzHessenbergDet_genFun

open toeplitzHessenbergDet_genFun

/-- **Generating function of Toeplitz–Hessenberg determinants.** Let $R$ be a commutative ring and
$a_0, a_1, a_2, \dots$ a sequence in $R$. Write $\det(a_0; a_1, \dots, a_n)$ for the determinant
of the $n \times n$ Toeplitz–Hessenberg matrix whose entry in row $i$ and column $j$ is
$a_{i+1-j}$ for $j \le i + 1$ and $0$ above the superdiagonal. In the ring of formal power series
over $R$ let $f(x) = \sum_{n \ge 1} \det(a_0; a_1, \dots, a_n)\, x^n$ and
$H(x) = \sum_{i \ge 1} a_i (-a_0)^{i-1} x^i$. Then $f = H + H f$.

When $a_0$ is invertible, $H(x) = -g(-a_0 x)/a_0$ with $g(x) = \sum_{i \ge 1} a_i x^i$, and the
identity is the paper's $f(x) = (-g(-a_0 x)/a_0)/(1 + g(-a_0 x)/a_0)$. The form $f = H + H f$
needs no hypothesis on $a_0$; for $a_0 = 0$ it gives $\det(0; a_1, \dots, a_n) = a_1^n$.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Lemma 2
(`jis-2026-26.1.2-lem-2`). -/
public theorem toeplitzHessenbergDet_genFun {R : Type*} [CommRing R] (a : ℕ → R) :
    PowerSeries.mk (fun n => if n = 0 then 0 else toeplitzHessenbergDet a n) =
      PowerSeries.mk (fun i => if i = 0 then 0 else a i * (-a 0) ^ (i - 1)) +
        PowerSeries.mk (fun i => if i = 0 then 0 else a i * (-a 0) ^ (i - 1)) *
          PowerSeries.mk (fun n => if n = 0 then 0 else toeplitzHessenbergDet a n) := by
  set H : PowerSeries R := PowerSeries.mk fun i => if i = 0 then 0 else a i * (-a 0) ^ (i - 1)
  set F : PowerSeries R := PowerSeries.mk fun n => toeplitzHessenbergDet a n
  have hf : PowerSeries.mk (fun n => if n = 0 then 0 else toeplitzHessenbergDet a n) = F - 1 := by
    ext n
    rcases n with _ | n
    · simp [F, toeplitzHessenbergDet_zero]
    · simp [F, PowerSeries.coeff_one]
  -- With `D 0 = 1`, the recurrence `det_succ` reads `F = 1 + H F` coefficientwise.
  have hF : F = 1 + H * F := by
    ext n
    rcases n with _ | n
    · simp [F, H, toeplitzHessenbergDet_zero]
    · rw [map_add, PowerSeries.coeff_one, ite_eq_right n.succ_ne_zero, zero_add,
        PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [F, H, det_succ]
  rw [hf]
  linear_combination hF

end MetaMathlibExt
