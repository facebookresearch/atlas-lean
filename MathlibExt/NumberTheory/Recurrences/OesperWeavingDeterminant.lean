/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith.Frontend

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators Matrix

private def Cfun : Nat → Int := fun j => Finset.sum (Finset.Icc 1 j)
  (fun i => (-1 : Int) ^ (i + 1) * Nat.fib i)

private def Mmat : Matrix (Fin 3) (Fin 3) Int := !![2, -1, 0; 0, 0, 1; -1, 0, 2]

private theorem C_odd : ∀ n : Nat, Cfun (2 * n + 1) = (Nat.fib (2 * n) : Int) + 1 := by
  intro n
  induction n with
  | zero => simp [Cfun]
  | succ n ih =>
    have hstep : 2 * (n + 1) + 1 = ((2 * n + 1) + 1) + 1 := by omega
    have h2n : 2 * (n + 1) = 2 * n + 2 := by omega
    have hab1 : 1 ≤ ((2 * n + 1) + 1) + 1 := by omega
    have hab2 : 1 ≤ (2 * n + 1) + 1 := by omega
    have step1 : Finset.sum (Finset.Icc 1 (((2 * n + 1) + 1) + 1))
        (fun i => (-1 : Int) ^ (i + 1) * (Nat.fib i : Int))
        = Finset.sum (Finset.Icc 1 ((2 * n + 1) + 1))
        (fun i => (-1 : Int) ^ (i + 1) * (Nat.fib i : Int))
        + (-1 : Int) ^ ((((2 * n + 1) + 1) + 1) + 1)
          * ((Nat.fib (((2 * n + 1) + 1) + 1) : Nat) : Int) :=
      Finset.sum_Icc_succ_top hab1 _
    have step2 : Finset.sum (Finset.Icc 1 ((2 * n + 1) + 1))
        (fun i => (-1 : Int) ^ (i + 1) * (Nat.fib i : Int))
        = Finset.sum (Finset.Icc 1 (2 * n + 1))
        (fun i => (-1 : Int) ^ (i + 1) * (Nat.fib i : Int))
        + (-1 : Int) ^ (((2 * n + 1) + 1) + 1) * ((Nat.fib ((2 * n + 1) + 1) : Nat) : Int) :=
      Finset.sum_Icc_succ_top hab2 _
    simp only [Cfun] at ih ⊢
    rw [hstep, step1, step2]
    have e3 : ((2 * n + 1) + 1) + 1 = 2 * n + 3 := by omega
    have e2 : (2 * n + 1) + 1 = 2 * n + 2 := by omega
    rw [e3, e2]
    have p1 : (-1 : Int) ^ ((2 * n + 3) + 1) = 1 := Even.neg_one_pow ⟨n + 2, by ring⟩
    have p2 : (-1 : Int) ^ ((2 * n + 2) + 1) = -1 := Odd.neg_one_pow ⟨n + 1, by ring⟩
    rw [p1, p2]
    have g1 :
        (Nat.fib (2 * n + 2) : Int) = (Nat.fib (2 * n) : Int) + (Nat.fib (2 * n + 1) : Int) := by
      have h := Nat.fib_add_two (n := 2 * n)
      exact_mod_cast h
    have g2 :
        (Nat.fib (2 * n + 3) : Int) =
          (Nat.fib (2 * n + 1) : Int) + (Nat.fib (2 * n + 2) : Int) := by
      have h := Nat.fib_add_two (n := 2 * n + 1)
      have he : (2 * n + 1) + 2 = 2 * n + 3 := by omega
      have he2 : (2 * n + 1) + 1 = 2 * n + 2 := by omega
      rw [he, he2] at h
      exact_mod_cast h
    rw [h2n]
    simp only [ih]
    linear_combination g2 - g1

private theorem C_even_all :
    ∀ n : Nat, Cfun (2 * n) = (Nat.fib (2 * n) : Int) - (Nat.fib (2 * n + 1) : Int) + 1 := by
  intro n
  induction n with
  | zero => simp [Cfun]
  | succ n ih =>
    have hstep : 2 * (n + 1) = ((2 * n) + 1) + 1 := by omega
    have hab1 : 1 ≤ ((2 * n) + 1) + 1 := by omega
    have hab2 : 1 ≤ (2 * n) + 1 := by omega
    have step1 : Finset.sum (Finset.Icc 1 (((2 * n) + 1) + 1))
        (fun i => (-1 : Int) ^ (i + 1) * (Nat.fib i : Int))
        = Finset.sum (Finset.Icc 1 ((2 * n) + 1))
        (fun i => (-1 : Int) ^ (i + 1) * (Nat.fib i : Int))
        + (-1 : Int) ^ ((((2 * n) + 1) + 1) + 1) * ((Nat.fib (((2 * n) + 1) + 1) : Nat) : Int) :=
      Finset.sum_Icc_succ_top hab1 _
    have step2 : Finset.sum (Finset.Icc 1 ((2 * n) + 1))
        (fun i => (-1 : Int) ^ (i + 1) * (Nat.fib i : Int))
        = Finset.sum (Finset.Icc 1 (2 * n))
        (fun i => (-1 : Int) ^ (i + 1) * (Nat.fib i : Int))
        + (-1 : Int) ^ (((2 * n) + 1) + 1) * ((Nat.fib ((2 * n) + 1) : Nat) : Int) :=
      Finset.sum_Icc_succ_top hab2 _
    simp only [Cfun] at ih ⊢
    rw [hstep, step1, step2]
    have e2 : ((2 * n) + 1) + 1 = 2 * n + 2 := by omega
    rw [e2]
    have p1 : (-1 : Int) ^ ((2 * n + 2) + 1) = -1 := Odd.neg_one_pow ⟨n + 1, by ring⟩
    have p2 : (-1 : Int) ^ (2 * n + 2) = 1 := Even.neg_one_pow ⟨n + 1, by ring⟩
    rw [p1, p2]
    have g1 :
        (Nat.fib (2 * n + 2) : Int) = (Nat.fib (2 * n) : Int) + (Nat.fib (2 * n + 1) : Int) := by
      have h := Nat.fib_add_two (n := 2 * n)
      exact_mod_cast h
    have g2 :
        (Nat.fib (2 * n + 3) : Int) =
          (Nat.fib (2 * n + 1) : Int) + (Nat.fib (2 * n + 2) : Int) := by
      have h := Nat.fib_add_two (n := 2 * n + 1)
      have he : (2 * n + 1) + 2 = 2 * n + 3 := by omega
      have he2 : (2 * n + 1) + 1 = 2 * n + 2 := by omega
      rw [he, he2] at h
      exact_mod_cast h
    have h2b' : 2 * n + 2 + 1 = 2 * n + 3 := by omega
    rw [h2b']
    simp only [ih]
    linear_combination g2 - g1

private theorem Mpow_entries : ∀ n : Nat,
    ((Mmat ^ (n+1)) 1 0 = 1 - (Nat.fib (2*n+1) : Int)) ∧
    ((Mmat ^ (n+1)) 1 1 = (Nat.fib (2*n+1) : Int) - (Nat.fib (2*n) : Int) - 1) ∧
    ((Mmat ^ (n+1)) 1 2 = (Nat.fib (2*n) : Int) + 1) ∧
    ((Mmat ^ (n+1)) 2 0 = 1 - (Nat.fib (2*n+3) : Int)) ∧
    ((Mmat ^ (n+1)) 2 1 = (Nat.fib (2*n+1) : Int) - 1) ∧
    ((Mmat ^ (n+1)) 2 2 = (Nat.fib (2*n+2) : Int) + 1) := by
  have m00 : Mmat 0 0 = 2 := by decide
  have m01 : Mmat 0 1 = -1 := by decide
  have m02 : Mmat 0 2 = 0 := by decide
  have m10 : Mmat 1 0 = 0 := by decide
  have m11 : Mmat 1 1 = 0 := by decide
  have m12 : Mmat 1 2 = 1 := by decide
  have m20 : Mmat 2 0 = -1 := by decide
  have m21 : Mmat 2 1 = 0 := by decide
  have m22 : Mmat 2 2 = 2 := by decide
  intro n
  induction n with
  | zero =>
    have e0 : (0 : Nat) + 1 = 1 := rfl
    rw [e0, pow_one]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
  | succ n ih =>
    obtain ⟨h10, h11, h12, h20, h21, h22⟩ := ih
    have hpow : Mmat ^ (n + 1 + 1) = Mmat ^ (n + 1) * Mmat := pow_succ _ _
    have hn0 : 2 * (n + 1) = 2 * n + 2 := by omega
    have k1 : 2 * n + 2 + 1 = 2 * n + 3 := by omega
    have k2 : 2 * n + 2 + 2 = 2 * n + 4 := by omega
    have k3 : 2 * n + 2 + 3 = 2 * n + 5 := by omega
    have g1 :
        (Nat.fib (2 * n + 2) : Int) = (Nat.fib (2 * n) : Int) + (Nat.fib (2 * n + 1) : Int) := by
      have h := Nat.fib_add_two (n := 2 * n)
      exact_mod_cast h
    have g2 :
        (Nat.fib (2 * n + 3) : Int) =
          (Nat.fib (2 * n + 1) : Int) + (Nat.fib (2 * n + 2) : Int) := by
      have h := Nat.fib_add_two (n := 2 * n + 1)
      have he : (2 * n + 1) + 2 = 2 * n + 3 := by omega
      have he2 : (2 * n + 1) + 1 = 2 * n + 2 := by omega
      rw [he, he2] at h
      exact_mod_cast h
    have g3 :
        (Nat.fib (2 * n + 4) : Int) =
          (Nat.fib (2 * n + 2) : Int) + (Nat.fib (2 * n + 3) : Int) := by
      have h := Nat.fib_add_two (n := 2 * n + 2)
      have he : (2 * n + 2) + 2 = 2 * n + 4 := by omega
      have he2 : (2 * n + 2) + 1 = 2 * n + 3 := by omega
      rw [he, he2] at h
      exact_mod_cast h
    have g4 :
        (Nat.fib (2 * n + 5) : Int) =
          (Nat.fib (2 * n + 3) : Int) + (Nat.fib (2 * n + 4) : Int) := by
      have h := Nat.fib_add_two (n := 2 * n + 3)
      have he : (2 * n + 3) + 2 = 2 * n + 5 := by omega
      have he2 : (2 * n + 3) + 1 = 2 * n + 4 := by omega
      rw [he, he2] at h
      exact_mod_cast h
    rw [hpow]
    simp only [hn0, k1, k2, k3, Matrix.mul_apply, Fin.sum_univ_three,
      m00, m01, m02, m10, m11, m12, m20, m21, m22, h10, h11, h12, h20, h21, h22]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination g2 + g1
    · linear_combination -g2
    · linear_combination -g1
    · linear_combination g4 + g3
    · ring
    · linear_combination -g3 - g2

private theorem fibpos : ∀ m : Nat, 1 ≤ Nat.fib (m + 1) := by
  intro m
  induction m with
  | zero => decide
  | succ m ih =>
    have e : m + 1 + 1 = m + 2 := by omega
    rw [e, Nat.fib_add_two]
    omega

private theorem Q'_fib : ∀ n : Nat,
    (Nat.fib (2*n+1):Int)^2 - (Nat.fib (2*n+1):Int)*(Nat.fib (2*n):Int)
      - ((Nat.fib (2*n):Int))^2 = 1 := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    have hb : 2*(n+1) = 2*n+2 := by omega
    have c1 : 2*n+2+1 = 2*n+3 := by omega
    have g1 : (Nat.fib (2*n+2):Int) = (Nat.fib (2*n):Int)+(Nat.fib (2*n+1):Int) := by
      have h := Nat.fib_add_two (n := 2*n)
      exact_mod_cast h
    have g2 : (Nat.fib (2*n+3):Int) = (Nat.fib (2*n+1):Int)+(Nat.fib (2*n+2):Int) := by
      have h := Nat.fib_add_two (n := 2*n+1)
      have he : (2*n+1)+2 = 2*n+3 := by omega
      have he2 : (2*n+1)+1 = 2*n+2 := by omega
      rw [he, he2] at h
      exact_mod_cast h
    simp only [hb, c1, g1, g2]
    linear_combination ih

private theorem main_unfolded (k : Nat) (hk : 0 < k) :
    abs (Matrix.det
          (((Mmat ^ k) - 1).submatrix (Fin.succAbove (0 : Fin 3))
            (Fin.succAbove (0 : Fin 3)))) =
      -(Cfun (2 * k - 2) + 1) * Cfun (2 * k) + Cfun (2 * k - 1) ^ 2 := by
  cases k with
  | zero => omega
  | succ n =>
    have hb : 2 * (n + 1) = 2 * n + 2 := by omega
    have e0 : 2 * (n + 1) - 2 = 2 * n := by omega
    have e1 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    have ck1 : 2 * n + 2 + 1 = 2 * n + 3 := by omega
    rw [e0, e1, hb]
    have c0 := C_even_all n
    have c1 := C_odd n
    have c2 := C_even_all (n + 1)
    rw [hb] at c2
    rw [ck1] at c2
    rw [c0, c1, c2]
    have hM := Mpow_entries n
    obtain ⟨_, h11, h12, _, h21, h22⟩ := hM
    have s00 : Fin.succAbove (0 : Fin 3) (0 : Fin 2) = 1 := by decide
    have s11 : Fin.succAbove (0 : Fin 3) (1 : Fin 2) = 2 := by decide
    have o11 : (1 : Matrix (Fin 3) (Fin 3) Int) 1 1 = 1 := by decide
    have o12 : (1 : Matrix (Fin 3) (Fin 3) Int) 1 2 = 0 := by decide
    have o21 : (1 : Matrix (Fin 3) (Fin 3) Int) 2 1 = 0 := by decide
    have o22 : (1 : Matrix (Fin 3) (Fin 3) Int) 2 2 = 1 := by decide
    have n00 : (((Mmat ^ (n + 1)) - 1).submatrix (Fin.succAbove (0 : Fin 3))
        (Fin.succAbove (0 : Fin 3))) 0 0 = (Mmat ^ (n + 1)) 1 1 - 1 := by
      simp only [Matrix.submatrix_apply, s00, Matrix.sub_apply, o11]
    have n01 : (((Mmat ^ (n + 1)) - 1).submatrix (Fin.succAbove (0 : Fin 3))
        (Fin.succAbove (0 : Fin 3))) 0 1 = (Mmat ^ (n + 1)) 1 2 := by
      simp only [Matrix.submatrix_apply, s00, s11, Matrix.sub_apply, o12, sub_zero]
    have n10 : (((Mmat ^ (n + 1)) - 1).submatrix (Fin.succAbove (0 : Fin 3))
        (Fin.succAbove (0 : Fin 3))) 1 0 = (Mmat ^ (n + 1)) 2 1 := by
      simp only [Matrix.submatrix_apply, s11, s00, Matrix.sub_apply, o21, sub_zero]
    have n11 : (((Mmat ^ (n + 1)) - 1).submatrix (Fin.succAbove (0 : Fin 3))
        (Fin.succAbove (0 : Fin 3))) 1 1 = (Mmat ^ (n + 1)) 2 2 - 1 := by
      simp only [Matrix.submatrix_apply, s11, Matrix.sub_apply, o22]
    rw [Matrix.det_fin_two, n00, n01, n10, n11, h11, h12, h21, h22]
    have g1 : (Nat.fib (2 * n + 2) : Int)
        = (Nat.fib (2 * n) : Int) + (Nat.fib (2 * n + 1) : Int) := by
      have h := Nat.fib_add_two (n := 2 * n)
      exact_mod_cast h
    have g2 : (Nat.fib (2 * n + 3) : Int)
        = (Nat.fib (2 * n + 1) : Int) + (Nat.fib (2 * n + 2) : Int) := by
      have h := Nat.fib_add_two (n := 2 * n + 1)
      have he : (2 * n + 1) + 2 = 2 * n + 3 := by omega
      have he2 : (2 * n + 1) + 1 = 2 * n + 2 := by omega
      rw [he, he2] at h
      exact_mod_cast h
    have hq := Q'_fib n
    have hdet : ((Nat.fib (2*n+1):Int)-(Nat.fib (2*n):Int)-1-1)*((Nat.fib (2*n+2):Int)+1-1)
        - ((Nat.fib (2*n):Int)+1)*((Nat.fib (2*n+1):Int)-1)
        = -(-(((Nat.fib (2*n):Int)-(Nat.fib (2*n+1):Int)+1)+1)
            *((Nat.fib (2*n+2):Int)-(Nat.fib (2*n+3):Int)+1)
          + ((Nat.fib (2*n):Int)+1)^2) := by
      linear_combination ((Nat.fib (2*n+1):Int)-(Nat.fib (2*n):Int)-2) * g1
        - ((Nat.fib (2*n+1):Int)-(Nat.fib (2*n):Int)-2) * g2
    have hval : (-(((Nat.fib (2*n):Int)-(Nat.fib (2*n+1):Int)+1)+1)
            *((Nat.fib (2*n+2):Int)-(Nat.fib (2*n+3):Int)+1)
          + ((Nat.fib (2*n):Int)+1)^2)
        = (Nat.fib (2*n):Int) + 3*(Nat.fib (2*n+1):Int) - 2 := by
      simp only [g1, g2]
      linear_combination -hq
    have hF0 : (0:Int) ≤ (Nat.fib (2*n):Int) := by positivity
    have hF1 : (1:Int) ≤ (Nat.fib (2*n+1):Int) := by
      have h : 1 ≤ Nat.fib (2*n+1) := fibpos (2*n)
      exact_mod_cast h
    have hnn : (0:Int) ≤ (-(((Nat.fib (2*n):Int)-(Nat.fib (2*n+1):Int)+1)+1)
            *((Nat.fib (2*n+2):Int)-(Nat.fib (2*n+3):Int)+1)
          + ((Nat.fib (2*n):Int)+1)^2) := by
      linarith [hval, hF0, hF1]
    have hle : ((Nat.fib (2*n+1):Int)-(Nat.fib (2*n):Int)-1-1)*((Nat.fib (2*n+2):Int)+1-1)
        - ((Nat.fib (2*n):Int)+1)*((Nat.fib (2*n+1):Int)-1) ≤ 0 := by
      linarith [hdet, hnn]
    rw [abs_of_nonpos hle, hdet, neg_neg]

/-- **Oesper's determinant formula for three-strand weaving knots.** Let $k \ge 1$ be an integer,
let $F_i$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$), let
$C_j = \sum_{i=1}^{j} (-1)^{i+1} F_i$ for $j \ge 0$, and let $M$ be the $3 \times 3$ integer
matrix with rows $(2, -1, 0)$, $(0, 0, 1)$ and $(-1, 0, 2)$. Then the absolute value of the
determinant of the $2 \times 2$ matrix obtained from $M^k - I$ by deleting its first row and
first column equals $-(C_{2k-2} + 1) C_{2k} + C_{2k-1}^2$.

Here $M$ is the base-word matrix of the spiral knot $S(3, k, (1, -1))$, which is the
three-strand weaving knot $W(k, 3)$, and the left-hand side is the determinant of this knot:
the cofactor minors of $M^k - I$ agree up to sign, so taking the absolute value gives the
nonnegative knot determinant.

Source: Seong Ju Kim, Ryan Stees, and Laura Taalman, "Sequences of Spiral
Knot Determinants", Journal of Integer Sequences 19 (2016), Article 16.1.4,
lines 409-412:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Stees/stees4.tex
The formula is attributed to L. Oesper, "p-colorings of weaving knots"
(preprint).
Proves `Wanted` entry `oesper_weaving_three_determinant`.
-/
theorem oesper_weaving_three_determinant (k : Nat) (hk : 0 < k) :
    let C : Nat -> Int := fun j => Finset.sum (Finset.Icc 1 j)
      (fun i => (-1 : Int) ^ (i + 1) * Nat.fib i);
    let M : Matrix (Fin 3) (Fin 3) Int := !![2, -1, 0; 0, 0, 1; -1, 0, 2];
    abs (Matrix.det
          (((M ^ k) - 1).submatrix (Fin.succAbove (0 : Fin 3))
            (Fin.succAbove (0 : Fin 3)))) =
      -(C (2 * k - 2) + 1) * C (2 * k) + C (2 * k - 1) ^ 2 := by
  exact main_unfolded k hk

end MetaMathlibExt
