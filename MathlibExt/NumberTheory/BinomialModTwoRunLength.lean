/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Fin.Rev

/-!
# Run length transforms and the companion matrix of a linear recurrence

Following Rampersad and Wiebe, the companion matrix advances the vector of consecutive terms
of a linear recurrence. Its powers recover the sequence from its initial values.
-/

@[expose] public section

namespace MetaMathlibExt

open Matrix

/-- **Run lengths of a digit list.** Given a list $b_1, \dots, b_k$ of natural numbers (binary
digits) and a natural number $c$, this is the list, in order of occurrence, of the lengths of the
maximal runs of $1$s in the sequence consisting of $c$ ones followed by $b_1, \dots, b_k$, where
every digit other than $1$ ends a run.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Definition 1. -/
public def bitRunLengths : List ℕ → ℕ → List ℕ
  | [], c => if c = 0 then [] else [c]
  | b :: bs, c =>
    if b = 1 then bitRunLengths bs (c + 1)
    else if c = 0 then bitRunLengths bs 0 else c :: bitRunLengths bs 0

/-- **Binary run lengths.** For a natural number $n$, the binary run lengths of $n$ form the list
of the lengths of the maximal runs of $1$s in the binary expansion of $n$, in the order in which
the runs occur when the digits are read from the least significant one. This is the paper's list
$\mathcal{L}(n)$, whose order does not matter there; for $n = 0$ the list is empty.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Definition 1. -/
public def binaryRunLengths (n : ℕ) : List ℕ :=
  bitRunLengths (Nat.digits 2 n) 0

/-- **Run length transform.** For a sequence $S : \mathbb{N} \to \mathbb{Z}$, the run length
transform of $S$ is the sequence $T : \mathbb{N} \to \mathbb{Z}$ given by
$T(n) = \prod_{\ell \in \mathcal{L}(n)} S(\ell)$, where $\mathcal{L}(n)$ is the list of the
lengths of the maximal runs of $1$s in the binary expansion of $n$, so that each run contributes
one factor.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Definition 1. -/
public def runLengthTransform (S : ℕ → ℤ) (n : ℕ) : ℤ :=
  ((binaryRunLengths n).map S).prod

/-- **Run length transform at zero.** For every sequence $S : \mathbb{N} \to \mathbb{Z}$, the run
length transform of $S$ takes the value $1$ at $0$, since $0$ has no runs of $1$s in binary.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Definition 1. -/
public theorem runLengthTransform_zero (S : ℕ → ℤ) : runLengthTransform S 0 = 1 := by
  simp [runLengthTransform, binaryRunLengths, bitRunLengths]

/-- **Run length transform at eleven.** For every sequence $S : \mathbb{N} \to \mathbb{Z}$, the run
length transform $T$ of $S$ satisfies $T(11) = S(1) S(2)$: in binary $11$ is $1011$, whose maximal
runs of $1$s have lengths $2$ and $1$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, example after Definition 1. -/
public theorem runLengthTransform_eleven (S : ℕ → ℤ) : runLengthTransform S 11 = S 1 * S 2 := by
  have hd : Nat.digits 2 11 = [1, 1, 0, 1] := by norm_num
  have h : binaryRunLengths 11 = [2, 1] := by
    rw [binaryRunLengths, hd]
    decide
  rw [runLengthTransform, h]
  simp [mul_comm]

-- The initial column already contains S(0), so the matrix identity holds for any S(0).
set_option linter.unusedVariables false in
/-- **Linear recurrences via powers of the companion matrix.** Let $r$ be a natural number, let
$d_0, \dots, d_r$ be integers, and let $S : \mathbb{N} \to \mathbb{Z}$ satisfy $S(0) = 1$ and
$S(m + 1) = d_0 S(m) + d_1 S(m - 1) + \dots + d_r S(m - r)$ for every $m \ge r$. Let $\gamma(1)$
be the $(r + 1) \times (r + 1)$ integer matrix with rows and columns indexed by $0, \dots, r$
whose row $i < r$ has a $1$ in column $i + 1$ and zeros elsewhere, and whose last row is
$(d_r, d_{r-1}, \dots, d_0)$. With $v = (1, 0, \dots, 0)$ and $w = (S(0), \dots, S(r))^{T}$,
we have $S(n) = v \, \gamma(1)^n \, w$ for every natural number $n$.

The values $S(1), \dots, S(r)$ are arbitrary.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Lemma 1. -/
public theorem linearRecurrence_eq_companion_pow (r : ℕ) (d : Fin (r + 1) → ℤ)
    (S : ℕ → ℤ) (hS0 : S 0 = 1)
    (hrec : ∀ m, r ≤ m → S (m + 1) = ∑ i : Fin (r + 1), d i * S (m - i)) (n : ℕ) :
    S n = Pi.single 0 1 ⬝ᵥ
      ((Matrix.of fun i j : Fin (r + 1) =>
          if (i : ℕ) < r then (if (j : ℕ) = i + 1 then 1 else 0) else d (Fin.rev j)) ^ n *ᵥ
        fun i => S i) := by
  set A := Matrix.of _
  have hpow (k : ℕ) :
      A ^ k *ᵥ (fun i => S i) = fun i : Fin (r + 1) => S (k + i) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih]
      funext i
      rw [mulVec_apply_eq_sum]
      by_cases hi : (i : ℕ) < r
      · let j : Fin (r + 1) := ⟨i + 1, by omega⟩
        have hj (t : Fin (r + 1)) : (t : ℕ) = i + 1 ↔ t = j :=
          (Fin.ext_iff (a := t) (b := j)).symm
        simp [A, hi, hj, ite_mul, j, Nat.add_assoc, Nat.add_comm 1]
      · have hlast : k + 1 + (i : ℕ) = k + r + 1 := by omega
        simp only [A, of_apply, ite_eq_right hi]
        rw [hlast, hrec (k + r) (by omega)]
        refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
        simp only [Fin.revPerm_apply, Fin.val_rev]
        congr 2
        omega
  simp [hpow]

end MetaMathlibExt
