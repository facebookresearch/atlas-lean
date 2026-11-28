/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-!
# Polygonal numbers

This file formalizes the polygonal-number family from the source cited below.

The source defines, for `m = 3, 4, ...` and `n = 0, 1, 2, ...`,
`p_m(n) = (m - 2) * C(n, 2) + n`.

The source's geometric polygonal interpretation assumes `3 ≤ s`.
The Lean definition below is the total natural-number extension of that
binomial formula to all `s : ℕ`, using `Nat.choose` so no unintended
truncated-subtraction semantics enter the definition itself.

## References

* Zhi-Wei Sun, *On universal sums of polygonal numbers*, Sci. China Math. 58 (2015), 1367–1396.
* `Nat.le_polygonalNumber` and `Nat.polygonalNumber_mono` use the proofs of
  [`polygonal_ge` and `polygonal_mono`](https://github.com/facebookresearch/atlas-lean/blob/9d8271ad4f924cdcdd560e3f0a65c9149fb2daaa/MathlibExt/NumberTheory/PracticalPolygonalSumsPracticalAddPolygonalExceptions.lean#L64-L74).
-/

namespace Nat

/-- Doubling identity underlying the square, pentagonal, and hexagonal forms. -/
private theorem two_choose_add (n : ℕ) : 2 * (Nat.choose n 2) + n = n ^ 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hpascal : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
      simpa [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ n 1
    have hsq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega

@[expose] public section

/-- **Polygonal numbers.** For natural numbers $s$ and $n$, the $n$-th $s$-gonal number is
$p_s(n) = (s - 2)\binom{n}{2} + n$, where $s - 2$ is truncated subtraction of natural numbers
(so it is $0$ when $s < 2$).

The polygonal interpretation assumes $s \ge 3$; this definition extends the formula to every
natural number $s$. -/
def polygonalNumber (s n : ℕ) : ℕ := (s - 2) * Nat.choose n 2 + n

/-- The binomial formula for `polygonalNumber`, with natural subtraction in `s - 2`. -/
theorem polygonalNumber_eq (s n : ℕ) :
    polygonalNumber s n = (s - 2) * n.choose 2 + n := rfl

/-- For all natural numbers `s` and `n`, the `n`-th `s`-gonal number is at least `n`. -/
theorem le_polygonalNumber (s n : ℕ) : n ≤ polygonalNumber s n := by
  rw [polygonalNumber_eq]
  exact Nat.le_add_left n ((s - 2) * n.choose 2)

/-- For natural numbers `s`, `a`, and `b` with `a ≤ b`, the `a`-th `s`-gonal number is at most
   the `b`-th. -/
theorem polygonalNumber_mono (s : ℕ) {a b : ℕ} (h : a ≤ b) :
    polygonalNumber s a ≤ polygonalNumber s b := by
  simp only [polygonalNumber_eq]
  have hC : a.choose 2 ≤ b.choose 2 := Nat.choose_le_choose 2 h
  have hmul : (s - 2) * a.choose 2 ≤ (s - 2) * b.choose 2 :=
    Nat.mul_le_mul_left (s - 2) hC
  exact Nat.add_le_add hmul h

/-- **Polygonal numbers at zero.** For every natural number $s$, $p_s(0) = 0$, where $p_s(n)$ is
the $n$-th $s$-gonal number.

The source considers only $s \ge 3$; the value holds for the extension of the formula to every
natural number $s$. -/
@[simp] theorem polygonalNumber_zero (s : ℕ) : polygonalNumber s 0 = 0 := by
  have h : Nat.choose 0 2 = 0 := by decide
  simp [polygonalNumber, h]

/-- **Polygonal numbers at one.** For every natural number $s$, $p_s(1) = 1$, where $p_s(n)$ is
the $n$-th $s$-gonal number.

The source considers only $s \ge 3$; the value holds for the extension of the formula to every
natural number $s$. -/
@[simp] theorem polygonalNumber_one (s : ℕ) : polygonalNumber s 1 = 1 := by
  have h : Nat.choose 1 2 = 0 := by decide
  simp only [polygonalNumber, h]
  simp

/-- **Polygonal numbers at two.** For every natural number $s \ge 3$, $p_s(2) = s$, where $p_s(n)$
is the $n$-th $s$-gonal number. -/
theorem polygonalNumber_at_two (s : ℕ) (hs : 3 ≤ s) : polygonalNumber s 2 = s := by
  have hc : Nat.choose 2 2 = 1 := by decide
  simp only [polygonalNumber, hc]
  omega

/-- **Polygonal numbers at three.** For every natural number $s \ge 3$, $p_s(3) = 3s - 3$, where
$p_s(n)$ is the $n$-th $s$-gonal number. -/
theorem polygonalNumber_at_three (s : ℕ) (hs : 3 ≤ s) :
    polygonalNumber s 3 = 3 * s - 3 := by
  have hc : Nat.choose 3 2 = 3 := by decide
  simp only [polygonalNumber, hc]
  omega

/-- **Polygonal numbers at four.** For every natural number $s \ge 3$, $p_s(4) = 6s - 8$, where
$p_s(n)$ is the $n$-th $s$-gonal number. -/
theorem polygonalNumber_at_four (s : ℕ) (hs : 3 ≤ s) :
    polygonalNumber s 4 = 6 * s - 8 := by
  have hc : Nat.choose 4 2 = 6 := by decide
  simp [polygonalNumber, hc]
  omega

/-- **Closed form of the triangular numbers.** For every natural number $n$, the $n$-th triangular
number is $p_3(n) = \frac{n(n + 1)}{2}$, where $p_s(n)$ is the $n$-th $s$-gonal number.

The quotient is exact, since $n(n + 1)$ is even. -/
theorem polygonalNumber_three (n : ℕ) :
    polygonalNumber 3 n = n * (n + 1) / 2 := by
  have h4 : 2 * (Nat.choose n 2) + n = n ^ 2 := two_choose_add n
  have hmul : n * (n + 1) = n ^ 2 + n := by ring
  simp [polygonalNumber]
  omega

/-- **Square numbers as polygonal numbers.** For every natural number $n$, the $n$-th square
number is $p_4(n) = n^2$, where $p_s(n)$ is the $n$-th $s$-gonal number. -/
theorem polygonalNumber_four (n : ℕ) : polygonalNumber 4 n = n ^ 2 := by
  simpa [polygonalNumber] using two_choose_add n

/-- **Closed form of the pentagonal numbers.** For every natural number $n$, the $n$-th pentagonal
number is $p_5(n) = \frac{3n^2 - n}{2}$, where $p_s(n)$ is the $n$-th $s$-gonal number.

The quotient is exact, since $3n^2 - n = n(3n - 1)$ is even. -/
theorem polygonalNumber_five (n : ℕ) :
    polygonalNumber 5 n = (3 * n ^ 2 - n) / 2 := by
  have h4 : 2 * (Nat.choose n 2) + n = n ^ 2 := two_choose_add n
  simp [polygonalNumber]
  omega

/-- **Closed form of the hexagonal numbers.** For every natural number $n$, the $n$-th hexagonal
number is $p_6(n) = 2n^2 - n$, where $p_s(n)$ is the $n$-th $s$-gonal number. -/
theorem polygonalNumber_six (n : ℕ) :
    polygonalNumber 6 n = 2 * n ^ 2 - n := by
  have h4 : 2 * (Nat.choose n 2) + n = n ^ 2 := two_choose_add n
  simp [polygonalNumber]
  omega

end

end Nat
