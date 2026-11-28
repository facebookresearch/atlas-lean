/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Int.ModEq
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.SecondOrderGenValueNeighbors
public import MathlibExt.NumberTheory.SecondOrderGenValueTrivialFamilies
public import MathlibExt.NumberTheory.SecondOrderMValue
public import MathlibExt.NumberTheory.SecondOrderMValueSmallNonneg
public import MathlibExt.NumberTheory.SecondOrderGenFunIntegerValuesExistsSmallSecondOrderMValueOfNeg

/-!
# Integer values of generating functions of `A_{n+1} = p A_n + A_{n-1}` (wanted statements)

Statements from Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a
Type of Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3. Throughout, `A_0 = a`, `A_1 = b`, `A_{n+1} = p A_n + A_{n-1}` with integers
`a, b, p`, `p ≠ 0`; the paper's standing assumption `(a, b) ≠ (0, 0)` is added where it is used.
For `p ≠ 0` the denominator `1 - p x - x²` has no rational root, so `A(x)` is defined on `ℚ`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Integer values propagate along a family.** Let $a, b, p$ be integers with $p \ne 0$, let
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ for rational $x$, and for integers $r, s$ let
$A^{(r,s)}$ be the two-sided integer sequence with $A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and
$A^{(r,s)}_{n+2} = pA^{(r,s)}_{n+1} + A^{(r,s)}_n$ for all integers $n$. If $r$ and $s$ are
coprime integers with $s \ne 0$ and $A(r/s)$ is an integer, then
$A(A^{(r,s)}_n / A^{(r,s)}_{n+1})$ is an integer for every integer $n$ with
$A^{(r,s)}_{n+1} \ne 0$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1 (`jis-2025-25.8.3-thm-1`). -/
public theorem_wanted secondOrderGenValue_family_integer (a b p : ℤ) (hp : p ≠ 0) (r s : ℤ)
    (hs : s ≠ 0)
    (hrs : Int.gcd r s = 1) (hint : ∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z)
    (n : ℤ) (hn : secondOrderBiSeq p r s (n + 1) ≠ 0) :
    ∃ z : ℤ, secondOrderGenValue a b p
      ((secondOrderBiSeq p r s n : ℚ) / secondOrderBiSeq p r s (n + 1)) = z

/-- **Algorithm for integer values of a second-order generating function.** Let $a, b, p$ be
integers with $p \ne 0$ and $(a, b) \ne (0, 0)$, let $A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$
for rational $x$, and for integers $r, s$ let $A^{(r,s)}$ be the two-sided integer sequence with
$A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and $A^{(r,s)}_{n+2} = pA^{(r,s)}_{n+1} + A^{(r,s)}_n$ for all
integers $n$. Put $E = abp^3 + (a^2 - b^2)p^2$, and let $B = E/(p^2 + 4)$ if $E \ge 0$ and
$B = -abp + b^2 - a^2$ if $E < 0$. (Soundness) If $M$ and $k$ are integers with $k \ne 0$ and
$M^2 = (kp - ap + b)^2 - 4k(a - k)$, then $A(x)$ is an integer for both
$x = (ap - kp - b + M)/(2k)$ and $x = (ap - kp - b - M)/(2k)$. (Completeness) If $x$ is a
rational number for which $A(x)$ is an integer, then at least one of the following holds: there
is an integer $n$ with $A^{(0,1)}_{n+1} \ne 0$ and $x = A^{(0,1)}_n / A^{(0,1)}_{n+1}$; there is
an integer $n$ with $A^{(-b,a)}_{n+1} \ne 0$ and $x = A^{(-b,a)}_n / A^{(-b,a)}_{n+1}$; or there
are integers $M, N, k$ with $M^2 \le B$, $M^2 + (p^2 + 2)MN + N^2 = E$, $k \ne 0$ and
$M^2 = (kp - ap + b)^2 - 4k(a - k)$, and a rational number
$x' \in \{(ap - kp - b + M)/(2k), (ap - kp - b - M)/(2k)\}$ such that $x$ lies in the family of
$x'$: writing $x' = u/v$ in lowest terms with $v > 0$, there is an integer $n$ with
$A^{(u,v)}_{n+1} \ne 0$ and $x = A^{(u,v)}_n / A^{(u,v)}_{n+1}$.

The bound $M^2 \le B$ is the condition $|M| \le \sqrt{B}$ of the source.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 3 (`jis-2025-25.8.3-thm-3`). -/
public theorem_wanted secondOrderGenValue_algorithm (a b p : ℤ) (hp : p ≠ 0) (hab : (a, b) ≠
    (0, 0)) :
    (∀ M k : ℤ, k ≠ 0 → M ^ 2 = (k * p - a * p + b) ^ 2 - 4 * k * (a - k) →
      ∀ x : ℚ, (x = (a * p - k * p - b + M) / (2 * k) ∨ x = (a * p - k * p - b - M) / (2 * k)) →
        ∃ z : ℤ, secondOrderGenValue a b p x = z) ∧
    ∀ x : ℚ, (∃ z : ℤ, secondOrderGenValue a b p x = z) →
      (∃ n : ℤ, secondOrderBiSeq p 0 1 (n + 1) ≠ 0 ∧
        x = (secondOrderBiSeq p 0 1 n : ℚ) / secondOrderBiSeq p 0 1 (n + 1)) ∨
      (∃ n : ℤ, secondOrderBiSeq p (-b) a (n + 1) ≠ 0 ∧
        x = (secondOrderBiSeq p (-b) a n : ℚ) / secondOrderBiSeq p (-b) a (n + 1)) ∨
      ∃ M N k : ℤ,
        ((M : ℝ) ^ 2 ≤ if 0 ≤ a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2 then
          ((a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2 : ℤ) : ℝ) / (p ^ 2 + 4)
          else ((-a * b * p + b ^ 2 - a ^ 2 : ℤ) : ℝ)) ∧
        M ^ 2 + (p ^ 2 + 2) * M * N + N ^ 2 = a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2 ∧
        k ≠ 0 ∧ M ^ 2 = (k * p - a * p + b) ^ 2 - 4 * k * (a - k) ∧
        ∃ x' : ℚ, (x' = (a * p - k * p - b + M) / (2 * k) ∨
          x' = (a * p - k * p - b - M) / (2 * k)) ∧ IsInSecondOrderFamily p x' x

/-- **Rationals where $x/(1 - px - x^2)$ is an integer.** Let $p \ne 0$ be an integer, let
$G(x) = \frac{x}{1 - px - x^2}$ for rational $x$, and let $A^{(0,1)}$ be the two-sided integer
sequence with $A^{(0,1)}_0 = 0$, $A^{(0,1)}_1 = 1$ and
$A^{(0,1)}_{n+2} = pA^{(0,1)}_{n+1} + A^{(0,1)}_n$ for all integers $n$. Then the set of rational
numbers $x$ for which $G(x)$ is an integer is
$\{A^{(0,1)}_n / A^{(0,1)}_{n+1} : n \in \mathbb{Z},\ n \ne -1\}$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Corollary 13 (`jis-2025-25.8.3-cor-13`). -/
public theorem_wanted secondOrderGenValue_zero_one_integer_set (p : ℤ) (hp : p ≠ 0) :
    {x : ℚ | ∃ z : ℤ, secondOrderGenValue 0 1 p x = z} =
      {x | ∃ n : ℤ, n ≠ -1 ∧
        x = (secondOrderBiSeq p 0 1 n : ℚ) / secondOrderBiSeq p 0 1 (n + 1)}

/-- **Integer values of $x/(1 - px - x^2)$ come from Lucas ratios.** Let $p \ne 0$ be an integer,
let $(U_n)_{n \ge 0}$ be the Lucas sequence $U(p, -1)$, so $U_0 = 0$, $U_1 = 1$ and
$U_{n+2} = pU_{n+1} + U_n$, and let $G(x) = \frac{x}{1 - px - x^2}$ for rational $x$. Then
$G(U_n/U_{n+1})$ is an integer for every natural number $n$; and if $G(x) = k$ for a rational
number $x$ and an integer $k$, then $G(U_n/U_{n+1}) = k$ for some natural number $n$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Corollary 14 (`jis-2025-25.8.3-cor-14`). -/
public theorem_wanted secondOrderGenValue_lucasU (p : ℤ) (hp : p ≠ 0) :
    (∀ n : ℕ, ∃ z : ℤ, secondOrderGenValue 0 1 p
      ((lucasU ⟨p, -1, by norm_num⟩ n : ℚ) / lucasU ⟨p, -1, by norm_num⟩ (n + 1)) = z) ∧
    ∀ (x : ℚ) (k : ℤ), secondOrderGenValue 0 1 p x = k → ∃ n : ℕ, secondOrderGenValue 0 1 p
      ((lucasU ⟨p, -1, by norm_num⟩ n : ℚ) / lucasU ⟨p, -1, by norm_num⟩ (n + 1)) = k

/-- **Integer values of $(1 - px + x)/(1 - px - x^2)$.** Let $p \ne 0$ be an integer, let
$A(x) = \frac{1 - px + x}{1 - px - x^2}$ for rational $x$, and for integers $r, s$ let $A^{(r,s)}$
be the two-sided integer sequence with $A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and
$A^{(r,s)}_{n+2} = pA^{(r,s)}_{n+1} + A^{(r,s)}_n$ for all integers $n$. If $x$ is a rational
number for which $A(x)$ is an integer, then there is an integer $n$ with $A^{(0,1)}_{n+1} \ne 0$
and $x = A^{(0,1)}_n / A^{(0,1)}_{n+1}$, or there is an integer $n$ with $A^{(-1,1)}_{n+1} \ne 0$
and $x = A^{(-1,1)}_n / A^{(-1,1)}_{n+1}$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Corollary 15 (`jis-2025-25.8.3-cor-15`). -/
public theorem_wanted secondOrderGenValue_one_one_families (p : ℤ) (hp : p ≠ 0) (x : ℚ)
    (hx : ∃ z : ℤ, secondOrderGenValue 1 1 p x = z) :
    (∃ n : ℤ, secondOrderBiSeq p 0 1 (n + 1) ≠ 0 ∧
      x = (secondOrderBiSeq p 0 1 n : ℚ) / secondOrderBiSeq p 0 1 (n + 1)) ∨
    ∃ n : ℤ, secondOrderBiSeq p (-1) 1 (n + 1) ≠ 0 ∧
      x = (secondOrderBiSeq p (-1) 1 n : ℚ) / secondOrderBiSeq p (-1) 1 (n + 1)

end

end MetaMathlibExt
