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

/-- **Generating function of the recurrence $A_{n+1} = pA_n + A_{n-1}$.** For integers $a$, $b$,
$p$ and a rational number $x$, $A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$, with the convention
that a fraction with denominator $0$ is $0$. As a rational function, $A$ is the generating function
$\sum_{n \ge 0} A_n x^n$ of the sequence with $A_0 = a$, $A_1 = b$ and $A_{n+1} = pA_n + A_{n-1}$;
for $p \ne 0$ the denominator $1 - px - x^2$ has no rational root.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Section 2. -/
def secondOrderGenValue (a b p : ℤ) (x : ℚ) : ℚ :=
  (a * (1 - p * x) + b * x) / (1 - p * x - x ^ 2)

/-- **Value of the generating function at zero.** For all integers $a, b, p$, the function
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ on the rationals satisfies $A(0) = a$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, proof of Theorem 2. -/
theorem secondOrderGenValue_zero (a b p : ℤ) : secondOrderGenValue a b p 0 = a := by
  simp [secondOrderGenValue]

/-- **Forward part of a second-order sequence.** For integers $p, r, s$, this is the sequence
$(A^{(r,s)}_n)_{n \ge 0}$ of integers with $A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and
$A^{(r,s)}_{n+2} = pA^{(r,s)}_{n+1} + A^{(r,s)}_n$ for every natural number $n$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
def secondOrderFwd (p r s : ℤ) : ℕ → ℤ
  | 0 => r
  | 1 => s
  | n + 2 => p * secondOrderFwd p r s (n + 1) + secondOrderFwd p r s n

/-- **Backward part of the two-sided sequence.** For integers $p$, $r$ and $s$, the backward
part is the sequence $(B_k)_{k \ge 0}$ with $B_0 = s$, $B_1 = r$ and $B_{k+2} = B_k - pB_{k+1}$.
Thus $B_k$ is the term of index $1 - k$ of the two-sided sequence with $A_0 = r$, $A_1 = s$ and
$A_{n+1} = pA_n + A_{n-1}$, computed backwards by $A_n = A_{n+2} - pA_{n+1}$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
def secondOrderBwd (p r s : ℤ) : ℕ → ℤ
  | 0 => s
  | 1 => r
  | n + 2 => secondOrderBwd p r s n - p * secondOrderBwd p r s (n + 1)

/-- **Two-sided second-order sequence.** For integers $p$, $r$ and $s$, the two-sided sequence
$(A^{(r,s)}_n)_{n \in \mathbb{Z}}$ for $p$ is the integer sequence indexed by $\mathbb{Z}$ with
$A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and $A^{(r,s)}_{n+1} = pA^{(r,s)}_n + A^{(r,s)}_{n-1}$ for
every integer $n$.

The paper's forward rule "if $n > 1$" is read as $n \ge 1$, as the definition of $A_2$ requires.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
def secondOrderBiSeq (p r s : ℤ) : ℤ → ℤ
  | (n : ℕ) => secondOrderFwd p r s n
  | Int.negSucc n => secondOrderBwd p r s (n + 2)

/-- **First values of the two-sided sequence.** For all integers $p$, $r$, $s$, the two-sided
sequence $(A^{(r,s)}_n)_{n \in \mathbb{Z}}$ for $p$ with initial values $r$ and $s$ satisfies
$A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$, $A^{(r,s)}_2 = ps + r$ and $A^{(r,s)}_{-1} = s - pr$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
theorem secondOrderBiSeq_small (p r s : ℤ) :
    secondOrderBiSeq p r s 0 = r ∧ secondOrderBiSeq p r s 1 = s ∧
      secondOrderBiSeq p r s 2 = p * s + r ∧ secondOrderBiSeq p r s (-1) = s - p * r := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  show secondOrderBwd p r s 2 = s - p * r
  rfl

/-- **First initial value of the two-sided sequence.** For all integers $p$, $r$, $s$, the
two-sided sequence $(A^{(r,s)}_n)_{n \in \mathbb{Z}}$ for $p$ with initial values $r$ and $s$
satisfies $A^{(r,s)}_0 = r$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
@[simp] theorem secondOrderBiSeq_zero (p r s : ℤ) : secondOrderBiSeq p r s 0 = r := rfl

/-- **Second initial value of the two-sided sequence.** For all integers $p$, $r$, $s$, the
two-sided sequence $(A^{(r,s)}_n)_{n \in \mathbb{Z}}$ for $p$ with initial values $r$ and $s$
satisfies $A^{(r,s)}_1 = s$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
@[simp] theorem secondOrderBiSeq_one (p r s : ℤ) : secondOrderBiSeq p r s 1 = s := rfl

/-- **The two-sided sequence satisfies its recurrence at every index.** Let $p$, $r$, $s$ be
integers and $(A^{(r,s)}_n)_{n \in \mathbb{Z}}$ the two-sided sequence for $p$ with initial values
$A^{(r,s)}_0 = r$ and $A^{(r,s)}_1 = s$. Then
$A^{(r,s)}_{n+2} = pA^{(r,s)}_{n+1} + A^{(r,s)}_n$ for every integer $n$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
theorem secondOrderBiSeq_add_two (p r s : ℤ) (n : ℤ) :
    secondOrderBiSeq p r s (n + 2) =
      p * secondOrderBiSeq p r s (n + 1) + secondOrderBiSeq p r s n := by
  rcases n with m | m
  · show secondOrderFwd p r s (m + 2) = p * secondOrderFwd p r s (m + 1) + secondOrderFwd p r s m
    rfl
  · rcases m with _ | _ | k
    · show secondOrderFwd p r s 1 = p * secondOrderFwd p r s 0 + secondOrderBwd p r s 2
      simp only [secondOrderFwd, secondOrderBwd]
      ring
    · show secondOrderFwd p r s 0 = p * secondOrderBwd p r s 2 + secondOrderBwd p r s 3
      simp only [secondOrderFwd, secondOrderBwd]
      ring
    · have h2 : Int.negSucc (k + 2) + 2 = Int.negSucc k := by omega
      have h1 : Int.negSucc (k + 2) + 1 = Int.negSucc (k + 1) := by omega
      rw [h2, h1]
      have e : secondOrderBwd p r s (k + 4) =
          secondOrderBwd p r s (k + 2) - p * secondOrderBwd p r s (k + 3) := rfl
      show secondOrderBwd p r s (k + 2) =
        p * secondOrderBwd p r s (k + 3) + secondOrderBwd p r s (k + 4)
      rw [e]
      ring

/-- **The quantity $M(r, s)$ for the recurrence $A_{n+1} = pA_n + A_{n-1}$.** For integers $a$,
$b$, $p$, $r$, $s$, $M(r, s) = \frac{br^2 + bs^2 - apr^2 + 2ars}{s^2 - prs - r^2}$, a rational
number, with the convention that a fraction with denominator $0$ is $0$.

When $s \ne 0$ and $s^2 - prs - r^2 \ne 0$, write $k = A(r/s)$, where
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ is the generating function of the sequence with
$A_0 = a$, $A_1 = b$ and $A_{n+1} = pA_n + A_{n-1}$; then
$M(r, s)^2 = (kp + b - ap)^2 - 4k(a - k)$, that is,
$M(r, s) = \pm\sqrt{(kp + b - ap)^2 - 4k(a - k)}$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Section 2 (before Lemma 8). -/
def secondOrderMValue (a b p r s : ℤ) : ℚ :=
  (b * r ^ 2 + b * s ^ 2 - a * p * r ^ 2 + 2 * a * r * s) / (s ^ 2 - p * r * s - r ^ 2)

/-- **Value of $M$ at $(0, 1)$.** For all integers $a$, $b$, $p$, the quantity
$M(r, s) = \frac{br^2 + bs^2 - apr^2 + 2ars}{s^2 - prs - r^2}$ satisfies $M(0, 1) = b$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Section 2. -/
theorem secondOrderMValue_zero_one (a b p : ℤ) : secondOrderMValue a b p 0 1 = b := by
  simp [secondOrderMValue]

/-- **Family generated by a rational number.** Let $p$ be an integer and $x_0$ a rational number,
written $x_0 = r/s$ in lowest terms with $s > 0$, and let $(A^{(r,s)}_n)_{n \in \mathbb{Z}}$ be
the two-sided sequence with $A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and
$A^{(r,s)}_{n+1} = pA^{(r,s)}_n + A^{(r,s)}_{n-1}$. A rational number $x$ belongs to the family
generated by $x_0$ when there is an integer $n$ with $A^{(r,s)}_{n+1} \ne 0$ and
$x = A^{(r,s)}_n / A^{(r,s)}_{n+1}$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1 and Remark 7(ii). -/
def IsInSecondOrderFamily (p : ℤ) (x₀ x : ℚ) : Prop :=
  ∃ n : ℤ, secondOrderBiSeq p x₀.num x₀.den (n + 1) ≠ 0 ∧
    x = (secondOrderBiSeq p x₀.num x₀.den n : ℚ) / secondOrderBiSeq p x₀.num x₀.den (n + 1)

/-- **Every rational number lies in its own family.** For every integer $p$ and every rational
number $x_0$, $x_0$ belongs to the family generated by $x_0$ for $p$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
theorem isInSecondOrderFamily_self (p : ℤ) (x₀ : ℚ) : IsInSecondOrderFamily p x₀ x₀ :=
  ⟨0, by simp [secondOrderBiSeq, secondOrderFwd], by
    simp [secondOrderBiSeq, secondOrderFwd, Rat.num_div_den]⟩

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

/-- **Two families of integer values.** Let $a, b, p$ be integers with $p \ne 0$, let
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ for rational $x$, and for integers $r, s$ let
$A^{(r,s)}$ be the two-sided integer sequence with $A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and
$A^{(r,s)}_{n+2} = pA^{(r,s)}_{n+1} + A^{(r,s)}_n$ for all integers $n$. Then
$A(A^{(0,1)}_n / A^{(0,1)}_{n+1})$ is an integer for every integer $n \ne -1$, and
$A(A^{(-b,a)}_n / A^{(-b,a)}_{n+1})$ is an integer for every integer $n$ with
$A^{(-b,a)}_{n+1} \ne 0$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 2 (`jis-2025-25.8.3-thm-2`). -/
public theorem_wanted secondOrderGenValue_trivial_families_integer (a b p : ℤ) (hp : p ≠ 0) :
    (∀ n : ℤ, n ≠ -1 → ∃ z : ℤ, secondOrderGenValue a b p
      ((secondOrderBiSeq p 0 1 n : ℚ) / secondOrderBiSeq p 0 1 (n + 1)) = z) ∧
    ∀ n : ℤ, secondOrderBiSeq p (-b) a (n + 1) ≠ 0 → ∃ z : ℤ, secondOrderGenValue a b p
      ((secondOrderBiSeq p (-b) a n : ℚ) / secondOrderBiSeq p (-b) a (n + 1)) = z

/-- **Integrality criterion at a rational point.** Let $a, b, p$ be integers with $p \ne 0$ and let
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ for rational $x$. Let $r, s$ be coprime integers
with $s \ne 0$ and put $D = s^2 - prs - r^2$. Then $A(r/s)$ is an integer if and only if
$b \equiv -art \pmod{D}$ for every integer $t$ with $st \equiv 1 \pmod{D}$.

Since $s$ is invertible modulo $D$, this is the congruence $b \equiv -ars^{-1} \pmod{|D|}$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 4 (`jis-2025-25.8.3-lem-4`). -/
public theorem_wanted secondOrderGenValue_integer_iff (a b p : ℤ) (hp : p ≠ 0) (r s : ℤ)
    (hs : s ≠ 0)
    (hrs : Int.gcd r s = 1) :
    (∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z) ↔
      ∀ t : ℤ, s * t ≡ 1 [ZMOD (s ^ 2 - p * r * s - r ^ 2)] →
        b ≡ -a * r * t [ZMOD (s ^ 2 - p * r * s - r ^ 2)]

/-- **Neighbours of an integer value.** Let $a, b, p$ be integers with $p \ne 0$ and let
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ for rational $x$. If $r, s$ are coprime integers
with $r \ne 0$, $s \ne 0$ and $r + ps \ne 0$, and $A(r/s)$ is an integer, then $A(s/(r + ps))$
and $A((s - pr)/r)$ are integers.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 6 (`jis-2025-25.8.3-lem-6`). -/
public theorem_wanted secondOrderGenValue_neighbors_integer (a b p : ℤ) (hp : p ≠ 0) (r s : ℤ)
    (hr : r ≠ 0)
    (hs : s ≠ 0) (hrps : r + p * s ≠ 0) (hrs : Int.gcd r s = 1)
    (hint : ∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z) :
    (∃ z : ℤ, secondOrderGenValue a b p ((s : ℚ) / (r + p * s)) = z) ∧
      ∃ z : ℤ, secondOrderGenValue a b p (((s : ℚ) - p * r) / r) = z

/-- **Relations between values of $M$ at neighbouring pairs.** Let $a$, $b$, $p$ be integers with
$p \ne 0$, and for integers $r$, $s$ let
$M(r, s) = \frac{br^2 + bs^2 - apr^2 + 2ars}{s^2 - prs - r^2}$. Then for all integers $r$, $s$
that are not both zero, $M(s - pr, r) + (p^2 + 2)M(r, s) + M(s, r + ps) = 0$ and
$M(r, s)^2 + (p^2 + 2)M(r, s)M(s, r + ps) + M(s, r + ps)^2 = abp^3 + (a^2 - b^2)p^2$.

The source assumes $r \ne 0$, $s \ne 0$ and $r + ps \ne 0$; here only $(r, s) \ne (0, 0)$ is
assumed. Since $p \ne 0$, the three denominators equal $\pm(s^2 - prs - r^2)$, which is nonzero.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 8 (`jis-2025-25.8.3-lem-8`). -/
public theorem_wanted secondOrderMValue_relations (a b p : ℤ) (hp : p ≠ 0) (r s : ℤ) (hrs :
    (r, s) ≠ (0, 0)) :
    secondOrderMValue a b p (s - p * r) r + (p ^ 2 + 2) * secondOrderMValue a b p r s +
        secondOrderMValue a b p s (r + p * s) = 0 ∧
      secondOrderMValue a b p r s ^ 2 +
          (p ^ 2 + 2) * secondOrderMValue a b p r s * secondOrderMValue a b p s (r + p * s) +
          secondOrderMValue a b p s (r + p * s) ^ 2 =
        a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2

/-- **A small value of $M$ in the family of $r/s$ when $abp + a^2 - b^2 < 0$.** Let $a, b, p$ be
integers with $p \ne 0$ and $abp + a^2 - b^2 < 0$. Let $A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$
for rational $x$, and for integers $u, v$ let
$M(u, v) = \frac{bu^2 + bv^2 - apu^2 + 2auv}{v^2 - puv - u^2}$, where in both a fraction with
denominator $0$ is read as $0$. Let $r, s$ be coprime integers with $s \ne 0$ such that $A(r/s)$
is an integer, and let $(A^{(r,s)}_n)_{n \in \mathbb{Z}}$ be the two-sided sequence with
$A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and $A^{(r,s)}_{n+1} = pA^{(r,s)}_n + A^{(r,s)}_{n-1}$ for
every integer $n$. If $A^{(r,s)}_n \ne 0$ for every integer $n$, then there is an integer $n$
with $|M(A^{(r,s)}_n, A^{(r,s)}_{n+1})| \le \sqrt{b^2 - a^2 - abp}$.

The hypothesis that no term vanishes is the paper's assumption before Lemma 8 ("we can assume
that the conditions $r \ne 0, s \ne 0, r + ps \ne 0$ automatically hold"). Without it the paper's
claim fails: for $(a, b, p) = (-1, 8, -1)$ and $x = 0$, the members $A_n/A_{n+1}$ of the family
$A^{(0,1)}$ with $A_{n+1} \ne 0$ have $\min |M| = 8 > \sqrt{55}$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 9 (`jis-2025-25.8.3-lem-9`). -/
public theorem_wanted exists_small_secondOrderMValue_of_neg (a b p : ℤ) (hp : p ≠ 0)
    (hneg : a * b * p + a ^ 2 - b ^ 2 < 0) (r s : ℤ) (hs : s ≠ 0) (hrs : Int.gcd r s = 1)
    (hint : ∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z)
    (hnz : ∀ n : ℤ, secondOrderBiSeq p r s n ≠ 0) :
    ∃ n : ℤ, |(secondOrderMValue a b p (secondOrderBiSeq p r s n)
        (secondOrderBiSeq p r s (n + 1)) : ℝ)| ≤ √((-a * b * p - a ^ 2 + b ^ 2 : ℤ) : ℝ)

/-- **A small value of $M$ in the family of $r/s$ when $abp + a^2 - b^2 \ge 0$.** Let $a, b, p$
be integers with $p \ne 0$ and $abp + a^2 - b^2 \ge 0$. Let
$A(x) = \frac{a(1 - px) + bx}{1 - px - x^2}$ for rational $x$, and for integers $u, v$ let
$M(u, v) = \frac{bu^2 + bv^2 - apu^2 + 2auv}{v^2 - puv - u^2}$, where in both a fraction with
denominator $0$ is read as $0$. Let $r, s$ be coprime integers with $s \ne 0$ such that $A(r/s)$
is an integer, and let $(A^{(r,s)}_n)_{n \in \mathbb{Z}}$ be the two-sided sequence with
$A^{(r,s)}_0 = r$, $A^{(r,s)}_1 = s$ and $A^{(r,s)}_{n+1} = pA^{(r,s)}_n + A^{(r,s)}_{n-1}$ for
every integer $n$. If $A^{(r,s)}_n \ne 0$ for every integer $n$, then there is an integer $n$
with $|M(A^{(r,s)}_n, A^{(r,s)}_{n+1})| \le \sqrt{(abp^3 + (a^2 - b^2)p^2)/(p^2 + 4)}$.

The hypothesis that no term vanishes is the paper's assumption before Lemma 8. Without it the
paper's claim fails: for $(a, b, p) = (-3, -8, 5)$ and $x = 0$, the members $A_n/A_{n+1}$ of the
family $A^{(0,1)}$ with $A_{n+1} \ne 0$ have $\min |M| = 8$, while
$(abp^3 + (a^2 - b^2)p^2)/(p^2 + 4) = 1625/29 < 64$.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 10 (`jis-2025-25.8.3-lem-10`). -/
public theorem_wanted exists_small_secondOrderMValue_of_nonneg (a b p : ℤ) (hp : p ≠ 0)
    (hnonneg : 0 ≤ a * b * p + a ^ 2 - b ^ 2) (r s : ℤ) (hs : s ≠ 0) (hrs : Int.gcd r s = 1)
    (hint : ∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z)
    (hnz : ∀ n : ℤ, secondOrderBiSeq p r s n ≠ 0) :
    ∃ n : ℤ, |(secondOrderMValue a b p (secondOrderBiSeq p r s n)
        (secondOrderBiSeq p r s (n + 1)) : ℝ)| ≤
      √(((a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2 : ℤ) : ℝ) / (p ^ 2 + 4))

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
