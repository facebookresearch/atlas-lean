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

/-- The generating function `A(x) = (a(1 - px) + bx) / (1 - px - x²)` of `A_0 = a`, `A_1 = b`,
`A_{n+1} = p A_n + A_{n-1}`, as a rational function evaluated at `x ∈ ℚ`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Section 2. -/
def secondOrderGenValue (a b p : ℤ) (x : ℚ) : ℚ :=
  (a * (1 - p * x) + b * x) / (1 - p * x - x ^ 2)

/-- Characteristic value: `A(0) = a`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, proof of Theorem 2. -/
theorem secondOrderGenValue_zero (a b p : ℤ) : secondOrderGenValue a b p 0 = a := by
  simp [secondOrderGenValue]

/-- Forward part `A^{(r,s)}_n` (`n ≥ 0`) of the two-sided sequence with `A_0 = r`, `A_1 = s`,
`A_{n+1} = p A_n + A_{n-1}`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
def secondOrderFwd (p r s : ℤ) : ℕ → ℤ
  | 0 => r
  | 1 => s
  | n + 2 => p * secondOrderFwd p r s (n + 1) + secondOrderFwd p r s n

/-- Backward part: `secondOrderBwd p r s k = A^{(r,s)}_{1-k}`, using
`A_n = A_{n+2} - p A_{n+1}` for `n < 0`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
def secondOrderBwd (p r s : ℤ) : ℕ → ℤ
  | 0 => s
  | 1 => r
  | n + 2 => secondOrderBwd p r s n - p * secondOrderBwd p r s (n + 1)

/-- The two-sided sequence `(A^{(r,s)}_n)_{n ∈ ℤ}` with `A_0 = r`, `A_1 = s` and
`A_{n+1} = p A_n + A_{n-1}` for all `n` (the paper's forward rule "if `n > 1`" is read as
`n ≥ 1`, as the definition of `A_2` requires).

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
def secondOrderBiSeq (p r s : ℤ) : ℤ → ℤ
  | (n : ℕ) => secondOrderFwd p r s n
  | Int.negSucc n => secondOrderBwd p r s (n + 2)

/-- Characteristic values: `A_0 = r`, `A_1 = s`, `A_2 = ps + r`, `A_{-1} = s - pr`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
theorem secondOrderBiSeq_small (p r s : ℤ) :
    secondOrderBiSeq p r s 0 = r ∧ secondOrderBiSeq p r s 1 = s ∧
      secondOrderBiSeq p r s 2 = p * s + r ∧ secondOrderBiSeq p r s (-1) = s - p * r := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  show secondOrderBwd p r s 2 = s - p * r
  rfl

/-- Initial value `A^{(r,s)}_0 = r`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
@[simp] theorem secondOrderBiSeq_zero (p r s : ℤ) : secondOrderBiSeq p r s 0 = r := rfl

/-- Initial value `A^{(r,s)}_1 = s`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
@[simp] theorem secondOrderBiSeq_one (p r s : ℤ) : secondOrderBiSeq p r s 1 = s := rfl

/-- The defining recurrence on all of `ℤ`: `A_{n+2} = p A_{n+1} + A_n` for every integer `n`.

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

/-- The quantity `M(r, s) = (b r² + b s² - a p r² + 2 a r s) / (s² - p r s - r²)`, equal to
`±√((kp + b - ap)² - 4k(a - k))` for `k = A(r/s)`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Section 2 (before Lemma 8). -/
def secondOrderMValue (a b p r s : ℤ) : ℚ :=
  (b * r ^ 2 + b * s ^ 2 - a * p * r ^ 2 + 2 * a * r * s) / (s ^ 2 - p * r * s - r ^ 2)

/-- Characteristic value: `M(0, 1) = b`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Section 2. -/
theorem secondOrderMValue_zero_one (a b p : ℤ) : secondOrderMValue a b p 0 1 = b := by
  simp [secondOrderMValue]

/-- `x` belongs to the family generated by `x₀ = r/s` (lowest terms, `s > 0`): `x` is a ratio
`A^{(r,s)}_n / A^{(r,s)}_{n+1}` with `A^{(r,s)}_{n+1} ≠ 0`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1 and Remark 7(ii). -/
def IsInSecondOrderFamily (p : ℤ) (x₀ x : ℚ) : Prop :=
  ∃ n : ℤ, secondOrderBiSeq p x₀.num x₀.den (n + 1) ≠ 0 ∧
    x = (secondOrderBiSeq p x₀.num x₀.den n : ℚ) / secondOrderBiSeq p x₀.num x₀.den (n + 1)

/-- Characteristic property: every `x₀` belongs to its own family (`n = 0`).

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1. -/
theorem isInSecondOrderFamily_self (p : ℤ) (x₀ : ℚ) : IsInSecondOrderFamily p x₀ x₀ :=
  ⟨0, by simp [secondOrderBiSeq, secondOrderFwd], by
    simp [secondOrderBiSeq, secondOrderFwd, Rat.num_div_den]⟩

/-- If `r, s` are coprime (`s ≠ 0`) and `A(r/s)` is an integer, then
`A(A^{(r,s)}_n / A^{(r,s)}_{n+1})` is an integer whenever `A^{(r,s)}_{n+1} ≠ 0` (all `n ∈ ℤ`).

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 1 (`jis-2025-25.8.3-thm-1`). -/
public theorem_wanted secondOrderGenValue_family_integer (a b p : ℤ) (hp : p ≠ 0) (r s : ℤ)
    (hs : s ≠ 0)
    (hrs : Int.gcd r s = 1) (hint : ∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z)
    (n : ℤ) (hn : secondOrderBiSeq p r s (n + 1) ≠ 0) :
    ∃ z : ℤ, secondOrderGenValue a b p
      ((secondOrderBiSeq p r s n : ℚ) / secondOrderBiSeq p r s (n + 1)) = z

/-- (i) `A(A^{(0,1)}_n / A^{(0,1)}_{n+1})` is an integer for all `n ≠ -1`; (ii)
`A(A^{(-b,a)}_n / A^{(-b,a)}_{n+1})` is an integer whenever `A^{(-b,a)}_{n+1} ≠ 0`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Theorem 2 (`jis-2025-25.8.3-thm-2`). -/
public theorem_wanted secondOrderGenValue_trivial_families_integer (a b p : ℤ) (hp : p ≠ 0) :
    (∀ n : ℤ, n ≠ -1 → ∃ z : ℤ, secondOrderGenValue a b p
      ((secondOrderBiSeq p 0 1 n : ℚ) / secondOrderBiSeq p 0 1 (n + 1)) = z) ∧
    ∀ n : ℤ, secondOrderBiSeq p (-b) a (n + 1) ≠ 0 → ∃ z : ℤ, secondOrderGenValue a b p
      ((secondOrderBiSeq p (-b) a n : ℚ) / secondOrderBiSeq p (-b) a (n + 1)) = z

/-- For coprime `r, s` (`s ≠ 0`), `A(r/s)` is an integer iff `b ≡ -a r s⁻¹ (mod |s² - prs - r²|)`,
stated for every inverse `t` of `s` modulo `s² - prs - r²`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 4 (`jis-2025-25.8.3-lem-4`). -/
public theorem_wanted secondOrderGenValue_integer_iff (a b p : ℤ) (hp : p ≠ 0) (r s : ℤ)
    (hs : s ≠ 0)
    (hrs : Int.gcd r s = 1) :
    (∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z) ↔
      ∀ t : ℤ, s * t ≡ 1 [ZMOD (s ^ 2 - p * r * s - r ^ 2)] →
        b ≡ -a * r * t [ZMOD (s ^ 2 - p * r * s - r ^ 2)]

/-- If `r, s ≠ 0`, `r + ps ≠ 0`, `gcd(r, s) = 1` and `A(r/s)` is an integer, then `A(s/(r + ps))`
and `A((s - pr)/r)` are integers.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 6 (`jis-2025-25.8.3-lem-6`). -/
public theorem_wanted secondOrderGenValue_neighbors_integer (a b p : ℤ) (hp : p ≠ 0) (r s : ℤ)
    (hr : r ≠ 0)
    (hs : s ≠ 0) (hrps : r + p * s ≠ 0) (hrs : Int.gcd r s = 1)
    (hint : ∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z) :
    (∃ z : ℤ, secondOrderGenValue a b p ((s : ℚ) / (r + p * s)) = z) ∧
      ∃ z : ℤ, secondOrderGenValue a b p (((s : ℚ) - p * r) / r) = z

/-- (i) `M(s - pr, r) + (p² + 2) M(r, s) + M(s, r + ps) = 0`; (ii)
`M(r, s)² + (p² + 2) M(r, s) M(s, r + ps) + M(s, r + ps)² = abp³ + (a² - b²)p²`. Domain
extension: stated for all `(r, s) ≠ (0, 0)` instead of `r, s ≠ 0`, `r + ps ≠ 0`; with `p ≠ 0`
all three denominators are `±(s² - prs - r²) ≠ 0`.

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

/-- Assume `abp + a² - b² < 0` and `A(r/s)` is an integer (`r, s` coprime, `s ≠ 0`). Then some
member `A_n / A_{n+1}` of the family of `r/s` has `|M| ≤ √(-abp - a² + b²)`. Corrected reading:
the family has no zero term (`A^{(r,s)}_n ≠ 0` for all `n`), as the paper assumes before Lemma 8
("we can assume that the conditions `r ≠ 0, s ≠ 0, r + ps ≠ 0` automatically hold"). Without it
the claim fails: for `(a, b, p) = (-1, 8, -1)` and `x = 0` the family `A^{(0,1)}` has
`min |M| = 8 > √55`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 9 (`jis-2025-25.8.3-lem-9`). -/
public theorem_wanted exists_small_secondOrderMValue_of_neg (a b p : ℤ) (hp : p ≠ 0)
    (hneg : a * b * p + a ^ 2 - b ^ 2 < 0) (r s : ℤ) (hs : s ≠ 0) (hrs : Int.gcd r s = 1)
    (hint : ∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z)
    (hnz : ∀ n : ℤ, secondOrderBiSeq p r s n ≠ 0) :
    ∃ n : ℤ, |(secondOrderMValue a b p (secondOrderBiSeq p r s n)
        (secondOrderBiSeq p r s (n + 1)) : ℝ)| ≤ √((-a * b * p - a ^ 2 + b ^ 2 : ℤ) : ℝ)

/-- Assume `abp + a² - b² ≥ 0` and `A(r/s)` is an integer (`r, s` coprime, `s ≠ 0`). Then some
member of the family of `r/s` has `|M| ≤ √((abp³ + (a² - b²)p²)/(p² + 4))`. Corrected reading:
the family has no zero term, as assumed in the paper before Lemma 8; without it the claim fails:
for `(a, b, p) = (-3, -8, 5)` and `x = 0`, `min |M| = 8` while
`(abp³ + (a² - b²)p²)/(p² + 4) = 1625/29 < 64`.

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

/-- The algorithm. Let `E = abp³ + (a² - b²)p²` and `C = √(E/(p² + 4))` if `E ≥ 0`,
`C = √(-abp + b² - a²)` if `E < 0`. (Soundness) for integers `M, k` with `k ≠ 0` and
`M² = (kp - ap + b)² - 4k(a - k)`, both values `x = (ap - kp - b ± M)/(2k)` give integer `A(x)`.
(Completeness) every `x ∈ ℚ` with `A(x) ∈ ℤ` lies in one of the families of Theorem 2 or in the
family of such an `x'` obtained from integers `M, N, k` with `|M| ≤ C`,
`M² + (p² + 2)MN + N² = E`, `k ≠ 0` and `M² = (kp - ap + b)² - 4k(a - k)`. The ± is written as
`M` versus `-M`, `|M| ≤ C` as `M² ≤ C²`; uses `(a, b) ≠ (0, 0)`.

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

/-- For `U_0 = 0`, `U_1 = 1`, `U_{n+1} = p U_n + U_{n-1}` (the case `(a, b) = (0, 1)`), the set of
rationals at which the generating function `U(x)` is an integer is
`{A^{(0,1)}_n / A^{(0,1)}_{n+1} : n ≠ -1}`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Corollary 13 (`jis-2025-25.8.3-cor-13`). -/
public theorem_wanted secondOrderGenValue_zero_one_integer_set (p : ℤ) (hp : p ≠ 0) :
    {x : ℚ | ∃ z : ℤ, secondOrderGenValue 0 1 p x = z} =
      {x | ∃ n : ℤ, n ≠ -1 ∧
        x = (secondOrderBiSeq p 0 1 n : ℚ) / secondOrderBiSeq p 0 1 (n + 1)}

/-- For `U_n = lucasU (p, -1)` (`U_0 = 0`, `U_1 = 1`, `U_{n+1} = p U_n + U_{n-1}`) and its
generating function `U`: (i) `U(U_n/U_{n+1})` is an integer for all `n ≥ 0`; (ii) if `U(x) = k`
is an integer for a rational `x`, then `U(U_n/U_{n+1}) = k` for some `n ≥ 0`.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a Type of
Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Corollary 14 (`jis-2025-25.8.3-cor-14`). -/
public theorem_wanted secondOrderGenValue_lucasU (p : ℤ) (hp : p ≠ 0) :
    (∀ n : ℕ, ∃ z : ℤ, secondOrderGenValue 0 1 p
      ((lucasU ⟨p, -1, by norm_num⟩ n : ℚ) / lucasU ⟨p, -1, by norm_num⟩ (n + 1)) = z) ∧
    ∀ (x : ℚ) (k : ℤ), secondOrderGenValue 0 1 p x = k → ∃ n : ℕ, secondOrderGenValue 0 1 p
      ((lucasU ⟨p, -1, by norm_num⟩ n : ℚ) / lucasU ⟨p, -1, by norm_num⟩ (n + 1)) = k

/-- For `(a, b) = (1, 1)` there are no families beyond those of Theorem 2: every rational `x`
with `A(x) ∈ ℤ` is a ratio of consecutive terms of `A^{(0,1)}` or of `A^{(-1,1)}`.

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
