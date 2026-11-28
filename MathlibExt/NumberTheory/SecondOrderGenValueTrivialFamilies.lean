/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SecondOrderGenValue
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Two families of integer values of a second-order generating function

For nonzero `p`, the ratios of consecutive terms in the sequences starting at `(0, 1)` and
`(-b, a)` give integer values of `secondOrderGenValue a b p` whenever the ratios are defined.
-/

namespace MetaMathlibExt

@[expose] public section

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
  change secondOrderBwd p r s 2 = s - p * r
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
  · change secondOrderFwd p r s (m + 2) = p * secondOrderFwd p r s (m + 1) + secondOrderFwd p r s m
    rfl
  · rcases m with _ | _ | k
    · change secondOrderFwd p r s 1 = p * secondOrderFwd p r s 0 + secondOrderBwd p r s 2
      simp only [secondOrderFwd, secondOrderBwd]
      ring
    · change secondOrderFwd p r s 0 = p * secondOrderBwd p r s 2 + secondOrderBwd p r s 3
      simp only [secondOrderFwd, secondOrderBwd]
      ring
    · have h2 : Int.negSucc (k + 2) + 2 = Int.negSucc k := by omega
      have h1 : Int.negSucc (k + 2) + 1 = Int.negSucc (k + 1) := by omega
      rw [h2, h1]
      have e : secondOrderBwd p r s (k + 4) =
          secondOrderBwd p r s (k + 2) - p * secondOrderBwd p r s (k + 3) := rfl
      change secondOrderBwd p r s (k + 2) =
        p * secondOrderBwd p r s (k + 3) + secondOrderBwd p r s (k + 4)
      rw [e]
      ring

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

namespace secondOrderGenValue_trivial_families_integer

-- In this representation the numerator of A(r/s) is u * s times its denominator.
private def HasCoefficients (a b p r s : ℤ) : Prop :=
  ∃ u v : ℤ, a = u * s + v * r ∧ b = -u * r + v * (p * r - s)

private theorem coefficients_step (a b p r s : ℤ) :
    HasCoefficients a b p s (p * s + r) ↔ HasCoefficients a b p r s := by
  constructor
  · rintro ⟨u, v, ha, hb⟩
    exact ⟨p * u + v, u, ha.trans (by ring), hb.trans (by ring)⟩
  · rintro ⟨u, v, ha, hb⟩
    exact ⟨v, u - p * v, ha.trans (by ring), hb.trans (by ring)⟩

private theorem coefficients_at {a b p r s : ℤ} (h : HasCoefficients a b p r s) (n : ℤ) :
    HasCoefficients a b p (secondOrderBiSeq p r s n) (secondOrderBiSeq p r s (n + 1)) := by
  let U := secondOrderBiSeq p r s
  let P (i : ℤ) := HasCoefficients a b p (U i) (U (i + 1))
  have step (i : ℤ) : P (i + 1) ↔ P i := by
    simp only [P, add_assoc, one_add_one_eq_two]
    rw [show U (i + 2) = p * U (i + 1) + U i from secondOrderBiSeq_add_two p r s i]
    exact coefficients_step _ _ _ _ _
  exact Int.inductionOn' (motive := P) n 0 h (fun i _ => (step i).2)
    (fun i _ ih => (step (i - 1)).1 (by simpa using ih))

private theorem integer_of_coefficients {a b p r s : ℤ} (hs : s ≠ 0)
    (h : HasCoefficients a b p r s) : ∃ z : ℤ, secondOrderGenValue a b p ((r : ℚ) / s) = z := by
  obtain ⟨u, v, rfl, rfl⟩ := h
  have hsq : (s : ℚ) ≠ 0 := by exact_mod_cast hs
  unfold secondOrderGenValue
  by_cases hd : 1 - p * ((r : ℚ) / s) - ((r : ℚ) / s) ^ 2 = 0
  · exact ⟨0, by simp [hd]⟩
  · refine ⟨u * s, (div_eq_iff hd).2 ?_⟩
    push_cast
    field_simp
    ring

-- The products p Uᵢ Uᵢ₊₁ increase by (p Uᵢ₊₁)². Their signs on either side of zero
-- rule out any other vanishing term of the sequence starting at (0, 1).
private theorem next_ne_zero {p n : ℤ} (hp : p ≠ 0) (hn : n ≠ -1) :
    secondOrderBiSeq p 0 1 (n + 1) ≠ 0 := by
  let U := secondOrderBiSeq p 0 1
  let f (i : ℤ) := p * U i * U (i + 1)
  have hm : Monotone f := monotone_int_of_le_succ fun i => by
    simp only [f, add_assoc, one_add_one_eq_two]
    rw [show U (i + 2) = p * U (i + 1) + U i from secondOrderBiSeq_add_two p 0 1 i]
    nlinarith only [sq_nonneg (p * U (i + 1))]
  rcases eq_or_ne n 0 with rfl | hn₀
  · exact one_ne_zero
  intro hz
  have hzero : f n = 0 := by simp [f, U, hz]
  rcases le_or_gt 1 n with h | h
  · have hle := (hm h).trans_eq hzero
    norm_num [f, U, secondOrderBiSeq, secondOrderFwd] at hle
    nlinarith only [hle, sq_pos_of_ne_zero hp]
  · have hle := hzero.symm.trans_le (hm (show n ≤ -2 by omega))
    change 0 ≤ p * secondOrderBwd p 0 1 3 * secondOrderBwd p 0 1 2 at hle
    simp [secondOrderBwd] at hle
    nlinarith only [hle, sq_pos_of_ne_zero hp]

end secondOrderGenValue_trivial_families_integer

open secondOrderGenValue_trivial_families_integer in
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
theorem secondOrderGenValue_trivial_families_integer (a b p : ℤ) (hp : p ≠ 0) :
    (∀ n : ℤ, n ≠ -1 → ∃ z : ℤ, secondOrderGenValue a b p
      ((secondOrderBiSeq p 0 1 n : ℚ) / secondOrderBiSeq p 0 1 (n + 1)) = z) ∧
    ∀ n : ℤ, secondOrderBiSeq p (-b) a (n + 1) ≠ 0 → ∃ z : ℤ, secondOrderGenValue a b p
      ((secondOrderBiSeq p (-b) a n : ℚ) / secondOrderBiSeq p (-b) a (n + 1)) = z := by
  constructor
  · intro n hn
    apply integer_of_coefficients (next_ne_zero hp hn)
    exact coefficients_at ⟨a, -b, by ring, by ring⟩ n
  · intro n hn
    apply integer_of_coefficients hn
    exact coefficients_at ⟨1, 0, by ring, by ring⟩ n

end

end MetaMathlibExt
