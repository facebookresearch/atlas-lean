/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.Ring

/-!
# Integrality of linear Fibonacci expressions

For rational numbers `a, b, c, d`, put `w n = (a n + b) F_n + (c n + d) F_{n-1}` with
`F_{-1} = 1`. This sequence satisfies the recurrence
`w (n + 4) = 2 w (n + 3) + w (n + 2) - 2 w (n + 1) - w n`, whose characteristic polynomial is
`(X² - X - 1)²`. Its coefficients are integers, so `w` takes only integer values exactly when
`w 0 = d`, `w 1 = a + b`, `w 2 = 2a + b + 2c + d` and `w 3 = 6a + 2b + 3c + d` are integers.
Solving `z₁ = w 1`, `z₂ = w 2 - d` and `z₃ = w 3 - d` for `a, b, c` gives
`fib_linear_coeff_isInt_iff`.

## Notes on the source

The source assumes `a ≠ 0` and `c ≠ 0`, so that both coefficient polynomials have degree one.
`fib_linear_coeff_isInt_iff` omits these assumptions because the initial values and the
recurrence hold for all rational coefficients. In the arXiv version of the source
(arXiv:2403.15053v1) the criterion is Theorem 1, in Section 2.2.1.
-/

namespace MetaMathlibExt

namespace FibonacciLinearCoefficients

/-- The term `(a n + b) F_n + (c n + d) F_{n-1}`, written with `F_{n-1} = F_{n+1} - F_n`. -/
private def term (a b c d : ℚ) (n : ℕ) : ℚ :=
  (a * n + b) * Nat.fib n + (c * n + d) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n)

/-- The terms satisfy the recurrence with characteristic polynomial `(X² - X - 1)²`. -/
private theorem term_add_four (a b c d : ℚ) (n : ℕ) :
    term a b c d (n + 4) = 2 * term a b c d (n + 3) + term a b c d (n + 2) -
      2 * term a b c d (n + 1) - term a b c d n := by
  simp only [term, Nat.fib_add_two, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- A sequence satisfying the recurrence of `term_add_four` takes only integer values once its
first four values are integers. -/
private theorem isInt_of_add_four {w : ℕ → ℚ}
    (hrec : ∀ n, w (n + 4) = 2 * w (n + 3) + w (n + 2) - 2 * w (n + 1) - w n)
    (h₀ : ∃ k : ℤ, (k : ℚ) = w 0) (h₁ : ∃ k : ℤ, (k : ℚ) = w 1)
    (h₂ : ∃ k : ℤ, (k : ℚ) = w 2) (h₃ : ∃ k : ℤ, (k : ℚ) = w 3) (n : ℕ) :
    ∃ k : ℤ, (k : ℚ) = w n := by
  suffices H : ∀ n, (∃ k : ℤ, (k : ℚ) = w n) ∧ (∃ k : ℤ, (k : ℚ) = w (n + 1)) ∧
      (∃ k : ℤ, (k : ℚ) = w (n + 2)) ∧ ∃ k : ℤ, (k : ℚ) = w (n + 3) from (H n).1
  intro n
  induction n with
  | zero => exact ⟨h₀, h₁, h₂, h₃⟩
  | succ n ih =>
    obtain ⟨⟨k₀, e₀⟩, ⟨k₁, e₁⟩, ⟨k₂, e₂⟩, ⟨k₃, e₃⟩⟩ := ih
    refine ⟨⟨k₁, e₁⟩, ⟨k₂, e₂⟩, ⟨k₃, e₃⟩, ⟨2 * k₃ + k₂ - 2 * k₁ - k₀, ?_⟩⟩
    rw [hrec n]
    push_cast
    rw [e₀, e₁, e₂, e₃]

end FibonacciLinearCoefficients

open FibonacciLinearCoefficients

/-- **Integer sequences with linear Fibonacci coefficients.** Let $F_n$ be the $n$-th Fibonacci
number and put $F_{-1} = 1$, so that $F_{n-1} = F_{n+1} - F_n$ for every $n \ge 0$. For rational
numbers $a, b, c, d$, the number $w_n = (an + b)F_n + (cn + d)F_{n-1}$ is an integer for every
natural number $n$ if and only if $d$ is an integer and there are integers $z_1, z_2, z_3$ with
$a = (-z_1 - 3z_2 + 2z_3)/5$, $b = (6z_1 + 3z_2 - 2z_3)/5$ and $c = (-2z_1 + 4z_2 - z_3)/5$.

The integers $z_i$ are then determined by the sequence: $z_1 = w_1$, $z_2 = w_2 - d$ and
$z_3 = w_3 - d$.

Source: Kálmán Liptai, László Németh, Tamás Szakács and László Szalay,
*On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4,
Theorem 2.1 (`fq-2024-szakacs06212024rev-thm-2.1`). -/
public theorem fib_linear_coeff_isInt_iff (a b c d : ℚ) :
    (∀ n : ℕ, ∃ k : ℤ, (k : ℚ) =
      (a * n + b) * Nat.fib n + (c * n + d) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n)) ↔
    (∃ k : ℤ, (k : ℚ) = d) ∧ ∃ z₁ z₂ z₃ : ℤ,
      a = ((-z₁ - 3 * z₂ + 2 * z₃ : ℤ) : ℚ) / 5 ∧
      b = ((6 * z₁ + 3 * z₂ - 2 * z₃ : ℤ) : ℚ) / 5 ∧
      c = ((-2 * z₁ + 4 * z₂ - z₃ : ℤ) : ℚ) / 5 := by
  change (∀ n : ℕ, ∃ k : ℤ, (k : ℚ) = term a b c d n) ↔ _
  have w₀ : term a b c d 0 = d := by simp [term]
  have w₁ : term a b c d 1 = a + b := by norm_num [term]
  have w₂ : term a b c d 2 = 2 * a + b + 2 * c + d := by norm_num [term]; ring
  have w₃ : term a b c d 3 = 6 * a + 2 * b + 3 * c + d := by norm_num [term]; ring
  constructor
  · intro h
    choose v hv using h
    refine ⟨⟨v 0, by rw [hv, w₀]⟩, v 1, v 2 - v 0, v 3 - v 0, ?_, ?_, ?_⟩
    all_goals
      push_cast
      simp only [hv, w₀, w₁, w₂, w₃]
      ring
  · rintro ⟨⟨k, hk⟩, z₁, z₂, z₃, ha, hb, hc⟩
    refine isInt_of_add_four (term_add_four a b c d) ⟨k, by rw [w₀, hk]⟩ ⟨z₁, ?_⟩
      ⟨z₂ + k, ?_⟩ ⟨z₃ + k, ?_⟩
    · rw [w₁, ha, hb]
      push_cast
      ring
    · rw [w₂, ha, hb, hc, ← hk]
      push_cast
      ring
    · rw [w₃, ha, hb, hc, ← hk]
      push_cast
      ring

end MetaMathlibExt
