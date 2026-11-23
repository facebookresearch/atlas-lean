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
# Integrality of linear Fibonacci expressions with an alternating term

The polynomial `(X² - X - 1)² (X² - 1)` gives a sixth-order recurrence with integer
coefficients. Thus the first six values determine integrality of the entire sequence.

## Notes on the source

`fib_linear_coeff_add_alternating_isInt_iff` omits the paper's nondegeneracy assumptions on the
leading coefficients because the initial-value formulas and the recurrence also hold when either
or both leading coefficients vanish.

The source prints $-3v_5$ in the numerator of $c$ and $+2v_1$ in $d$. The corrected terms
$+3v_5$ and $-2v_1$ give $c = 3/5$ and $d = 0$ for the source's tiling example
$(v_0, \dots, v_5) = (0, 1, 2, 6, 12, 26)$.
-/

namespace MetaMathlibExt

namespace FibonacciPolynomialCoefficients

private def term (a b c d e f : ℚ) (n : ℕ) : ℚ :=
  (a * n + b) * Nat.fib n + (c * n + d) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n) +
    e + f * (-1) ^ n

private theorem term_add_six (a b c d e f : ℚ) (n : ℕ) :
    let w := term a b c d e f
    w (n + 6) = 2 * w (n + 5) + 2 * w (n + 4) - 4 * w (n + 3) -
      2 * w (n + 2) + 2 * w (n + 1) + w n := by
  dsimp only [term]
  rw [Nat.fib_add n 6, Nat.fib_add n 5, Nat.fib_add n 4, Nat.fib_add n 3,
    Nat.fib_add n 2, Nat.fib_add n 1]
  norm_num [Nat.cast_add, Nat.cast_mul, pow_add]
  ring

end FibonacciPolynomialCoefficients

open FibonacciPolynomialCoefficients

/-- **Integer sequences with linear Fibonacci coefficients and an alternating term.** Let $F_n$
be the $n$-th Fibonacci number and put $F_{-1} = 1$, so that $F_{n-1} = F_{n+1} - F_n$ for every
$n \ge 0$. For rational numbers $a, b, c, d, e, f$, the number
$w_n = (an + b)F_n + (cn + d)F_{n-1} + e + f(-1)^n$ is an integer for every natural number $n$
if and only if there are integers $v_0, \dots, v_5$ with
$a = (3v_0 + 2v_1 - 7v_2 - v_3 + 4v_4 - v_5)/5$,
$b = (-3v_0 - 2v_1 - 3v_2 + 6v_3 + 6v_4 - 4v_5)/5$,
$c = (-4v_0 - v_1 + 11v_2 - 2v_3 - 7v_4 + 3v_5)/5$,
$d = -2v_1 + v_2 + 2v_3 - v_4$,
$e = (v_0 + 3v_1 + v_2 - 3v_3 - v_4 + v_5)/2$ and
$f = (v_0 + v_1 - 3v_2 - v_3 + 3v_4 - v_5)/2$.

These integers are then the initial values of the sequence: $v_i = w_i$ for $0 \le i \le 5$.

Source: Kálmán Liptai, László Németh, Tamás Szakács and László Szalay,
*On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4,
Theorem 3.1 (`fq-2024-szakacs06212024rev-thm-3.1`). -/
public theorem fib_linear_coeff_add_alternating_isInt_iff (a b c d e f : ℚ) :
    (∀ n : ℕ, ∃ k : ℤ, (k : ℚ) =
      (a * n + b) * Nat.fib n + (c * n + d) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n) +
        e + f * (-1) ^ n) ↔
    ∃ w₀ w₁ w₂ w₃ w₄ w₅ : ℤ,
      a = ((3 * w₀ + 2 * w₁ - 7 * w₂ - w₃ + 4 * w₄ - w₅ : ℤ) : ℚ) / 5 ∧
      b = ((-3 * w₀ - 2 * w₁ - 3 * w₂ + 6 * w₃ + 6 * w₄ - 4 * w₅ : ℤ) : ℚ) / 5 ∧
      c = ((-4 * w₀ - w₁ + 11 * w₂ - 2 * w₃ - 7 * w₄ + 3 * w₅ : ℤ) : ℚ) / 5 ∧
      d = ((-2 * w₁ + w₂ + 2 * w₃ - w₄ : ℤ) : ℚ) ∧
      e = ((w₀ + 3 * w₁ + w₂ - 3 * w₃ - w₄ + w₅ : ℤ) : ℚ) / 2 ∧
      f = ((w₀ + w₁ - 3 * w₂ - w₃ + 3 * w₄ - w₅ : ℤ) : ℚ) / 2 := by
  let w := term a b c d e f
  change (∀ n : ℕ, ∃ k : ℤ, (k : ℚ) = w n) ↔ _
  constructor
  · intro h
    choose v hv using h
    refine ⟨v 0, v 1, v 2, v 3, v 4, v 5, ?_⟩
    push_cast
    simp only [hv, w, term]
    norm_num
    exact ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, v₅, ha, hb, hc, hd, he, hf⟩ n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      refine match n, ih with
        | 0, _ => ⟨v₀, ?_⟩
        | 1, _ => ⟨v₁, ?_⟩
        | 2, _ => ⟨v₂, ?_⟩
        | 3, _ => ⟨v₃, ?_⟩
        | 4, _ => ⟨v₄, ?_⟩
        | 5, _ => ⟨v₅, ?_⟩
        | m + 6, prev => by
          choose v hv using prev
          refine ⟨2 * v (m + 5) (by omega) + 2 * v (m + 4) (by omega) -
            4 * v (m + 3) (by omega) - 2 * v (m + 2) (by omega) +
            2 * v (m + 1) (by omega) + v m (by omega), ?_⟩
          push_cast
          simpa only [hv] using (term_add_six a b c d e f m).symm
      all_goals
        norm_num [w, term, ha, hb, hc, hd, he, hf]
        ring

end MetaMathlibExt
