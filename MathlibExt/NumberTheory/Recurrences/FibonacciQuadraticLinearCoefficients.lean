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
# Integrality of quadratic and linear Fibonacci expressions

The theorem `fib_quadratic_linear_coeff_isInt_iff` characterizes the rational quadratic and
linear coefficients for which every term of the Fibonacci expression is integral.
The terms satisfy the recurrence with characteristic polynomial `(X² - X - 1)³`.
The first five values recover the coefficients, and the sixth is an integer combination
of those five values.

The recurrence and the initial-value formulas hold even when the leading coefficients vanish.
-/

namespace MetaMathlibExt

namespace fib_quadratic_linear_coeff_isInt_iff

/-- The Fibonacci expression with the convention `F_{-1} = 1`. -/
private def term (a b c d e : ℚ) (n : ℕ) : ℚ :=
  (a * n ^ 2 + b * n + c) * Nat.fib n +
    (d * n + e) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n)

/-- The recurrence associated to `(X² - X - 1)³`. -/
private theorem term_add_six (a b c d e : ℚ) (n : ℕ) :
    let w := term a b c d e
    w (n + 6) = 3 * w (n + 5) - 5 * w (n + 3) + 3 * w (n + 1) + w n := by
  simp only [term, Nat.fib_add_two, Nat.cast_add, Nat.cast_ofNat]
  ring

end fib_quadratic_linear_coeff_isInt_iff

open fib_quadratic_linear_coeff_isInt_iff

/-- **Integer sequences with quadratic and linear Fibonacci coefficients.** Let $F_n$ be the
$n$-th Fibonacci number and put $F_{-1} = 1$, so that $F_{n-1} = F_{n+1} - F_n$ for every
$n \ge 0$. For rational numbers $a, b, c, d, e$, the number
$w_n = (an^2 + bn + c)F_n + (dn + e)F_{n-1}$ is an integer for every natural number $n$ if and
only if $e$ is an integer and there are integers $z_1, z_2, z_3, z_4$ with
$a = (2z_1 - z_2 - 2z_3 + z_4)/10$, $b = (-56z_1 - 7z_2 + 66z_3 - 23z_4)/50$,
$c = (48z_1 + 6z_2 - 28z_3 + 9z_4)/25$ and $d = (-6z_1 + 18z_2 - 9z_3 + 2z_4)/25$.

The integers $z_i$ are then determined by the sequence: $z_1 = w_1$, $z_2 = w_2 - e$,
$z_3 = w_3 - e$ and $z_4 = w_4 - 2e$.

Source: Kálmán Liptai, László Németh, Tamás Szakács and László Szalay,
*On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4,
Theorem 2.3 (`fq-2024-szakacs06212024rev-thm-2.3`). -/
public theorem fib_quadratic_linear_coeff_isInt_iff (a b c d e : ℚ) :
    (∀ n : ℕ, ∃ k : ℤ, (k : ℚ) =
      (a * n ^ 2 + b * n + c) * Nat.fib n +
        (d * n + e) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n)) ↔
    (∃ k : ℤ, (k : ℚ) = e) ∧ ∃ z₁ z₂ z₃ z₄ : ℤ,
      a = ((2 * z₁ - z₂ - 2 * z₃ + z₄ : ℤ) : ℚ) / 10 ∧
      b = ((-56 * z₁ - 7 * z₂ + 66 * z₃ - 23 * z₄ : ℤ) : ℚ) / 50 ∧
      c = ((48 * z₁ + 6 * z₂ - 28 * z₃ + 9 * z₄ : ℤ) : ℚ) / 25 ∧
      d = ((-6 * z₁ + 18 * z₂ - 9 * z₃ + 2 * z₄ : ℤ) : ℚ) / 25 := by
  let w := term a b c d e
  change (∀ n : ℕ, ∃ k : ℤ, (k : ℚ) = w n) ↔ _
  constructor
  · intro h
    choose v hv using h
    refine ⟨⟨v 0, by simpa [w, term] using hv 0⟩, v 1, v 2 - v 0, v 3 - v 0,
      v 4 - 2 * v 0, ?_⟩
    push_cast
    simp only [hv, w, term]
    norm_num
    exact ⟨by ring, by ring, by ring, by ring⟩
  · rintro ⟨⟨k, hk⟩, z₁, z₂, z₃, z₄, ha, hb, hc, hd⟩ n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      refine match n, ih with
        | 0, _ => ⟨k, ?_⟩
        | 1, _ => ⟨z₁, ?_⟩
        | 2, _ => ⟨z₂ + k, ?_⟩
        | 3, _ => ⟨z₃ + k, ?_⟩
        | 4, _ => ⟨z₄ + 2 * k, ?_⟩
        | 5, _ => ⟨3 * z₁ - 4 * z₂ - 3 * z₃ + 4 * z₄ + 3 * k, ?_⟩
        | m + 6, prev => by
          choose v hv using prev
          refine ⟨3 * v (m + 5) (by omega) - 5 * v (m + 3) (by omega) +
            3 * v (m + 1) (by omega) + v m (by omega), ?_⟩
          push_cast
          simpa only [hv] using (term_add_six a b c d e m).symm
      all_goals norm_num [w, term, ha, hb, hc, hd, ← hk]
      all_goals ring

end MetaMathlibExt
