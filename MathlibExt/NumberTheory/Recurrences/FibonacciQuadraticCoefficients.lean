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
# Integer sequences `P(n) F_n + Q(n) F_{n-1}` with rational polynomial coefficients

The theorem `fib_quadratic_coeff_isInt_iff` characterizes the quadratic coefficients
for which all terms are integers.

A statement from Kálmán Liptai, László Németh, Tamás Szakács and László Szalay,
*On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4.

The paper uses `F_{-1} = 1`. To stay inside `Nat.fib`, every occurrence of `F_{n-1}`
is written as `F_{n+1} - F_n`, which agrees with the paper for all `n ≥ 0`
(including `n = 0`). A sequence is an *integer sequence* when every term `w_n`,
`n ≥ 0`, is an integer. The paper's nondegeneracy assumptions on the leading
coefficients (`a ≠ 0`, `d ≠ 0`) are dropped because the equivalence holds for all rational
coefficients.

The coefficient formulas (2.10) survive in the extracted text with their numerators only.
The denominators used here are the unique ones for which the displayed numerators solve
the paper's initial-value system (2.8), and they reproduce its worked example.
-/

namespace MetaMathlibExt

namespace fib_quadratic_coeff_isInt_iff

private def term (a b c d e f : ℚ) (n : ℕ) : ℚ :=
  (a * n ^ 2 + b * n + c) * Nat.fib n +
    (d * n ^ 2 + e * n + f) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n)

/-- The recurrence given by the polynomial `(X² - X - 1)³`. -/
private theorem term_add_six (a b c d e f : ℚ) (n : ℕ) :
    let w := term a b c d e f
    w (n + 6) = 3 * w (n + 5) - 5 * w (n + 3) + 3 * w (n + 1) + w n := by
  simp only [term, Nat.fib_add_two, Nat.cast_add, Nat.cast_ofNat]
  ring

end fib_quadratic_coeff_isInt_iff

open fib_quadratic_coeff_isInt_iff

/-- **Integer sequences with quadratic Fibonacci coefficients.** Let $F_n$ be the $n$-th Fibonacci
number and put $F_{-1} = 1$, so that $F_{n-1} = F_{n+1} - F_n$ for every $n \ge 0$. For rational
numbers $a, b, c, d, e, f$, the number
$w_n = (an^2 + bn + c)F_n + (dn^2 + en + f)F_{n-1}$ is an integer for every natural number $n$
if and only if $f$ is an integer and there are integers $z_1, \dots, z_5$ with
$a = (-z_1 + 3z_2 + z_3 - 3z_4 + z_5)/10$,
$b = (-5z_1 - 75z_2 + 15z_3 + 45z_4 - 17z_5)/50$,
$c = (30z_1 + 30z_2 - 10z_3 - 15z_4 + 6z_5)/25$,
$d = (3z_1 - 4z_2 - 3z_3 + 4z_4 - z_5)/10$ and
$e = (-45z_1 + 80z_2 + 15z_3 - 40z_4 + 11z_5)/50$.

The integers $z_i$ are then determined by the sequence: $z_1 = w_1$, $z_2 = w_2 - f$,
$z_3 = w_3 - f$, $z_4 = w_4 - 2f$ and $z_5 = w_5 - 3f$.

Source: Kálmán Liptai, László Németh, Tamás Szakács and László Szalay,
*On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4,
Theorem 2.2 (`fq-2024-szakacs06212024rev-thm-2.2`). -/
public theorem fib_quadratic_coeff_isInt_iff (a b c d e f : ℚ) :
    (∀ n : ℕ, ∃ k : ℤ, (k : ℚ) =
      (a * n ^ 2 + b * n + c) * Nat.fib n +
        (d * n ^ 2 + e * n + f) * ((Nat.fib (n + 1) : ℚ) - Nat.fib n)) ↔
    (∃ k : ℤ, (k : ℚ) = f) ∧ ∃ z₁ z₂ z₃ z₄ z₅ : ℤ,
      a = ((-z₁ + 3 * z₂ + z₃ - 3 * z₄ + z₅ : ℤ) : ℚ) / 10 ∧
      b = ((-5 * z₁ - 75 * z₂ + 15 * z₃ + 45 * z₄ - 17 * z₅ : ℤ) : ℚ) / 50 ∧
      c = ((30 * z₁ + 30 * z₂ - 10 * z₃ - 15 * z₄ + 6 * z₅ : ℤ) : ℚ) / 25 ∧
      d = ((3 * z₁ - 4 * z₂ - 3 * z₃ + 4 * z₄ - z₅ : ℤ) : ℚ) / 10 ∧
      e = ((-45 * z₁ + 80 * z₂ + 15 * z₃ - 40 * z₄ + 11 * z₅ : ℤ) : ℚ) / 50 := by
  let w := term a b c d e f
  change (∀ n : ℕ, ∃ k : ℤ, (k : ℚ) = w n) ↔ _
  constructor
  · intro h
    choose v hv using h
    refine ⟨⟨v 0, by simpa [w, term] using hv 0⟩, v 1, v 2 - v 0, v 3 - v 0,
      v 4 - 2 * v 0, v 5 - 3 * v 0, ?_⟩
    push_cast
    simp only [hv, w, term]
    norm_num
    exact ⟨by ring, by ring, by ring, by ring, by ring⟩
  · rintro ⟨⟨k, hk⟩, z₁, z₂, z₃, z₄, z₅, ha, hb, hc, hd, he⟩ n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      refine match n, ih with
        | 0, _ => ⟨k, ?_⟩
        | 1, _ => ⟨z₁, ?_⟩
        | 2, _ => ⟨z₂ + k, ?_⟩
        | 3, _ => ⟨z₃ + k, ?_⟩
        | 4, _ => ⟨z₄ + 2 * k, ?_⟩
        | 5, _ => ⟨z₅ + 3 * k, ?_⟩
        | m + 6, prev => by
          choose v hv using prev
          refine ⟨3 * v (m + 5) (by omega) - 5 * v (m + 3) (by omega) +
            3 * v (m + 1) (by omega) + v m (by omega), ?_⟩
          push_cast
          simpa only [hv] using (term_add_six a b c d e f m).symm
      all_goals norm_num [w, term, ha, hb, hc, hd, he, ← hk]
      all_goals ring

end MetaMathlibExt
