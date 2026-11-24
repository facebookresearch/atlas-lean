/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Pell
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Euler's family of solutions of `a T² - b U² = c`

The substitution `(T, U) ↦ (T x + b U y, a T y + U x)` multiplies `a T² - b U²` by
`x² - ab y²`; for positive `a` and `b` it is the multiplication of `T √a + U √b` by
`x + y √(ab)`. Let `ε` be the fundamental solution of the Pell equation `x² - ab y² = 1` and
write `εʲ = x_j + y_j √(ab)`. Applied with `(x, y) = (x_j, y_j)`, the substitution sends a
solution `(T₁, U₁)` of `a T² - b U² = c` to the solution `(T₁ x_j + b U₁ y_j, a T₁ y_j + U₁ x_j)`.

When `c ≠ 0` these solutions are pairwise distinct. If the indices `j < k` give the same pair
`(T, U)`, then the substitution for `ε^(k - j)` fixes `(T, U)`. The `x`-coordinate of
`ε^(k - j)` is not `1`, so the only fixed pair is `(0, 0)`, and then `c = 0`.

## Main statement

* `MetaMathlibExt.pell_euler_solutions`: the pairs `(T₁ x_j + b U₁ y_j, a T₁ y_j + U₁ x_j)`
  solve `a T² - b U² = c` and are distinct for distinct `j`.

## References

* E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality Test*,
  Journal of Integer Sequences 28 (2025), Article 25.2.5, as cited in the docstring of
  `MetaMathlibExt.pell_euler_solutions`.
-/

namespace MetaMathlibExt

/-- The substitution `(T, U) ↦ (T x + b U y, a T y + U x)` preserves `a T² - b U²` when
`x² - ab y² = 1`. -/
private theorem pell_euler_solutions_norm (a b T U x y : ℤ)
    (hxy : x ^ 2 - a * b * y ^ 2 = 1) :
    a * (T * x + b * U * y) ^ 2 - b * (a * T * y + U * x) ^ 2 = a * T ^ 2 - b * U ^ 2 := by
  linear_combination (a * T ^ 2 - b * U ^ 2) * hxy

/-- If `x² - ab y² = 1` and `x ≠ 1`, the only pair fixed by the substitution
`(T, U) ↦ (T x + b U y, a T y + U x)` is `(0, 0)`, so a fixed pair has `a T² - b U² = 0`. -/
private theorem pell_euler_solutions_fixed (a b T U x y : ℤ)
    (hxy : x ^ 2 - a * b * y ^ 2 = 1) (hx : x ≠ 1) (hT : T = T * x + b * U * y)
    (hU : U = a * T * y + U * x) :
    a * T ^ 2 - b * U ^ 2 = 0 := by
  have h2 : 2 - 2 * x ≠ 0 := fun h => hx (by linarith)
  have hT0 : T = 0 := by
    refine (mul_eq_zero.mp ?_).resolve_left h2
    linear_combination (1 - x) * hT + b * y * hU - T * hxy
  have hU0 : U = 0 := by
    refine (mul_eq_zero.mp ?_).resolve_left h2
    linear_combination a * y * hT + (1 - x) * hU - U * hxy
  rw [hT0, hU0]
  ring

set_option linter.unusedVariables false in
/-- **Euler's family of solutions of $aT^2 - bU^2 = c$.** Let $a$, $b$, $c$ be integers
with $ab > 1$, $ab$ not a perfect square and $c \ne 0$, and let $T_1$, $U_1$ be integers with
$aT_1^2 - bU_1^2 = c$. Let $\varepsilon = x_1 + y_1\sqrt{ab}$ be the fundamental solution of
$x^2 - ab\,y^2 = 1$ and, for every natural number $j$, write
$\varepsilon^j = x_j + y_j\sqrt{ab}$. Then for every $j \ge 0$ the integers
$T = T_1 x_j + b U_1 y_j$ and $U = a T_1 y_j + U_1 x_j$ satisfy $aT^2 - bU^2 = c$, and different
$j$ give different pairs $(T, U)$.

The hypothesis $c \ne 0$ is added to the source statement: for $c = 0$ the only integer solution
is $(0, 0)$, since $ab$ is not a square.

Source: E. L. Roettger and H. C. Williams, *Some Remarks Concerning the Lucas-Lehmer Primality
Test*, Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem 8. -/
public theorem pell_euler_solutions (a b c T₁ U₁ : ℤ) (hab : 1 < a * b)
    (hsq : ¬ IsSquare (a * b)) (hc : c ≠ 0) (h₁ : a * T₁ ^ 2 - b * U₁ ^ 2 = c)
    (ε : Pell.Solution₁ (a * b)) (hε : Pell.IsFundamental ε) :
    (∀ j : ℕ, a * (T₁ * (ε ^ j).x + b * U₁ * (ε ^ j).y) ^ 2 -
        b * (a * T₁ * (ε ^ j).y + U₁ * (ε ^ j).x) ^ 2 = c) ∧
      Function.Injective fun j : ℕ =>
        (T₁ * (ε ^ j).x + b * U₁ * (ε ^ j).y, a * T₁ * (ε ^ j).y + U₁ * (ε ^ j).x) := by
  have hsol : ∀ j : ℕ, a * (T₁ * (ε ^ j).x + b * U₁ * (ε ^ j).y) ^ 2 -
      b * (a * T₁ * (ε ^ j).y + U₁ * (ε ^ j).x) ^ 2 = c := fun j =>
    (pell_euler_solutions_norm a b T₁ U₁ _ _ (ε ^ j).prop).trans h₁
  refine ⟨hsol, ?_⟩
  -- The pair at index `j` does not come back at the index `j + (m + 1)`.
  have key : ∀ j m : ℕ,
      (T₁ * (ε ^ j).x + b * U₁ * (ε ^ j).y, a * T₁ * (ε ^ j).y + U₁ * (ε ^ j).x) ≠
        (T₁ * (ε ^ (j + (m + 1))).x + b * U₁ * (ε ^ (j + (m + 1))).y,
          a * T₁ * (ε ^ (j + (m + 1))).y + U₁ * (ε ^ (j + (m + 1))).x) := by
    intro j m h
    rw [pow_add, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul, Prod.mk.injEq] at h
    have hp := (ε ^ (m + 1)).prop
    have hy : 0 < (ε ^ (m + 1)).y := Pell.Solution₁.y_pow_succ_pos hε.x_pos hε.2.1 m
    have hx : (ε ^ (m + 1)).x ≠ 1 := by
      intro hx
      rw [hx] at hp
      have : 0 < a * b * (ε ^ (m + 1)).y ^ 2 := mul_pos (by linarith) (pow_pos hy 2)
      linarith
    refine hc ((hsol j).symm.trans (pell_euler_solutions_fixed a b _ _ _ _ hp hx ?_ ?_))
    · linear_combination h.1
    · linear_combination h.2
  refine Function.Injective.of_lt_imp_ne fun j k hjk => ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hjk
  exact key j m

end MetaMathlibExt
