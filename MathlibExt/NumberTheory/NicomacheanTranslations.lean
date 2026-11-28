/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Translations and extensions of the Nicomachean identity

## References

- Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean Identity*,
  Journal of Integer Sequences 27 (2024), Article 24.6.3, pp. 1–23. Section 9 gives the two-term
  case of the concatenation formula.

For a finite sequence `σ = (a_1, …, a_n)` the paper's operator is
`ν(σ) = (∑ a_i)^2 - ∑ a_i^3`, here `nicomacheanNu` on lists over a commutative ring; the
classical identity is `ν(1, 2, …, n) = 0`. Sequences are lists (repetitions allowed; `ν` does not
depend on the order).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Nicomachean defect.** For a finite sequence $\sigma = (a_1, \ldots, a_n)$ of elements of a
commutative ring, the Nicomachean defect of $\sigma$ is
$\nu(\sigma) = \left(\sum_{i=1}^n a_i\right)^2 - \sum_{i=1}^n a_i^3$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Section 1. -/
def nicomacheanNu {R : Type*} [CommRing R] (σ : List R) : R :=
  σ.sum ^ 2 - (σ.map (· ^ 3)).sum

/-- **Nicomachean defect under concatenation.** Let $\nu$ be the Nicomachean defect. For finite
sequences $\sigma$ and $\tau = (t_1, \ldots, t_m)$ over a commutative ring, write $s$ for the sum of
$\sigma$ and $t$ for the sum of $\tau$. Then
$\nu(\sigma, \tau) = \nu(\sigma) + (2s + t)t - \sum_{j=1}^m t_j^3$. -/
theorem nicomacheanNu_append {R : Type*} [CommRing R] (σ τ : List R) :
    nicomacheanNu (σ ++ τ) =
      nicomacheanNu σ + (2 * σ.sum + τ.sum) * τ.sum - (τ.map (· ^ 3)).sum := by
  simp only [nicomacheanNu, List.sum_append, List.map_append]
  ring

/-- **Examples of the Nicomachean defect.** For the Nicomachean defect $\nu$ of a sequence of
integers, $\nu(1, 2, 3, 4) = 0$, $\nu(1, 2) = 0$, $\nu(3, 3, 3) = 0$,
$\nu(1, 2, 2, 3, 4, 5, 6, 8) = 0$ and $\nu(1, 2, 2, 3, 4, 6, 6, 8) = -28$.

The last two are the values at $x = 5$ and $x = 6$ of the paper's identity
$\nu(1, 2, 2, 3, 4, x, 6, 8) = (5 - x)(x - 4)(8 + x)$; the identity itself is not stated here.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Section 1. -/
theorem nicomacheanNu_examples :
    nicomacheanNu ([1, 2, 3, 4] : List ℤ) = 0 ∧ nicomacheanNu ([1, 2] : List ℤ) = 0 ∧
      nicomacheanNu ([3, 3, 3] : List ℤ) = 0 ∧
      nicomacheanNu ([1, 2, 2, 3, 4, 5, 6, 8] : List ℤ) = 0 ∧
      nicomacheanNu ([1, 2, 2, 3, 4, 6, 6, 8] : List ℤ) = -28 := by
  decide

/-- **The Nicomachean progression factor.** For rational numbers $n$, $s$ and $a$, define

$$\alpha(n, s, a) = 2n^2 + na - a^2 + \frac{n(n-1)(s - s^2)}{2} - (n-1)as.$$

This is the second factor of $\nu(S_m)$, where
$\nu(a_1, \dots, a_k) = (a_1 + \dots + a_k)^2 - (a_1^3 + \dots + a_k^3)$ is the Nicomachean defect,
$S = (a, a + s, \dots, a + (n-1)s)$, and $S_m$ joins $n$ copies of $n$ with the translated
progressions $S, S + n, \dots, S + mn$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Section 6, equation (nusm). -/
def nicomacheanAlpha (n s a : ℚ) : ℚ :=
  2 * n ^ 2 + n * a - a ^ 2 + n * (n - 1) * (s - s ^ 2) / 2 - (n - 1) * a * s

/-- **Specializations of the Nicomachean factor at $s = 1, 2, 3$.** Let
$\alpha(n, s, a) = 2n^2 + na - a^2 + n(n-1)(s - s^2)/2 - (n-1)as$. For all rational numbers $n$
and $a$, $\alpha(n, 1, a) = 2n^2 + a - a^2$, $\alpha(n, 2, a) = n^2 + (1 - a)n - a^2 + 2a$ and
$\alpha(n, 3, a) = -(a + n - 3)(a + n)$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Section 6. -/
theorem nicomacheanAlpha_one_two_three (n a : ℚ) :
    nicomacheanAlpha n 1 a = 2 * n ^ 2 + a - a ^ 2 ∧
      nicomacheanAlpha n 2 a = n ^ 2 + (1 - a) * n - a ^ 2 + 2 * a ∧
      nicomacheanAlpha n 3 a = -(a + n - 3) * (a + n) := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold nicomacheanAlpha; ring

/-- **Nicomachean sequences of rationals with large denominators.** Write
$\nu(a_1, \dots, a_n) = (a_1 + \dots + a_n)^2 - (a_1^3 + \dots + a_n^3)$ for the Nicomachean defect
of a finite sequence. For every natural number $Q$ there is a finite sequence $\sigma$ of positive
rational numbers with $\nu(\sigma) = 0$ having an entry whose denominator in lowest terms is
greater than $Q$.

Source: Seon-Hong Kim and Kenneth B. Stolarsky, *Translations and Extensions of the Nicomachean
Identity*, Journal of Integer Sequences 27 (2024), Article 24.6.3, Proposition 3
(`jis-2024-24.6.3-prop-3`). -/
theorem exists_pos_rat_nicomacheanNu_eq_zero_large_den (Q : ℕ) :
    ∃ σ : List ℚ, (∀ x ∈ σ, 0 < x) ∧ nicomacheanNu σ = 0 ∧ ∃ x ∈ σ, Q < x.den := by
  -- Scale the pair (1, Q + 2) so that its squared sum equals its sum of cubes.
  let x : ℚ := (Q + 3) / (Q * (Q + 3) + 3)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  refine ⟨[x, (Q + 2) * x], ?_, ?_, x, by simp, ?_⟩
  · simpa using And.intro hx (mul_pos (by positivity : 0 < (Q : ℚ) + 2) hx)
  · simp [nicomacheanNu, x]
    field_simp
    ring
  · -- The reduced numerator is at least one, whereas Q * x is strictly below one.
    have hsmall : (Q : ℚ) * x < 1 := by
      dsimp [x]
      rw [← mul_div_assoc, div_lt_one (by positivity)]
      exact lt_add_of_pos_right _ (by decide)
    have hnum : (1 : ℤ) ≤ x.num := Rat.num_pos.mpr hx
    have hlt : (Q : ℚ) * x < x.den * x := by
      rw [Rat.den_mul_eq_num]
      exact hsmall.trans_le (by exact_mod_cast hnum)
    exact_mod_cast (lt_of_mul_lt_mul_right hlt hx.le)

end

end MetaMathlibExt
