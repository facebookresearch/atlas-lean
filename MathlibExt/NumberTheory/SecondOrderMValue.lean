/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Rat
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Neighbouring values of the rational quantity `M` for a second-order recurrence

A recurrence step sends `(r, s)` to `(s, r + p * s)` and negates the denominator of `M`.
The values of `M` at successive pairs satisfy a three-term recurrence and a quadratic identity.
-/

namespace MetaMathlibExt

@[expose] public section

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

/-- A zero of the denominator would have coprime coordinates that are both units after
dividing out their gcd. -/
private theorem secondOrderMValue_den_ne_zero {p r s : ℤ} (hp : p ≠ 0)
    (hrs : (r, s) ≠ (0, 0)) : s ^ 2 - p * r * s - r ^ 2 ≠ 0 := by
  have hg : 0 < Int.gcd r s := Int.gcd_pos_iff.mpr (by grind)
  obtain ⟨g, u, v, hgpos, huv, rfl, rfl⟩ := Int.exists_gcd_one' hg
  intro h
  have hred : v ^ 2 - p * u * v - u ^ 2 = 0 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 (Int.natCast_ne_zero.mpr hgpos.ne'))
    linear_combination h
  have hcop := Int.isCoprime_iff_gcd_eq_one.mpr huv
  have hu : IsUnit u := hcop.pow_right.isUnit_of_dvd
    (show u ∣ v ^ 2 from ⟨p * v + u, by linear_combination hred⟩)
  have hv : IsUnit v := hcop.symm.pow_right.isUnit_of_dvd
    (show v ∣ u ^ 2 from ⟨v - p * u, by linear_combination -hred⟩)
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;> rcases Int.isUnit_iff.mp hv with rfl | rfl <;>
    exact hp (by linarith only [hred])

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
theorem secondOrderMValue_relations (a b p : ℤ) (hp : p ≠ 0) (r s : ℤ) (hrs :
    (r, s) ≠ (0, 0)) :
    secondOrderMValue a b p (s - p * r) r + (p ^ 2 + 2) * secondOrderMValue a b p r s +
        secondOrderMValue a b p s (r + p * s) = 0 ∧
      secondOrderMValue a b p r s ^ 2 +
          (p ^ 2 + 2) * secondOrderMValue a b p r s * secondOrderMValue a b p s (r + p * s) +
          secondOrderMValue a b p s (r + p * s) ^ 2 =
        a * b * p ^ 3 + (a ^ 2 - b ^ 2) * p ^ 2 := by
  have hD : (s : ℚ) ^ 2 - p * r * s - r ^ 2 ≠ 0 := by
    exact_mod_cast secondOrderMValue_den_ne_zero hp hrs
  unfold secondOrderMValue
  push_cast
  -- Both neighbouring denominators are the negative of the central denominator.
  rw [show (r : ℚ) ^ 2 - p * (s - p * r) * r - (s - p * r) ^ 2 =
        -(s ^ 2 - p * r * s - r ^ 2) by ring,
      show ((r : ℚ) + p * s) ^ 2 - p * s * (r + p * s) - s ^ 2 =
        -(s ^ 2 - p * r * s - r ^ 2) by ring]
  set D : ℚ := (s : ℚ) ^ 2 - p * r * s - r ^ 2
  simp only [div_neg]
  constructor
  · field_simp [hD]
    ring
  · field_simp [hD]
    dsimp [D]
    ring

end

end MetaMathlibExt
