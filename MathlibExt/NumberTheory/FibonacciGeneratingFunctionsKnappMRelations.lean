/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FibonacciGeneratingFunctions
import MathlibExt.NumberTheory.SecondOrderMValue
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

-- This is the parameter-one case of the denominator argument in `SecondOrderMValue`.
private theorem knappDen_ne_zero {p q : ℤ} (hpq : (p, q) ≠ (0, 0)) :
    q ^ 2 - p * q - p ^ 2 ≠ 0 := by
  have hg : 0 < Int.gcd p q := Int.gcd_pos_iff.mpr (by grind)
  obtain ⟨g, u, v, hgpos, huv, rfl, rfl⟩ := Int.exists_gcd_one' hg
  intro h
  have hred : v ^ 2 - u * v - u ^ 2 = 0 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 (Int.natCast_ne_zero.mpr hgpos.ne'))
    linear_combination h
  have hcop := Int.isCoprime_iff_gcd_eq_one.mpr huv
  have hu : IsUnit u := hcop.pow_right.isUnit_of_dvd
    (show u ∣ v ^ 2 from ⟨v + u, by linear_combination hred⟩)
  have hv : IsUnit v := hcop.symm.pow_right.isUnit_of_dvd
    (show v ∣ u ^ 2 from ⟨v - u, by linear_combination -hred⟩)
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;>
    rcases Int.isUnit_iff.mp hv with rfl | rfl <;> norm_num at hred

private theorem knappM_eq_secondOrderMValue (a b p q : ℤ) (hpq : (p, q) ≠ (0, 0)) :
    knappM a b p q = secondOrderMValue a b 1 p q := by
  have hD : (q : ℚ) ^ 2 - p * q - (p : ℚ) ^ 2 ≠ 0 := by
    exact_mod_cast knappDen_ne_zero hpq
  unfold knappM secondOrderMValue
  push_cast
  simp only [one_mul, mul_one]
  set D : ℚ := (q : ℚ) ^ 2 - p * q - (p : ℚ) ^ 2
  have hD' : D ≠ 0 := hD
  field_simp [hD']
  dsimp [D]
  ring

/-- Lemma 11: `M(a, b, p+q, p+2q) = -3M(a, b, q, p+q) - M(a, b, p, q)` and
`M(a,b,p,q)² + 3M(a,b,p,q)M(a,b,q,p+q) + M(a,b,q,p+q)² = a² + ab - b²`.
Stated for every `(p, q) ≠ (0, 0)`; the paper assumes `q ≠ 0`,
`p + q ≠ 0`, `p + 2q ≠ 0`.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 11 (`jis-2024-24.3.1-lem-11`). -/
public theorem knappM_recurrence_and_quadratic (a b p q : ℤ) (hpq : (p, q) ≠ (0, 0)) :
    knappM a b (p + q) (p + 2 * q) = -3 * knappM a b q (p + q) - knappM a b p q ∧
      knappM a b p q ^ 2 + 3 * knappM a b p q * knappM a b q (p + q) +
          knappM a b q (p + q) ^ 2 = ((a ^ 2 + a * b - b ^ 2 : ℤ) : ℚ) := by
  have hmid : (q, p + q) ≠ (0, 0) := by
    intro h
    obtain ⟨hq, hpq'⟩ := Prod.mk.inj h
    apply hpq
    exact Prod.ext (by omega) hq
  have hlast : (p + q, p + 2 * q) ≠ (0, 0) := by
    intro h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    apply hpq
    exact Prod.ext (by omega) (by omega)
  rw [knappM_eq_secondOrderMValue _ _ _ _ hpq, knappM_eq_secondOrderMValue _ _ _ _ hmid,
    knappM_eq_secondOrderMValue _ _ _ _ hlast]
  have hrec := (secondOrderMValue_relations a b 1 (by decide) q (p + q) hmid).1
  have hquad := (secondOrderMValue_relations a b 1 (by decide) p q hpq).2
  rw [one_mul, add_sub_cancel_right, one_mul, show q + (p + q) = p + 2 * q by ring] at hrec
  norm_num at hrec hquad
  push_cast
  constructor
  · linear_combination hrec
  · linear_combination hquad

end MetaMathlibExt
