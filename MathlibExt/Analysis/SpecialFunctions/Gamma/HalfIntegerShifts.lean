/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.LinearCombination

/-!
# The Gamma function at half-integer shifts

Two evaluations of the Gamma function at half-integer shifts: `Γ(r + 1/2)` through
`Γ(2r + 1) / Γ(r + 1)`, for every complex `r` that is not a negative integer, and a closed form
of `Γ(1/2 - r)`, for every natural number `r`.

The first is Legendre's duplication formula `Complex.Gamma_mul_Gamma_add_half` at `r + 1/2`,
divided by `Γ(r + 1)`. The second follows by induction on `r` from `Γ(s + 1) = s Γ(s)` at
`s = 1/2 - (r + 1)`, from `Γ(1/2) = √π`, and from the recurrence
`(r + 1) C(2r + 2, r + 1) = 2 (2r + 1) C(2r, r)` of the central binomial coefficients.

## Main statements

* `MetaMathlibExt.Gamma_add_half_and_Gamma_half_sub_nat`:
  `Γ(r + 1/2) = √π / 2^(2r) * (Γ(2r + 1) / Γ(r + 1))` for every complex `r` that is not a
  negative integer, and `Γ(1/2 - r) = (-1)^r 2^(2r) √π / (r! C(2r, r))` for every natural `r`.

## References

* Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of Nörlund*,
  INTEGERS 25 (2025), Article A18, Lemma 2.
-/

namespace MetaMathlibExt

@[expose] public section

-- Legendre's duplication formula at `r + 1/2`, divided by `Γ(r + 1) ≠ 0`.
private theorem Gamma_add_half_eq (r : ℂ) (hr : ∀ m : ℕ, r ≠ -((m : ℂ) + 1)) :
    Complex.Gamma (r + 1 / 2) =
      (Real.sqrt Real.pi : ℂ) / (2 : ℂ) ^ (2 * r) *
        (Complex.Gamma (2 * r + 1) / Complex.Gamma (r + 1)) := by
  have hΓ : Complex.Gamma (r + 1) ≠ 0 :=
    Complex.Gamma_ne_zero fun m h ↦ hr m (by linear_combination h)
  have h2 : (2 : ℂ) ^ (2 * r) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have h := Complex.Gamma_mul_Gamma_add_half (r + 1 / 2)
  rw [show (1 : ℂ) - 2 * (r + 1 / 2) = -(2 * r) by ring, show r + 1 / 2 + 1 / 2 = r + 1 by ring,
    show 2 * (r + 1 / 2) = 2 * r + 1 by ring, Complex.cpow_neg] at h
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero h2 hΓ)]
  linear_combination (2 : ℂ) ^ (2 * r) * h +
    Complex.Gamma (2 * r + 1) * (Real.sqrt Real.pi : ℂ) * mul_inv_cancel₀ h2

-- Induction on `r`, stepping down from `1/2 - r` to `1/2 - (r + 1)` with `Γ(s + 1) = s Γ(s)`.
private theorem Gamma_one_half_sub_nat_eq (r : ℕ) :
    Complex.Gamma (1 / 2 - r) =
      (Real.sqrt Real.pi : ℂ) * (-1) ^ r / r.factorial * 2 ^ (2 * r) / (2 * r).choose r := by
  induction r with
  | zero =>
    have hhalf : Complex.Gamma (1 / 2) = (Real.sqrt Real.pi : ℂ) := by
      rw [← Real.Gamma_one_half_eq, ← Complex.Gamma_ofReal]
      norm_num
    rw [Nat.cast_zero, sub_zero, hhalf]
    simp
  | succ r ih =>
    have hs : (1 / 2 : ℂ) - ((r : ℂ) + 1) ≠ 0 := by
      have h2r : ((2 * r + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (2 * r).succ_ne_zero
      intro h
      apply h2r
      push_cast
      linear_combination -2 * h
    have hA : ((2 * r).choose r : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hB : ((2 * (r + 1)).choose (r + 1) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hF : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
    have hr1 : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast r.succ_ne_zero
    have hc : ((r : ℂ) + 1) * ((2 * (r + 1)).choose (r + 1) : ℂ) =
        2 * (2 * r + 1) * ((2 * r).choose r : ℂ) := by
      have h := Nat.succ_mul_centralBinom_succ r
      rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
      exact_mod_cast h
    -- `Γ(1/2 - r) = (1/2 - (r + 1)) Γ(1/2 - (r + 1))`, with the denominators of `ih` cleared.
    have hstep := Complex.Gamma_add_one _ hs
    rw [show (1 / 2 : ℂ) - ((r : ℂ) + 1) + 1 = 1 / 2 - r by ring, ih, div_mul_eq_mul_div,
      div_div, div_eq_iff (mul_ne_zero hF hA)] at hstep
    rw [Nat.factorial_succ]
    push_cast
    rw [div_mul_eq_mul_div, div_div, eq_div_iff (mul_ne_zero (mul_ne_zero hr1 hF) hB)]
    linear_combination (Complex.Gamma (1 / 2 - ((r : ℂ) + 1)) * r.factorial) * hc + 4 * hstep

/-- **The Gamma function at $r + \tfrac12$ and at $\tfrac12 - r$.** For every complex number $r$
that is not a negative integer,
$$\Gamma\bigl(r + \tfrac12\bigr) =
\frac{\sqrt{\pi}}{2^{2r}} \cdot \frac{\Gamma(2r + 1)}{\Gamma(r + 1)},$$
where $2^{2r} = e^{2r \log 2}$; and for every natural number $r$,
$$\Gamma\bigl(\tfrac12 - r\bigr) = \frac{(-1)^r \, 2^{2r} \sqrt{\pi}}{r! \binom{2r}{r}}.$$

In the first identity $\Gamma$ is taken to be $0$ at the non-positive integers, so for
$r = -\tfrac12, -\tfrac32, \dots$ both sides are $0$.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Lemma 2 (`integers-2025-A18-lem-2`). -/
public theorem Gamma_add_half_and_Gamma_half_sub_nat :
    (∀ r : ℂ, (∀ m : ℕ, r ≠ -((m : ℂ) + 1)) →
      Complex.Gamma (r + 1 / 2) =
        (Real.sqrt Real.pi : ℂ) / (2 : ℂ) ^ (2 * r) *
          (Complex.Gamma (2 * r + 1) / Complex.Gamma (r + 1))) ∧
    ∀ r : ℕ, Complex.Gamma (1 / 2 - r) =
      (Real.sqrt Real.pi : ℂ) * (-1) ^ r / r.factorial * 2 ^ (2 * r) / (2 * r).choose r :=
  ⟨Gamma_add_half_eq, Gamma_one_half_sub_nat_eq⟩

end

end MetaMathlibExt
