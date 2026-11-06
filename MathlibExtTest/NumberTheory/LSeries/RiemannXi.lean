/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.RiemannXi
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

@[expose] public section

/-!
# Tests for the Riemann xi function

Focused elaboration/API checks: the defining equation, entireness, the
functional equation, agreement with the completed zeta function away from
`s = 0, 1`, nonvanishing on `1 ≤ s.re`, the critical-strip location of zeros,
and the packaged corollary.
-/

namespace RiemannXiTest

/-- The definition unfolds to the stated normalization. -/
example (s : ℂ) :
    RiemannXi.riemannXi s =
      s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2 :=
  rfl

/-- Entireness API. -/
example : Differentiable ℂ RiemannXi.riemannXi :=
  RiemannXi.differentiable_riemannXi

/-- Functional-equation API. -/
example (s : ℂ) : RiemannXi.riemannXi (1 - s) = RiemannXi.riemannXi s :=
  RiemannXi.riemannXi_one_sub s

/-- Agreement with the completed zeta function away from `s = 0, 1`. -/
example {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    RiemannXi.riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s :=
  RiemannXi.riemannXi_eq_mul_completedRiemannZeta hs0 hs1

/-- Nonvanishing on the closed half-plane `1 ≤ s.re`. -/
example {s : ℂ} (hs : 1 ≤ s.re) : RiemannXi.riemannXi s ≠ 0 :=
  RiemannXi.riemannXi_ne_zero_of_one_le_re hs

/-- Zeros have strictly positive real part. -/
example {s : ℂ} (h : RiemannXi.riemannXi s = 0) : 0 < s.re :=
  RiemannXi.re_pos_of_riemannXi_eq_zero h

/-- Zeros have real part strictly less than one. -/
example {s : ℂ} (h : RiemannXi.riemannXi s = 0) : s.re < 1 :=
  RiemannXi.re_lt_one_of_riemannXi_eq_zero h

/-- Zeros lie in the open critical strip. -/
example {s : ℂ} (h : RiemannXi.riemannXi s = 0) : 0 < s.re ∧ s.re < 1 :=
  RiemannXi.riemannXi_mem_strip h

/-- The packaged corollary is available. -/
example :
    Differentiable ℂ RiemannXi.riemannXi ∧
      (∀ s : ℂ, RiemannXi.riemannXi (1 - s) = RiemannXi.riemannXi s) ∧
      ∀ s : ℂ, RiemannXi.riemannXi s = 0 → 0 < s.re ∧ s.re < 1 :=
  RiemannXi.riemannXi_entire_functional_equation_and_critical_strip

/-! ### `riemannZetaNontrivialZeros` -/

/-- `s = 0` is not a nontrivial zero, since `ζ(0) = -1/2`. -/
example : (0 : ℂ) ∉ riemannZetaNontrivialZeros := fun h => by
  have := h.1
  rw [riemannZeta_zero] at this
  norm_num at this

/-- The pole `s = 1` is not a nontrivial zero (Mathlib's junk value `ζ(1)` is nonzero). -/
example : (1 : ℂ) ∉ riemannZetaNontrivialZeros := fun h => riemannZeta_one_ne_zero h.1

/-- The trivial zero `s = -2` is excluded. -/
example : riemannZeta (-2) = 0 ∧ (-2 : ℂ) ∉ riemannZetaNontrivialZeros := by
  refine ⟨?_, fun h => by have := h.2.1; norm_num at this⟩
  simpa using riemannZeta_neg_two_mul_nat_add_one 0

/-- `ξ(0) = ξ(1) = 1/2`, consistent with `riemannXi_eq_zero_iff` at the excluded points. -/
example : RiemannXi.riemannXi 0 ≠ 0 ∧ RiemannXi.riemannXi 1 ≠ 0 := by
  constructor <;> simp [RiemannXi.riemannXi]

/-- The zeros of `ξ` are the nontrivial zeros of `ζ`. -/
example (s : ℂ) : RiemannXi.riemannXi s = 0 ↔ riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 :=
  RiemannXi.riemannXi_eq_zero_iff s

/-- A nontrivial zero lies in the open strip. -/
example {s : ℂ} (hs : s ∈ riemannZetaNontrivialZeros) : 0 < s.re ∧ s.re < 1 :=
  RiemannXi.riemannXi_mem_strip ((RiemannXi.riemannXi_eq_zero_iff s).mpr hs)

end RiemannXiTest
