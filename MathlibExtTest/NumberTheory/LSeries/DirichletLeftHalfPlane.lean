/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.DirichletLeftHalfPlane

/-!
# Tests for `L'/L` on the left half-plane

The parity of a character, the nonvanishing of the root number, and the bound for `L'/L` on
`Re s ≥ 2` at the character mod `1`.
-/

@[expose] public section

open DirichletCharacter

namespace DirichletLeftHalfPlaneTest

/-- The trivial character mod `1` is even: its parity is `a = 0`. -/
example : ∃ a : ℝ, a = 0 ∧ (1 - (1 : DirichletCharacter ℂ 1) (-1)) / 2 = (a : ℂ) := by
  obtain ⟨a, ha, hpar, -, -⟩ := exists_parity_gammaFactor_eq (1 : DirichletCharacter ℂ 1)
  refine ⟨a, ?_, hpar⟩
  rcases ha with rfl | rfl
  · rfl
  · exfalso
    have : (1 : DirichletCharacter ℂ 1) (-1) = 1 := MulChar.one_apply (isUnit_of_subsingleton _)
    rw [this] at hpar
    norm_num at hpar

example : (1 : DirichletCharacter ℂ 1).rootNumber ≠ 0 :=
  isPrimitive_one_level_one.rootNumber_ne_zero

/-- `‖ζ'/ζ(s)‖ ≤ ∑ Λ(n)/n²` on `Re s ≥ 2`, via the character mod `1`. -/
example {s : ℂ} (hs : 2 ≤ s.re) : ‖deriv riemannZeta s / riemannZeta s‖ ≤
    ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 n‖ := by
  simpa using norm_logDeriv_LFunction_le_of_two_le_re (1 : DirichletCharacter ℂ 1) hs

/-- The cofactor `H` of `L = ξ H` is entire. -/
example (q : ℕ) [NeZero q] : Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ (-((s + 1) / 2)) *
    ((Real.pi : ℂ) ^ ((s + 1) / 2) * (Complex.Gamma ((s + 1) / 2))⁻¹)) := by
  simpa using differentiable_xi_cofactor q 1

end DirichletLeftHalfPlaneTest
