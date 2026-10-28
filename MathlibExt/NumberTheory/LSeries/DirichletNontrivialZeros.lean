/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The nontrivial zeros of a Dirichlet `L`-function

The nontrivial zeros of `L(s, χ)` are its zeros in the closed critical strip `0 ≤ Re s ≤ 1`,
other than `s = 0`. For a primitive even nonprincipal `χ`, `s = 0` is a trivial zero of `L(s, χ)`,
cancelled in the completed `L`-function by the pole of `Γ(s / 2)`.

The set is a `Set ℂ`: zeros are counted without multiplicity.

## Main definitions

* `DirichletCharacter.nontrivialZeros χ`: the nontrivial zeros of `L(s, χ)`.

## Main statements

* `DirichletCharacter.re_lt_one_of_mem_nontrivialZeros`: nontrivial zeros lie in `Re s < 1`
  (except possibly the junk value at the pole `s = 1` of the principal `L`-function).
-/

@[expose] public section

namespace DirichletCharacter

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- The **nontrivial zeros** of the Dirichlet `L`-function `L(s, χ)`: the zeros of
`DirichletCharacter.LFunction χ` in the closed critical strip `0 ≤ Re s ≤ 1`, other than `s = 0`.
Primitivity and nonprincipality are not part of the definition; they are hypotheses of the
statements that need them. -/
def nontrivialZeros : Set ℂ :=
  {s | LFunction χ s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ s ≠ 0}

variable {χ}

/-- Membership in the nontrivial zeros, unfolded. -/
theorem mem_nontrivialZeros {s : ℂ} :
    s ∈ χ.nontrivialZeros ↔ LFunction χ s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ s ≠ 0 :=
  Iff.rfl

/-- A nontrivial zero is a zero of `L(s, χ)`. -/
theorem LFunction_eq_zero_of_mem_nontrivialZeros {s : ℂ} (hs : s ∈ χ.nontrivialZeros) :
    LFunction χ s = 0 :=
  hs.1

/-- Nontrivial zeros lie in the half-plane `Re s < 1`, by the nonvanishing of `L(s, χ)` on
`Re s ≥ 1`. The point `s = 1` for the principal character, where `LFunction` takes a junk value
at the pole, is excluded. -/
theorem re_lt_one_of_mem_nontrivialZeros {s : ℂ} (hs : s ∈ χ.nontrivialZeros)
    (hχs : χ ≠ 1 ∨ s ≠ 1) : s.re < 1 := by
  by_contra h
  exact LFunction_ne_zero_of_one_le_re χ hχs (not_lt.mp h) hs.1

end DirichletCharacter
