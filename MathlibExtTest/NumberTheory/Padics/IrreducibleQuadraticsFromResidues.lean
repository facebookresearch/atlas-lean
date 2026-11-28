/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.IrreducibleQuadraticsFromResidues

/-!
# Tests for irreducible quadratics over $\mathbb{Q}_p$ from residues in $U_p$
-/

set_option autoImplicit false

@[expose] public section

open Polynomial

namespace IrreducibleQuadraticsFromResiduesTest

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The statement, with the source's binders. -/
example {p : ℕ} [Fact p.Prime] {s : ℤ_[p]}
    (hs : PadicInt.toZMod s ∈ FiniteField.tracesOfIrreducibleQuadratics (ZMod p)) :
    Irreducible (X ^ 2 - C (s : ℚ_[p]) * X + 1 : ℚ_[p][X]) :=
  Padic.irreducible_X_sq_sub_C_mul_X_add_one_of_toZMod_mem hs

/-- $x^2 + 1$ is irreducible over $\mathbb{Q}_3$, as $0 \in U_3$. -/
example : Irreducible (X ^ 2 + 1 : ℚ_[3][X]) := by
  have h := Padic.irreducible_X_sq_sub_C_mul_X_add_one_of_toZMod_mem (p := 3) (s := 0)
    (by rw [map_zero]; exact FiniteField.mem_tracesOfIrreducibleQuadratics_iff.2 (by decide))
  simpa using h

/-- $x^2 - 3x + 1$ is irreducible over $\mathbb{Q}_7$, as $3 \in U_7$. -/
example : Irreducible (X ^ 2 - C (3 : ℚ_[7]) * X + 1 : ℚ_[7][X]) := by
  have h := Padic.irreducible_X_sq_sub_C_mul_X_add_one_of_toZMod_mem (p := 7) (s := 3)
    (by rw [map_ofNat]; exact FiniteField.mem_tracesOfIrreducibleQuadratics_iff.2 (by decide))
  rwa [show ((3 : ℤ_[7]) : ℚ_[7]) = 3 by norm_cast] at h

#check @Padic.irreducible_X_sq_sub_C_mul_X_add_one_of_toZMod_mem

end IrreducibleQuadraticsFromResiduesTest
