/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.LocallyFinite.FiniteSupport

/-!
# Noncommutative ideal and original common-unit clients
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe uR

namespace Matrix.LocallyFinite.SourceClients.FiniteSupport

variable {R : Type uR} [Semiring R]

/-- The actual left-ideal interface accepts arbitrary original left matrix multiplication. -/
theorem original_left_ideal (A : Matrix.LocallyFinite ℕ ℕ R) (N : ℕ) :
    A * finiteProjection N ∈ finiteSupportIdeal :=
  (finiteSupportIdeal (n := ℕ) (R := R)).mul_mem_left A (hasFiniteSupport_finiteProjection N)

/-- The actual two-sided instance accepts arbitrary original right matrix multiplication. -/
theorem original_right_ideal (A : Matrix.LocallyFinite ℕ ℕ R) (N : ℕ) :
    finiteProjection N * A ∈ finiteSupportIdeal :=
  (finiteSupportIdeal (n := ℕ) (R := R)).mul_mem_right A (hasFiniteSupport_finiteProjection N)

/-- A common actual projection keeps both original multiplication directions on two matrices. -/
theorem original_two_matrix_unit (A B : Matrix.LocallyFinite ℕ ℕ R)
    (hA : HasFiniteSupport A) (hB : HasFiniteSupport B) :
    ∃ N : ℕ, finiteProjection N * A = A ∧ A * finiteProjection N = A ∧
      finiteProjection N * B = B ∧ B * finiteProjection N = B := by
  let F : Bool → Matrix.LocallyFinite ℕ ℕ R := fun b => if b then A else B
  have hF : ∀ b, HasFiniteSupport (F b) := by
    intro b
    cases b <;> assumption
  obtain ⟨N, hN⟩ := exists_common_finiteProjection_local_unit F hF
  exact ⟨N, (hN true).1, (hN true).2, (hN false).1, (hN false).2⟩

/-- The original finite matrix keeps its actual row and column cutoff. -/
theorem actual_finite_cutoff (A : Matrix.LocallyFinite ℕ ℕ R) (hA : A ∈ finiteSupportIdeal) :
    ∃ N : ℕ, ∀ i j, N ≤ i ∨ N ≤ j → A i j = 0 := exists_bound_of_hasFiniteSupport hA

end Matrix.LocallyFinite.SourceClients.FiniteSupport

end
