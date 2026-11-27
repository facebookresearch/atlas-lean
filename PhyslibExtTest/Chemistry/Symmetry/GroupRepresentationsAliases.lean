/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Symmetry.GroupRepresentations

/-!
# Deprecated cross-product names in `PhyslibExt.Chemistry.Symmetry.GroupRepresentations`

The cross-product transformation law moved to `MathlibExt.LinearAlgebra.CrossProduct`. Its
former names `Chemistry.Symmetry.mulVec_cross_mulVec` and
`Chemistry.Symmetry.mulVec_cross_mulVec_of_mem_orthogonalGroup` stay available, as deprecated
aliases, to a file that imports only the chemistry module:

* each former name has the statement of its `Matrix` replacement;
* a proof written against the former names still checks.
-/

@[expose] public section

namespace Chemistry.Symmetry.GroupRepresentationsAliasesTest

open scoped Matrix

-- The pre-move names still elaborate, as deprecated aliases with the same statements.
set_option linter.deprecated false in
example : @Chemistry.Symmetry.mulVec_cross_mulVec = @Matrix.mulVec_cross_mulVec := rfl

set_option linter.deprecated false in
example : @Chemistry.Symmetry.mulVec_cross_mulVec_of_mem_orthogonalGroup =
    @Matrix.mulVec_cross_mulVec_of_mem_orthogonalGroup := rfl

-- A downstream proof written against the pre-move names: for orthogonal `Q` the cofactor
-- matrix acts on cross products as `det Q • Q`.
set_option linter.deprecated false in
example {Q : Matrix (Fin 3) (Fin 3) ℝ} (hQ : Q ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (a b : Fin 3 → ℝ) :
    (Matrix.adjugate Q)ᵀ *ᵥ (a ⨯₃ b) = Q.det • (Q *ᵥ (a ⨯₃ b)) := by
  rw [← Chemistry.Symmetry.mulVec_cross_mulVec,
    Chemistry.Symmetry.mulVec_cross_mulVec_of_mem_orthogonalGroup hQ]

end Chemistry.Symmetry.GroupRepresentationsAliasesTest
