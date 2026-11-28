/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic

/-!
# The standard representation of the general linear group

For a finite type `n` and a commutative ring `R`, the group `GL_n(R)` acts `R`-linearly on
column vectors `Rⁿ = n → R` by `g • v = g *ᵥ v`. This is the standard representation
`Matrix.GeneralLinearGroup.stdRep n R : Representation R (GL n R) (n → R)`, and
`Matrix.GeneralLinearGroup.stdRep_apply` is its defining equation.
-/

@[expose] public section

set_option autoImplicit false

namespace Matrix.GeneralLinearGroup

/-- The **standard representation** of `GL_n(R)` on `Rⁿ = n → R`, by `g • v = g *ᵥ v`. -/
noncomputable def stdRep (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
    Representation R (GL n R) (n → R) :=
  (Units.coeHom _).comp toLin.toMonoidHom

/-- The standard representation acts by matrix-vector multiplication. -/
@[simp]
theorem stdRep_apply (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R]
    (g : GL n R) (v : n → R) : stdRep n R g v = (g : Matrix n n R).mulVec v :=
  rfl

end Matrix.GeneralLinearGroup

end
