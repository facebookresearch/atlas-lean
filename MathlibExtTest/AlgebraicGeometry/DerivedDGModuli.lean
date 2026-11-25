/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DerivedDGModuliTangentModels
import MathlibExt.AlgebraicGeometry.DerivedOpenSubstacks

open CategoryTheory
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open scoped Simplicial

/-! The source's Reedy boundary is empty in degree zero and has both
distinct vertices in degree one. The degree-one latching diagram must
retain both of these face maps. -/

example (a : LatchingIndex ⦋0⦌) : False := by
  have h := a.property.1
  change a.obj.left.len < 0 at h
  omega

def leftBoundaryVertex : LatchingIndex ⦋1⦌ :=
  ⟨Over.mk (SimplexCategory.δ (0 : Fin 2)), by
    constructor
    · decide
    · intro a b _
      change Fin 1 at a b
      exact Subsingleton.elim a b⟩

def rightBoundaryVertex : LatchingIndex ⦋1⦌ :=
  ⟨Over.mk (SimplexCategory.δ (1 : Fin 2)), by
    constructor
    · decide
    · intro a b _
      change Fin 1 at a b
      exact Subsingleton.elim a b⟩

example : leftBoundaryVertex.obj.hom ≠ rightBoundaryVertex.obj.hom := by
  intro h
  have he := congrArg (fun f : ⦋0⦌ ⟶ ⦋1⦌ => f.toOrderHom 0) h
  change (1 : Fin 2) = 0 at he
  exact (by decide : (1 : Fin 2) ≠ 0) he
