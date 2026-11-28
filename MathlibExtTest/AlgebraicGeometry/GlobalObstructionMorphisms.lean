/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GlobalObstructionMorphisms

/-- The global finite-free local model has the correct cohomological support. -/
example (X : Scheme.{0}) (rMinus rZero : ℕ)
    (d : freeModule X rMinus ⟶ freeModule X rZero) :
    IsZero ((twoTerm X rMinus rZero d).X (2 : ℤ)) := by
  rw [twoTerm, CochainComplex.mappingCone.isZero_X_iff]
  constructor <;> exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

/-- Restriction along the same open fixes every actual module section. -/
example {X : Scheme.{0}} (C : Complex X) (U : X.Opens) (i : ℤ) (x : Γ(C.X i, U)) :
    ((MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory.sectionRestriction
      C (le_rfl : U ≤ U)).f i) x = x := by
  change (C.X i).presheaf.map (homOfLE (le_rfl : U ≤ U)).op x = x
  simp
