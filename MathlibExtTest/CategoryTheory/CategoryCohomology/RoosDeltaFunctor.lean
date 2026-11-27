/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.CategoryTheory.CategoryCohomology.RoosDeltaFunctor

/-!
# Degree-zero Roos exactness clients

For an arbitrary index category, sized exact products give a monomorphism on
degree-zero Roos cohomology induced by the first map of a short exact
coefficient row.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.CategoryCohomology

universe v₁ v₂ u₁ u₂

namespace RoosDeltaFunctorTests

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Abelian A]
  [HasProducts.{max u₁ v₁} A] [AB4StarOfSize.{max u₁ v₁} A]

/-- The actual leading map on H0 of Roos complexes is mono, with no global I-limit. -/
example (S : ShortComplex.ShortExactSequences (I ⥤ A)) :
    Mono (HomologicalComplex.homologyMap
      ((roosComplexFunctor (I := I) (A := A)).map S.obj.f) 0) := by
  let T := roosCohomologicalDeltaFunctor (I := I) (A := A)
  let H : (I ⥤ A) ⥤ A := roosComplexFunctor ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) 0
  let e : T.T 0 ≅ H := roosDeltaFunctorHomologyIso (I := I) (A := A) 0
  let e₁ : (T.T 0).obj S.obj.X₁ ≅ H.obj S.obj.X₁ := e.app S.obj.X₁
  let e₂ : (T.T 0).obj S.obj.X₂ ≅ H.obj S.obj.X₂ := e.app S.obj.X₂
  let m : (T.T 0).obj S.obj.X₁ ⟶ (T.T 0).obj S.obj.X₂ := (T.T 0).map S.obj.f
  have : Mono m := T.monoZero S
  have : Mono (e₁.inv ≫ m) := inferInstance
  have h : H.map S.obj.f ≫ e₂.inv = e₁.inv ≫ m := e.inv.naturality S.obj.f
  change Mono (H.map S.obj.f)
  exact mono_of_mono_fac h

end RoosDeltaFunctorTests

end
