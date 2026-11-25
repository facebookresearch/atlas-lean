/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.Algebra.Category.ModuleCat.MonoidAction
import Mathlib.Algebra.Homology.Additive

open CategoryTheory
open scoped MonoidAlgebra

noncomputable section

universe u v w

namespace Action

variable {M : Type u} [Monoid M]
variable {A B : Action AddCommGrpCat.{v} M}

example (m : M) (x : A.V) :
    intRepresentation M A m x = (A.ρ m).asHom.hom x :=
  intRepresentation_apply M A m x

example (f : A ⟶ B) (x : A.V) :
    (intRepMap M f).hom x = f.hom.hom x :=
  intRepMap_apply M f x

example :
    Action AddCommGrpCat.{v} M ⥤ ModuleCat.{v} (MonoidAlgebra ℤ M) :=
  monoidAlgebraModuleFunctor M

example : (monoidAlgebraModuleFunctor.{u, v} M).Additive :=
  inferInstance

example {I : Type w} (c : ComplexShape I) :
    HomologicalComplex (Action AddCommGrpCat.{v} M) c ⥤
      HomologicalComplex (ModuleCat.{v} (MonoidAlgebra ℤ M)) c :=
  (monoidAlgebraModuleFunctor M).mapHomologicalComplex c

example :
    monoidAlgebraModuleFunctor.{u, v} M ⋙
        forget₂ (ModuleCat.{v} (MonoidAlgebra ℤ M)) AddCommGrpCat.{v} ≅
      Action.forget AddCommGrpCat.{v} M :=
  monoidAlgebraModuleForgetIso M

example (C : Action AddCommGrpCat.{v} M) (x : C.V) :
    (monoidAlgebraModuleForgetIso M).inv.app C x =
      (intRepresentation M C).asModuleEquiv.symm x :=
  monoidAlgebraModuleForgetIso_inv_apply M C x

example (C : Action AddCommGrpCat.{v} M) (m : M) (z : ℤ)
    (x : (monoidAlgebraModuleFunctor M).obj C) :
    (monoidAlgebraModuleForgetIso M).hom.app C
        (MonoidAlgebra.single m z • x) =
      z • (C.ρ m).asHom.hom ((monoidAlgebraModuleForgetIso M).hom.app C x) :=
  monoidAlgebraModuleForgetIso_single_smul M C m z x

example (C : Action AddCommGrpCat.{v} M) (m : M)
    (x : (monoidAlgebraModuleFunctor M).obj C) :
    (monoidAlgebraModuleForgetIso M).hom.app C
        (MonoidAlgebra.of ℤ M m • x) =
      (C.ρ m).asHom.hom ((monoidAlgebraModuleForgetIso M).hom.app C x) :=
  monoidAlgebraModuleForgetIso_of_smul M C m x

example (f : A ⟶ B) :
    ((monoidAlgebraModuleFunctor M ⋙
          forget₂ (ModuleCat.{v} (MonoidAlgebra ℤ M)) AddCommGrpCat.{v}).map f) ≫
        (monoidAlgebraModuleForgetIso M).hom.app B =
      (monoidAlgebraModuleForgetIso M).hom.app A ≫ f.hom :=
  (monoidAlgebraModuleForgetIso M).hom.naturality f

section Trivial

variable (M)

def trivialIntAction : Action AddCommGrpCat M :=
  Action.trivial M (AddCommGrpCat.of ℤ)

example (m : M)
    (x : (monoidAlgebraModuleFunctor M).obj (trivialIntAction M)) :
    (monoidAlgebraModuleForgetIso M).hom.app (trivialIntAction M)
        (MonoidAlgebra.of ℤ M m • x) =
      (monoidAlgebraModuleForgetIso M).hom.app (trivialIntAction M) x := by
  rw [monoidAlgebraModuleForgetIso_of_smul]
  have hρ : ((trivialIntAction M).ρ m).asHom = 𝟙 _ := by
    rfl
  rw [hρ]
  simp

end Trivial

#print axioms Action.intRepresentation
#print axioms Action.intRepFunctor
#print axioms Action.monoidAlgebraModuleFunctor
#print axioms Action.monoidAlgebraModuleFunctor_additive
#print axioms Action.monoidAlgebraModuleForgetIso
#print axioms Action.monoidAlgebraModuleForgetIso_inv_apply
#print axioms Action.monoidAlgebraModuleForgetIso_single_smul
#print axioms Action.monoidAlgebraModuleForgetIso_of_smul

end Action
