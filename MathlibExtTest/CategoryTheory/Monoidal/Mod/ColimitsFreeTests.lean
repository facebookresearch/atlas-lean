/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Monoidal.Mod.ColimitsFree

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe w v u

namespace MathlibExtTest.CategoryTheory.Mod.ColimitsFree

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable (A : C) [MonObj A]

section PublicSurface

#check Mod.forgetCreatesLimits
#check Mod.forgetCreatesReflexiveCoequalizers
#check Mod.forgetCreatesColimits
#check Mod.hasLimits
#check Mod.hasColimits
#check Mod.free
#check Mod.freeForgetAdjunction
#check Mod.free_obj
#check Mod.free_map
#check Mod.freeForgetAdjunction_unit_app
#check Mod.freeForgetAdjunction_counit_app_hom
#check Mod.freeForgetAdjunction_homEquiv_symm_apply_hom
#check Mod.freeForgetAdjunction_homEquiv_apply
#check Mod.isLocallyPresentable

#check @Mod.forgetCreatesLimits.{1, 1, 1}
#check @Mod.forgetCreatesLimits.{0, 0, 0}
#check @Mod.forgetCreatesReflexiveCoequalizers.{1, 1}
#check @Mod.forgetCreatesReflexiveCoequalizers.{0, 0}
#check @Mod.forgetCreatesColimits.{1, 1, 1}
#check @Mod.forgetCreatesColimits.{0, 0, 0}
#check @Mod.hasLimits.{1, 1, 1}
#check @Mod.hasLimits.{0, 0, 0}
#check @Mod.hasColimits.{1, 1, 1}
#check @Mod.hasColimits.{0, 0, 0}
#check @Mod.free.{1, 1}
#check @Mod.free.{0, 0}
#check @Mod.freeForgetAdjunction.{1, 1}
#check @Mod.freeForgetAdjunction.{0, 0}
#check @Mod.free_obj.{1, 1}
#check @Mod.free_obj.{0, 0}
#check @Mod.free_map.{1, 1}
#check @Mod.free_map.{0, 0}
#check @Mod.freeForgetAdjunction_unit_app.{1, 1}
#check @Mod.freeForgetAdjunction_unit_app.{0, 0}
#check @Mod.freeForgetAdjunction_counit_app_hom.{1, 1}
#check @Mod.freeForgetAdjunction_counit_app_hom.{0, 0}
#check @Mod.freeForgetAdjunction_homEquiv_symm_apply_hom.{1, 1}
#check @Mod.freeForgetAdjunction_homEquiv_symm_apply_hom.{0, 0}
#check @Mod.freeForgetAdjunction_homEquiv_apply.{1, 1}
#check @Mod.freeForgetAdjunction_homEquiv_apply.{0, 0}
#check @Mod.isLocallyPresentable.{1, 1, 1}
#check @Mod.isLocallyPresentable.{0, 0, 0}

end PublicSurface

section TensorMonadComparison

#check Mod.toTensorMonadAlgebra
#check Mod.ofTensorMonadAlgebra
#check Mod.tensorMonadEquivalence
#check @Mod.toTensorMonadAlgebra.{1, 1}
#check @Mod.toTensorMonadAlgebra.{0, 0}
#check @Mod.ofTensorMonadAlgebra.{1, 1}
#check @Mod.ofTensorMonadAlgebra.{0, 0}
#check @Mod.tensorMonadEquivalence.{1, 1}
#check @Mod.tensorMonadEquivalence.{0, 0}

example : Mod C A ⥤ (Monad.tensorMonad A).Algebra :=
  Mod.toTensorMonadAlgebra A

example : (Monad.tensorMonad A).Algebra ⥤ Mod C A :=
  Mod.ofTensorMonadAlgebra A

example : Mod C A ≌ (Monad.tensorMonad A).Algebra :=
  Mod.tensorMonadEquivalence A

example : (Mod.tensorMonadEquivalence A).functor =
    Mod.toTensorMonadAlgebra A := rfl

example : (Mod.tensorMonadEquivalence A).inverse =
    Mod.ofTensorMonadAlgebra A := rfl

example (M : Mod C A) :
    ((Mod.tensorMonadEquivalence A).functor.obj M).A = M.X := rfl

example (X : (Monad.tensorMonad A).Algebra) :
    ((Mod.tensorMonadEquivalence A).inverse.obj X).X = X.A := rfl

example (M : Mod C A) :
    ((Mod.toTensorMonadAlgebra A).obj M).a =
      ModObj.smul (M := A) (X := M.X) := rfl

example (X : (Monad.tensorMonad A).Algebra) :
    ((Mod.ofTensorMonadAlgebra A).obj X).mod.smul = X.a := rfl

example {M N : Mod C A} (f : M ⟶ N) :
    ((Mod.toTensorMonadAlgebra A).map f).f = f.hom := rfl

example {X Y : (Monad.tensorMonad A).Algebra} (f : X ⟶ Y) :
    ((Mod.ofTensorMonadAlgebra A).map f).hom = f.f := rfl

example (M : Mod C A) :
    (Monad.tensorMonad A).η.app M.X ≫
        ((Mod.toTensorMonadAlgebra A).obj M).a = 𝟙 M.X :=
  ((Mod.toTensorMonadAlgebra A).obj M).unit

example (X : (Monad.tensorMonad A).Algebra) :
    (MonObj.one ▷ X.A) ≫
        ((Mod.ofTensorMonadAlgebra A).obj X).mod.smul = (λ_ X.A).hom := by
  let _ : ModObj A X.A := ((Mod.ofTensorMonadAlgebra A).obj X).mod
  exact ModObj.one_smul_self A X.A

example (M : Mod C A) :
    ((Mod.tensorMonadEquivalence A).unitIso.app M).hom.hom = 𝟙 M.X := rfl

example (M : Mod C A) :
    ((Mod.tensorMonadEquivalence A).unitIso.app M).inv.hom = 𝟙 M.X := rfl

example (X : (Monad.tensorMonad A).Algebra) :
    ((Mod.tensorMonadEquivalence A).counitIso.app X).hom.f = 𝟙 X.A := rfl

example (X : (Monad.tensorMonad A).Algebra) :
    ((Mod.tensorMonadEquivalence A).counitIso.app X).inv.f = 𝟙 X.A := rfl

#print axioms Mod.toTensorMonadAlgebra
#print axioms Mod.ofTensorMonadAlgebra
#print axioms Mod.tensorMonadEquivalence

end TensorMonadComparison

section CreatedLimits

variable {J : Type w} [Category.{w} J]

example (F : J ⥤ Mod C A) : CreatesLimit F (Mod.forget A) := by
  let _ := Mod.forgetCreatesLimits.{w} A
  infer_instance

example (F : Discrete.{w} PEmpty ⥤ Mod C A) :
    CreatesLimit F (Mod.forget A) := by
  let _ := Mod.forgetCreatesLimits.{w} A
  infer_instance

example (F : Discrete.{w} PUnit ⥤ Mod C A) :
    CreatesLimit F (Mod.forget A) := by
  let _ := Mod.forgetCreatesLimits.{w} A
  infer_instance

example (F : Discrete.{w} (ULift.{w} (Fin 2)) ⥤ Mod C A) :
    CreatesLimit F (Mod.forget A) := by
  let _ := Mod.forgetCreatesLimits.{w} A
  infer_instance

example (F : WalkingParallelPair ⥤ Mod C A) :
    CreatesLimit F (Mod.forget A) := by
  let _ := Mod.forgetCreatesLimits.{0} A
  infer_instance

example (F : WalkingCospan ⥤ Mod C A) :
    CreatesLimit F (Mod.forget A) := by
  let _ := Mod.forgetCreatesLimits.{0} A
  infer_instance

example [HasLimitsOfSize.{w, w} C] :
    HasLimitsOfSize.{w, w} (Mod C A) :=
  Mod.hasLimits A

end CreatedLimits

section ConditionalColimits

variable [PreservesColimitsOfSize.{w, w} (tensorLeft A)]

example : CreatesColimitsOfSize.{w, w} (Mod.forget (D := C) A) :=
  Mod.forgetCreatesColimits A

example [HasColimitsOfSize.{w, w} C] :
    HasColimitsOfSize.{w, w} (Mod C A) :=
  Mod.hasColimits A

end ConditionalColimits

section ReflexiveCreation

variable [Monad.PreservesColimitOfIsReflexivePair (tensorLeft A)]

example (M : Mod C A) :
    CreatesColimit (parallelPair (𝟙 M) (𝟙 M)) (Mod.forget A) := by
  let _ : IsReflexivePair (𝟙 M) (𝟙 M) :=
    IsReflexivePair.mk' (𝟙 M) (by simp) (by simp)
  exact Mod.forgetCreatesReflexiveCoequalizers A (𝟙 M) (𝟙 M)

example [HasReflexiveCoequalizers C] (M : Mod C A) :
    HasColimit (parallelPair (𝟙 M) (𝟙 M)) := by
  let _ : IsReflexivePair (𝟙 M) (𝟙 M) :=
    IsReflexivePair.mk' (𝟙 M) (by simp) (by simp)
  let _ : IsReflexivePair (𝟙 M.X) (𝟙 M.X) :=
    IsReflexivePair.mk' (𝟙 M.X) (by simp) (by simp)
  let _ : HasColimit
      ((parallelPair (𝟙 M) (𝟙 M)) ⋙ Mod.forget A) := by
    rw [hasColimit_iff_of_iso (diagramIsoParallelPair _)]
    exact inferInstanceAs (HasCoequalizer (𝟙 M.X) (𝟙 M.X))
  let _ := Mod.forgetCreatesReflexiveCoequalizers A (𝟙 M) (𝟙 M)
  exact hasColimit_of_created (parallelPair (𝟙 M) (𝟙 M))
    (Mod.forget A)

example {M N : Mod C A} (_f _g : M ⟶ N) : True := by
  fail_if_success
    let _ : CreatesColimit (parallelPair _f _g) (Mod.forget A) :=
      Mod.forgetCreatesReflexiveCoequalizers A _f _g
  trivial

example : True := by
  fail_if_success
    let _ : CreatesColimitsOfSize.{w, w} (Mod.forget A) :=
      Mod.forgetCreatesColimits A
  trivial

end ReflexiveCreation

section FreeFormulas

variable {X Y : C} (f : X ⟶ Y)

example : ((Mod.free A).obj X).X = A ⊗ X := Mod.free_obj A X

example : eqToHom (Mod.free_obj A X) ≫ (A ◁ f) =
    ((Mod.free A).map f).hom ≫ eqToHom (Mod.free_obj A Y) :=
  Mod.free_map A f

example : (Mod.freeForgetAdjunction A).unit.app X =
    (λ_ X).inv ≫ (η[A] ▷ X) ≫ eqToHom (Mod.free_obj A X).symm :=
  Mod.freeForgetAdjunction_unit_app A X

example (M : Mod C A) :
    ((Mod.freeForgetAdjunction A).counit.app M).hom =
      eqToHom (Mod.free_obj A M.X) ≫ M.mod.smul :=
  Mod.freeForgetAdjunction_counit_app_hom A M

example (M : Mod C A) (g : X ⟶ M.X) :
    (((Mod.freeForgetAdjunction A).homEquiv X M).symm g).hom =
      eqToHom (Mod.free_obj A X) ≫ (A ◁ g) ≫ M.mod.smul :=
  Mod.freeForgetAdjunction_homEquiv_symm_apply_hom A M g

example (M : Mod C A) (k : (Mod.free A).obj X ⟶ M) :
    (Mod.freeForgetAdjunction A).homEquiv X M k =
      (λ_ X).inv ≫ (η[A] ▷ X) ≫
        eqToHom (Mod.free_obj A X).symm ≫ k.hom :=
  Mod.freeForgetAdjunction_homEquiv_apply A M k

end FreeFormulas

section UnderlyingIsomorphism

example {M N : Mod C A} (f : M ⟶ N) [IsIso f.hom] : IsIso f := by
  let fInv : N ⟶ M := Mod.Hom.mk' (inv f.hom) (by
    change N.mod.smul ≫ inv f.hom =
      (A ◁ inv f.hom) ≫ M.mod.smul
    rw [← cancel_mono f.hom]
    simp [Category.assoc])
  exact ⟨⟨fInv, by
    apply Mod.hom_ext
    change f.hom ≫ inv f.hom = 𝟙 M.X
    simp, by
    apply Mod.hom_ext
    change inv f.hom ≫ f.hom = 𝟙 N.X
    simp⟩⟩

end UnderlyingIsomorphism

section Presentability

variable [IsLocallyPresentable.{w} C]
variable [PreservesColimitsOfSize.{w, w} (tensorLeft A)]

example : IsLocallyPresentable.{w} (Mod C A) :=
  Mod.isLocallyPresentable A

end Presentability

section NoGlobalInstances

example : True := by
  fail_if_success
    let _ : HasLimitsOfSize.{w, w} (Mod C A) := inferInstance
  fail_if_success
    let _ : IsLocallyPresentable.{w} (Mod C A) := inferInstance
  trivial

end NoGlobalInstances

section PrivateAndNonclaims

#guard_msgs (error, substring := true) in
#check Mod.freeHomEquiv

#guard_msgs (error, substring := true) in
#check Mod.forgetReflectsIsomorphisms

#guard_msgs (error, substring := true) in
#check Mod.forgetMonadic

#guard_msgs (error, substring := true) in
#check Mod.forgetIsCardinalAccessible

#guard_msgs (error, substring := true) in
#check Mod.freeStrongGenerator

#guard_msgs (error, substring := true) in
#check Mod.relativeTensor

#guard_msgs (error, substring := true) in
#check ModuleCat

end PrivateAndNonclaims

#print axioms Mod.forgetCreatesLimits
#print axioms Mod.forgetCreatesReflexiveCoequalizers
#print axioms Mod.forgetCreatesColimits
#print axioms Mod.hasLimits
#print axioms Mod.hasColimits
#print axioms Mod.free
#print axioms Mod.freeForgetAdjunction
#print axioms Mod.free_obj
#print axioms Mod.free_map
#print axioms Mod.freeForgetAdjunction_unit_app
#print axioms Mod.freeForgetAdjunction_counit_app_hom
#print axioms Mod.freeForgetAdjunction_homEquiv_symm_apply_hom
#print axioms Mod.freeForgetAdjunction_homEquiv_apply
#print axioms Mod.isLocallyPresentable

#lint- only unusedArguments in MathlibExt.CategoryTheory.Monoidal.Mod.ColimitsFree

end MathlibExtTest.CategoryTheory.Mod.ColimitsFree
