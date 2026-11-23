/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Monoidal.SInverseSComponentSpace

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject Algebra

universe u v

namespace SInverseSComponentProductTests

open CategoryTheory.SInverseS CategoryTheory.SInverseS.ComponentTranslation

#check exists_pair_difference
#print axioms exists_pair_difference
#check toZero_zero
#print axioms toZero_zero
#check fromZero_zero
#print axioms fromZero_zero
#check componentProperty_eq_stock
#print axioms componentProperty_eq_stock
#check componentDecompositionIsoCat
#print axioms componentDecompositionIsoCat
#check componentDecompositionIsoCat_functor
#print axioms componentDecompositionIsoCat_functor
#check CategoryTheory.decomposedIsoCat_functor
#print axioms CategoryTheory.decomposedIsoCat_functor
#check CategoryTheory.NerveDecomposition.nerveSigmaIso
#print axioms CategoryTheory.NerveDecomposition.nerveSigmaIso
#check originalClassNerveCofanIsColimit
#print axioms originalClassNerveCofanIsColimit
#check originalClassRealizationIso_ι
#print axioms originalClassRealizationIso_ι
#check originalProductHomotopyEquiv
#print axioms originalProductHomotopyEquiv
#check originalProductLeftHomotopyRel
#print axioms originalProductLeftHomotopyRel
#check originalProductRightHomotopyRel
#print axioms originalProductRightHomotopyRel
#check originalProductForward_class
#print axioms originalProductForward_class
#check originalProductInverse_class
#print axioms originalProductInverse_class
#check componentSpace_pathConnected
#print axioms componentSpace_pathConnected
#check zeroPathComponentHomeomorph
#print axioms zeroPathComponentHomeomorph
#check zeroPathComponentHomeomorph_apply
#print axioms zeroPathComponentHomeomorph_apply
#check @zeroSpacePoint_eq_realizedVertex
#print axioms zeroSpacePoint_eq_realizedVertex
#check @originalSpacePoint_eq_realizedVertex
#print axioms originalSpacePoint_eq_realizedVertex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

example : zeroSpacePoint (C := C) =
    SSet.realizedVertex (X := CategoryTheory.nerve (ZeroComponent (C := C)))
      (ComposableArrows.mk₀ (zeroComponentBaseObject (C := C))) :=
  zeroSpacePoint_eq_realizedVertex

example : originalSpacePoint (C := C) =
    SSet.realizedVertex (X := CategoryTheory.nerve (Pair C))
      (ComposableArrows.mk₀ (⟨0, 0⟩ : Pair C)) :=
  originalSpacePoint_eq_realizedVertex

-- The original automatic difference formulas still simplify through the general API.
example (X : Core C × Core C) :
    (differenceFunctor.obj (corePairInclusion.obj X)).as =
      GrothendieckAddGroup.of (toSkeleton X.1.of) -
        GrothendieckAddGroup.of (toSkeleton X.2.of) := by
  simp

example (X : Core C) :
    (differenceFunctor.obj (coreInclusion.obj X)).as =
      GrothendieckAddGroup.of (toSkeleton X.of) := by
  simp

example (g : GrothendieckAddGroup (Skeleton C)) :
    (representative g).difference = g := representative_difference g

example : representative (C := C) 0 = (⟨0, 0⟩ : Pair C) := representative_zero

example (g : GrothendieckAddGroup (Skeleton C)) (X : Component g) :
    (componentDecompositionIsoCat (C := C)).functor.obj ⟨g, X⟩ = X.obj :=
  componentDecompositionIsoCat_obj g X

example (g : GrothendieckAddGroup (Skeleton C)) :
    CategoryTheory.Sigma.incl g ⋙ (componentDecompositionIsoCat (C := C)).functor =
      (componentProperty g).ι := componentDecompositionIsoCat_incl g

example {J : Type u} [Category.{max u v} J] (X : J) :
    (CategoryTheory.decomposedIsoCat J).functor.obj
      ⟨CategoryTheory.ConnectedComponents.mk X, ⟨X, rfl⟩⟩ = X := by
  rw [CategoryTheory.decomposedIsoCat_functor]
  rfl

example (g : GrothendieckAddGroup (Skeleton C)) (z : componentSpace g) :
    originalProductForward
      (SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι) z) =
        (g, componentForward g z) := originalProductForward_class g z

example (g : GrothendieckAddGroup (Skeleton C)) (z : zeroSpace (C := C)) :
    originalProductInverse (g, z) =
      SSet.toTop.map (CategoryTheory.nerveMap (componentProperty g).ι) (componentInverse g z) :=
  originalProductInverse_class g z

example : originalProductForward (originalSpacePoint (C := C)) = componentProductPoint :=
  originalProductForward_point

example : originalProductInverse (componentProductPoint (C := C)) = originalSpacePoint :=
  originalProductInverse_point

example (t : unitInterval) :
    originalProductLeftHomotopyRel (t, originalSpacePoint (C := C)) = originalSpacePoint :=
  originalProductLeftHomotopyRel.eq_snd t (by simp)

example (t : unitInterval) :
    originalProductRightHomotopyRel (t, componentProductPoint (C := C)) = componentProductPoint := by
  let : TopologicalSpace (componentProductSpace (C := C)) :=
    (componentProductSpace (C := C)).str
  exact (originalProductRightHomotopyRel (C := C)).eq_snd t (by simp)

example (z : zeroSpace (C := C)) :
    (zeroPathComponentHomeomorph z : originalSpace (C := C)) =
      SSet.toTop.map (CategoryTheory.nerveMap (componentProperty (C := C) 0).ι) z :=
  zeroPathComponentHomeomorph_apply z

example : zeroPathComponentHomeomorph (zeroSpacePoint (C := C)) =
    ⟨originalSpacePoint, mem_pathComponent_self originalSpacePoint⟩ :=
  zeroPathComponentHomeomorph_point

example {I : Type u} {D : I → Type u} [∀ i, Category.{max u v} (D i)] (i : I) :
    Limits.Sigma.ι (fun i => CategoryTheory.nerve (D i)) i ≫
      (NerveDecomposition.nerveSigmaIso (C := D)).hom =
        CategoryTheory.nerveMap (CategoryTheory.Sigma.incl i) :=
  NerveDecomposition.nerveSigmaIso_ι i

end SInverseSComponentProductTests
