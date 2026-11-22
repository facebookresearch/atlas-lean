/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.ExtensionOfScalars
public import MathlibExt.CategoryTheory.Monoidal.Mod.MonoidalAdjunction

/-!
# Extension of scalars after a monoidal adjunction

Lift modules through the given monoidal adjunction and then extend scalars.
Both Hom functions use the given monoidal Hom equivalence and the actual
balanced scalar descent. Only target-module coequalizers are required.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.Mod.MonoidalAdjunction

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
  {F : C ⥤ D} {R : D ⥤ C} [F.Monoidal] [R.LaxMonoidal]
  (a : F ⊣ R) [a.IsMonoidal] (A : C) [MonObj A]
  {B : D} [MonObj B] (p : F.obj A ⟶ B) [IsMonHom p]
  [HasCoequalizers (Mod D B)]

/-- The actual monoidal lift and actual scalar induction form the original balanced composite. -/
def extensionOfScalarsAdjunction :
    (Functor.mapMod F A ⋙ Mod.ExtensionOfScalars.induction p) ⊣
      (Mod.ExtensionOfScalars.restriction p ⋙ Mod.MonoidalAdjunction.right a A) :=
  (Mod.MonoidalAdjunction.adjunction a A).comp (Mod.ExtensionOfScalars.adjunction p)

/-- The original module Hom function uses the actual scalar descent and original monoidal Hom function. -/
theorem extensionOfScalarsAdjunction_homEquiv (M : Mod C A) (N : Mod D B)
    (f : (Functor.mapMod F A ⋙ Mod.ExtensionOfScalars.induction p).obj M ⟶ N) :
    (extensionOfScalarsAdjunction a A p).homEquiv M N f =
      (Mod.MonoidalAdjunction.adjunction a A).homEquiv M ((Mod.ExtensionOfScalars.restriction p).obj N)
        (Mod.ExtensionOfScalars.homEquiv p ((Functor.mapMod F A).obj M) N f) := by
  have h := congrFun (congrFun (Adjunction.comp_homEquiv
    (Mod.MonoidalAdjunction.adjunction a A) (Mod.ExtensionOfScalars.adjunction p)) M) N
  have h0 := congrArg (fun e => e f) h
  have h1 := Mod.ExtensionOfScalars.adjunction_homEquiv p ((Functor.mapMod F A).obj M) N
  exact h0.trans (congrArg (fun e =>
    (Mod.MonoidalAdjunction.adjunction a A).homEquiv M ((Mod.ExtensionOfScalars.restriction p).obj N)
      (e f)) h1)

/-- The original inverse module Hom function keeps actual monoidal descent and actual balanced scalar descent. -/
theorem extensionOfScalarsAdjunction_homEquiv_symm (M : Mod C A) (N : Mod D B)
    (g : M ⟶ (Mod.ExtensionOfScalars.restriction p ⋙ Mod.MonoidalAdjunction.right a A).obj N) :
    ((extensionOfScalarsAdjunction a A p).homEquiv M N).symm g =
      (Mod.ExtensionOfScalars.homEquiv p ((Functor.mapMod F A).obj M) N).symm
        (((Mod.MonoidalAdjunction.adjunction a A).homEquiv M
          ((Mod.ExtensionOfScalars.restriction p).obj N)).symm g) := by
  have h := congrFun (congrFun (Adjunction.comp_homEquiv
    (Mod.MonoidalAdjunction.adjunction a A) (Mod.ExtensionOfScalars.adjunction p)) M) N
  have h1 := Mod.ExtensionOfScalars.adjunction_homEquiv p ((Functor.mapMod F A).obj M) N
  have h2 := congrArg (fun e => e.trans
    ((Mod.MonoidalAdjunction.adjunction a A).homEquiv M ((Mod.ExtensionOfScalars.restriction p).obj N))) h1
  exact congrArg (fun e => e.symm g) (h.trans h2)

end CategoryTheory.Mod.MonoidalAdjunction
