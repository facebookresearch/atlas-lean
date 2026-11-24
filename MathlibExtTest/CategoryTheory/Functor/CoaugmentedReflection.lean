/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
import MathlibExt.CategoryTheory.Functor.CoaugmentedReflection
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory

namespace MathlibExtTest.CoaugmentedReflection

/-- Every complete public source root keeps its actual module and kernel kind. -/
def expectedKernelKinds : Array (Lean.Name × Lean.Name × String) := #[
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.map_unit_eq_unit_obj, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.unitHomEquiv, "def"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.unitHomEquiv_apply, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.unitHomEquiv_symm_apply, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.unitHomEquiv_source, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.unitHomEquiv_source_symm, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.unitHomEquiv_target, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.unitHomEquiv_target_symm, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.precomp_unit_bijective, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.map_isIso_iff_fixed_homtests, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.unitHomEquiv_characteristic, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.unitHomEquiv_right_triangle, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.unitHomEquiv_left_triangle, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.testFunctor, "def"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.testUnitIso, "def"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.testHomEquiv, "def"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.testHomEquiv_apply, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.testHomEquiv_symm_apply, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.testAdjunction, "def"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.testAdjunction_unit_app, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.testAdjunction_counit_app, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.testAdjunction_left_triangle, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.testAdjunction_right_triangle, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.testAdjunction_homEquiv_apply, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedReflection,
    `CategoryTheory.Functor.CoaugmentedReflection.testAdjunction_homEquiv, "theorem")
]

run_cmd do
  let env ← Lean.getEnv
  unless expectedKernelKinds.size == 25 do throwError "incomplete source surface"
  for (m, n, expectedKind) in expectedKernelKinds do
    let idx ← match env.getModuleIdx? m with
      | some i => pure i
      | none => throwError "missing actual source module {m}"
    let info ← match env.find? n with
      | some ci => pure ci
      | none => throwError "missing complete public source root {n}"
    unless env.getModuleIdxFor? n == some idx do throwError "wrong actual source module {n}"
    let kind := match info with
      | .defnInfo _ => "def"
      | .thmInfo _ => "theorem"
      | _ => "other"
    unless kind == expectedKind do throwError "wrong actual source kind {n} {kind}"
    Lean.logInfo m!"FULL_PUBLIC_COAUGMENTED_MODULE_KIND {m} {n} {kind} {idx.toNat}"
    Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent n)))


open CategoryTheory.Functor.CoaugmentedReflection
variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ C) (η : 𝟭 C ⟶ F)
variable (hunit : ∀ X, IsIso (η.app (F.obj X)))
variable (hmap : ∀ X, IsIso (F.map (η.app X)))

include hunit hmap in
example (X : C) : F.map (η.app X) = η.app (F.obj X) :=
  map_unit_eq_unit_obj F η hunit hmap X
example (X Z : C) [IsIso (η.app Z)] :
    (unitHomEquiv F η hunit hmap X Z).toFun = fun g => η.app X ≫ g := rfl
example (X Z : C) [IsIso (η.app Z)] :
    (unitHomEquiv F η hunit hmap X Z).invFun =
      fun f => F.map f ≫ CategoryTheory.inv (η.app Z) := rfl
example (X Z : C) [IsIso (η.app Z)] (g : F.obj X ⟶ Z) :
    (unitHomEquiv F η hunit hmap X Z).symm
      (unitHomEquiv F η hunit hmap X Z g) = g :=
  (unitHomEquiv F η hunit hmap X Z).symm_apply_apply g
example (X Z : C) [IsIso (η.app Z)] (f : X ⟶ Z) :
    unitHomEquiv F η hunit hmap X Z ((unitHomEquiv F η hunit hmap X Z).symm f) = f :=
  (unitHomEquiv F η hunit hmap X Z).apply_symm_apply f
example (X X' Z : C) [IsIso (η.app Z)] (a : X' ⟶ X) (g : F.obj X ⟶ Z) :
    unitHomEquiv F η hunit hmap X' Z (F.map a ≫ g) =
      a ≫ unitHomEquiv F η hunit hmap X Z g :=
  unitHomEquiv_source F η hunit hmap a Z g
example (X X' Z : C) [IsIso (η.app Z)] (a : X' ⟶ X) (f : X ⟶ Z) :
    (unitHomEquiv F η hunit hmap X' Z).symm (a ≫ f) =
      F.map a ≫ (unitHomEquiv F η hunit hmap X Z).symm f :=
  unitHomEquiv_source_symm F η hunit hmap a Z f
example (X Z Z' : C) [IsIso (η.app Z)] [IsIso (η.app Z')]
    (b : Z ⟶ Z') (g : F.obj X ⟶ Z) :
    unitHomEquiv F η hunit hmap X Z' (g ≫ b) =
      unitHomEquiv F η hunit hmap X Z g ≫ b :=
  unitHomEquiv_target F η hunit hmap X b g
example (X Z Z' : C) [IsIso (η.app Z)] [IsIso (η.app Z')]
    (b : Z ⟶ Z') (f : X ⟶ Z) :
    (unitHomEquiv F η hunit hmap X Z').symm (f ≫ b) =
      (unitHomEquiv F η hunit hmap X Z).symm f ≫ b :=
  unitHomEquiv_target_symm F η hunit hmap X b f
example (X Z : C) [IsIso (η.app Z)] (f : X ⟶ Z) (g : F.obj X ⟶ Z) :
    (unitHomEquiv F η hunit hmap X Z).symm f = g ↔ η.app X ≫ g = f :=
  unitHomEquiv_characteristic F η hunit hmap X Z f g
include hunit hmap in
example (X Z : C) [IsIso (η.app Z)] (f : X ⟶ Z) :
    η.app X ≫ (F.map f ≫ CategoryTheory.inv (η.app Z)) = f :=
  unitHomEquiv_right_triangle F η hunit hmap X Z f
include hunit hmap in
example (X Z : C) [IsIso (η.app Z)] (g : F.obj X ⟶ Z) :
    F.map (η.app X ≫ g) ≫ CategoryTheory.inv (η.app Z) = g :=
  unitHomEquiv_left_triangle F η hunit hmap X Z g
include hunit hmap in
example (X Z : C) [IsIso (η.app Z)] :
    Function.Bijective (fun g : F.obj X ⟶ Z => η.app X ≫ g) :=
  precomp_unit_bijective F η hunit hmap X Z

variable (P : ObjectProperty C) (himage : ∀ X, P (F.obj X))
variable (hfixed : ∀ Z, P Z → IsIso (η.app Z))

example (X : C) : ((testFunctor F P himage).obj X).obj = F.obj X := rfl
example {X Y : C} (f : X ⟶ Y) : ((testFunctor F P himage).map f).hom = F.map f := rfl
example (X : C) : (testFunctor F P himage).map (𝟙 X) =
    𝟙 ((testFunctor F P himage).obj X) := (testFunctor F P himage).map_id X
example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (testFunctor F P himage).map (f ≫ g) =
    (testFunctor F P himage).map f ≫ (testFunctor F P himage).map g :=
  (testFunctor F P himage).map_comp f g
example (Z : P.FullSubcategory) : (testUnitIso F η P hfixed Z).hom = η.app Z.obj := rfl
example (X : C) (Z : P.FullSubcategory) (g : (testFunctor F P himage).obj X ⟶ Z) :
    testHomEquiv F η hunit hmap P himage hfixed X Z g = η.app X ≫ g.hom :=
  testHomEquiv_apply F η hunit hmap P himage hfixed X Z g
example (X : C) (Z : P.FullSubcategory) (f : X ⟶ Z.obj) :
    ((testHomEquiv F η hunit hmap P himage hfixed X Z).symm f).hom =
      F.map f ≫ (testUnitIso F η P hfixed Z).inv :=
  testHomEquiv_symm_apply F η hunit hmap P himage hfixed X Z f
example (X : C) : (testAdjunction F η hunit hmap P himage hfixed).unit.app X = η.app X :=
  testAdjunction_unit_app F η hunit hmap P himage hfixed X
example (Z : P.FullSubcategory) :
    ((testAdjunction F η hunit hmap P himage hfixed).counit.app Z).hom =
      (testUnitIso F η P hfixed Z).inv :=
  testAdjunction_counit_app F η hunit hmap P himage hfixed Z
example (X : C) : (testFunctor F P himage).map (η.app X) ≫
    (testAdjunction F η hunit hmap P himage hfixed).counit.app
      ((testFunctor F P himage).obj X) = 𝟙 ((testFunctor F P himage).obj X) :=
  testAdjunction_left_triangle F η hunit hmap P himage hfixed X
example (Z : P.FullSubcategory) :
    η.app Z.obj ≫ ((testAdjunction F η hunit hmap P himage hfixed).counit.app Z).hom = 𝟙 Z.obj :=
  testAdjunction_right_triangle F η hunit hmap P himage hfixed Z
example (X : C) (Z : P.FullSubcategory) :
    (testAdjunction F η hunit hmap P himage hfixed).homEquiv X Z =
      testHomEquiv F η hunit hmap P himage hfixed X Z :=
  testAdjunction_homEquiv F η hunit hmap P himage hfixed X Z
include η hunit hmap himage hfixed in
example {X Y : C} (f : X ⟶ Y) : IsIso (F.map f) ↔
    ∀ Z, P Z → Function.Bijective (fun g : Y ⟶ Z => f ≫ g) :=
  map_isIso_iff_fixed_homtests F η hunit hmap P himage hfixed f

end MathlibExtTest.CoaugmentedReflection
