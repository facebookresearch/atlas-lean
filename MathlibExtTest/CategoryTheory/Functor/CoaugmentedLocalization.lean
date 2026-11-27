/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
import MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization
import MathlibExtTest.CategoryTheory.Functor.CoaugmentedReflection
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory

namespace MathlibExtTest.CoaugmentedLocalization

/-- Every complete public source root keeps its actual module and kernel kind. -/
def expectedKernelKinds : Array (Lean.Name × Lean.Name × String) := #[
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.inverts, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.localizedFunctor, "def"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.localizedFunctor_obj, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.localizedFunctor_map, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.mappedUnit, "def"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.localizedUnit, "def"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.localizedUnit_app, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.localizedUnit_obj_isIso, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.localizedFunctor_unit_isIso, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv, "def"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_apply, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_symm_apply, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.precomp_unit_bijective, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.map_isIso_iff_homtests, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_source, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_source_symm, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_target, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_target_symm, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.localizedFunctor_unit_eq, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_source_hom, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_source_hom_symm, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_characteristic, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_right_triangle, "theorem"),
  (`MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization,
    `CategoryTheory.Functor.CoaugmentedLocalization.unitHomEquiv_left_triangle, "theorem")
]

run_cmd do
  let env ← Lean.getEnv
  unless expectedKernelKinds.size == 24 do throwError "incomplete source surface"
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


open CategoryTheory.Functor.CoaugmentedLocalization
variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) (F : C ⥤ C) (η : 𝟭 C ⟶ F)
variable (hpreserve : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → W (F.map f))
variable (hunit : ∀ X, W (η.app (F.obj X)))
variable (hmap : ∀ X, W (F.map (η.app X)))

example (X : C) : (localizedFunctor W F hpreserve).obj (W.Q.obj X) = W.Q.obj (F.obj X) :=
  localizedFunctor_obj W F hpreserve X
example {X Y : C} (f : X ⟶ Y) :
    (localizedFunctor W F hpreserve).map (W.Q.map f) = W.Q.map (F.map f) :=
  localizedFunctor_map W F hpreserve f
example (X : C) : (mappedUnit W F η).app X = W.Q.map (η.app X) := rfl
example (X : C) : (localizedUnit W F η hpreserve).app (W.Q.obj X) = W.Q.map (η.app X) :=
  localizedUnit_app W F η hpreserve X
example (X : W.Localization) : (localizedFunctor W F hpreserve).map (𝟙 X) =
    𝟙 ((localizedFunctor W F hpreserve).obj X) := (localizedFunctor W F hpreserve).map_id X
example {X Y Z : W.Localization} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (localizedFunctor W F hpreserve).map (f ≫ g) =
      (localizedFunctor W F hpreserve).map f ≫ (localizedFunctor W F hpreserve).map g :=
  (localizedFunctor W F hpreserve).map_comp f g
include hunit in
example (X : W.Localization) : IsIso ((localizedUnit W F η hpreserve).app
    ((localizedFunctor W F hpreserve).obj X)) :=
  localizedUnit_obj_isIso W F η hpreserve hunit X
include hmap in
example (X : W.Localization) : IsIso ((localizedFunctor W F hpreserve).map
    ((localizedUnit W F η hpreserve).app X)) :=
  localizedFunctor_unit_isIso W F η hpreserve hmap X
include hunit hmap in
example (X : W.Localization) :
    (localizedFunctor W F hpreserve).map ((localizedUnit W F η hpreserve).app X) =
      (localizedUnit W F η hpreserve).app ((localizedFunctor W F hpreserve).obj X) :=
  localizedFunctor_unit_eq W F η hpreserve hunit hmap X
example (X Z : C) (hZ : W (η.app Z)) (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    unitHomEquiv W F η hpreserve hunit hmap X Z hZ g = W.Q.map (η.app X) ≫ g :=
  unitHomEquiv_apply W F η hpreserve hunit hmap X Z hZ g
example (X Z : C) (hZ : W (η.app Z)) (g : W.Q.obj X ⟶ W.Q.obj Z) :
    (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm g =
      (localizedFunctor W F hpreserve).map g ≫
        (Localization.Construction.wIso (η.app Z) hZ).inv :=
  unitHomEquiv_symm_apply W F η hpreserve hunit hmap X Z hZ g
example (X Z : C) (hZ : W (η.app Z)) (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm
      (unitHomEquiv W F η hpreserve hunit hmap X Z hZ g) = g :=
  (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm_apply_apply g
example (X Z : C) (hZ : W (η.app Z)) (f : W.Q.obj X ⟶ W.Q.obj Z) :
    unitHomEquiv W F η hpreserve hunit hmap X Z hZ
      ((unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm f) = f :=
  (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).apply_symm_apply f
example (X X' Z : C) (a : X' ⟶ X) (hZ : W (η.app Z))
    (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    unitHomEquiv W F η hpreserve hunit hmap X' Z hZ (W.Q.map (F.map a) ≫ g) =
      W.Q.map a ≫ unitHomEquiv W F η hpreserve hunit hmap X Z hZ g :=
  unitHomEquiv_source W F η hpreserve hunit hmap a Z hZ g
example (X X' Z : C) (a : X' ⟶ X) (hZ : W (η.app Z)) (g : W.Q.obj X ⟶ W.Q.obj Z) :
    (unitHomEquiv W F η hpreserve hunit hmap X' Z hZ).symm (W.Q.map a ≫ g) =
      W.Q.map (F.map a) ≫ (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm g :=
  unitHomEquiv_source_symm W F η hpreserve hunit hmap a Z hZ g
example (X X' Z : C) (a : W.Q.obj X' ⟶ W.Q.obj X) (hZ : W (η.app Z))
    (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    unitHomEquiv W F η hpreserve hunit hmap X' Z hZ
      ((localizedFunctor W F hpreserve).map a ≫ g) =
      a ≫ unitHomEquiv W F η hpreserve hunit hmap X Z hZ g :=
  unitHomEquiv_source_hom W F η hpreserve hunit hmap X X' Z a hZ g
example (X X' Z : C) (a : W.Q.obj X' ⟶ W.Q.obj X) (hZ : W (η.app Z))
    (g : W.Q.obj X ⟶ W.Q.obj Z) :
    (unitHomEquiv W F η hpreserve hunit hmap X' Z hZ).symm (a ≫ g) =
      (localizedFunctor W F hpreserve).map a ≫
        (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm g :=
  unitHomEquiv_source_hom_symm W F η hpreserve hunit hmap X X' Z a hZ g
example (X Z Z' : C) (hZ : W (η.app Z)) (hZ' : W (η.app Z'))
    (b : W.Q.obj Z ⟶ W.Q.obj Z') (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    unitHomEquiv W F η hpreserve hunit hmap X Z' hZ' (g ≫ b) =
      unitHomEquiv W F η hpreserve hunit hmap X Z hZ g ≫ b :=
  unitHomEquiv_target W F η hpreserve hunit hmap X Z Z' hZ hZ' b g
example (X Z Z' : C) (hZ : W (η.app Z)) (hZ' : W (η.app Z'))
    (b : W.Q.obj Z ⟶ W.Q.obj Z') (g : W.Q.obj X ⟶ W.Q.obj Z) :
    (unitHomEquiv W F η hpreserve hunit hmap X Z' hZ').symm (g ≫ b) =
      (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm g ≫ b :=
  unitHomEquiv_target_symm W F η hpreserve hunit hmap X Z Z' hZ hZ' b g
example (X Z : C) (hZ : W (η.app Z)) (f : W.Q.obj X ⟶ W.Q.obj Z)
    (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    (unitHomEquiv W F η hpreserve hunit hmap X Z hZ).symm f = g ↔
      W.Q.map (η.app X) ≫ g = f :=
  unitHomEquiv_characteristic W F η hpreserve hunit hmap X Z hZ f g
include hpreserve hunit hmap in
example (X Z : C) (hZ : W (η.app Z)) (f : W.Q.obj X ⟶ W.Q.obj Z) :
    W.Q.map (η.app X) ≫ ((localizedFunctor W F hpreserve).map f ≫
      (Localization.Construction.wIso (η.app Z) hZ).inv) = f :=
  unitHomEquiv_right_triangle W F η hpreserve hunit hmap X Z hZ f
include hunit hmap in
example (X Z : C) (hZ : W (η.app Z)) (g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z) :
    (localizedFunctor W F hpreserve).map (W.Q.map (η.app X) ≫ g) ≫
      (Localization.Construction.wIso (η.app Z) hZ).inv = g :=
  unitHomEquiv_left_triangle W F η hpreserve hunit hmap X Z hZ g
include hpreserve hunit hmap in
example (X Z : C) (hZ : W (η.app Z)) :
    Function.Bijective (fun g : W.Q.obj (F.obj X) ⟶ W.Q.obj Z => W.Q.map (η.app X) ≫ g) :=
  precomp_unit_bijective W F η hpreserve hunit hmap X Z hZ

variable (P : C → Prop) (himage : ∀ X, P (F.obj X))
variable (hfixed : ∀ Z, P Z → W (η.app Z))
include η hpreserve hunit hmap himage hfixed in
example {X Y : C} (f : X ⟶ Y) : IsIso (W.Q.map (F.map f)) ↔
    ∀ Z, P Z → Function.Bijective (fun g : W.Q.obj Y ⟶ W.Q.obj Z => W.Q.map f ≫ g) :=
  map_isIso_iff_homtests W F η hpreserve hunit hmap P himage hfixed f

end MathlibExtTest.CoaugmentedLocalization
