/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Cross-universe nerve maps and homotopies

For `A : Type (max u v)` with `Category.{v} A` and `B : Type u` with
`Category.{v} B`, a functor `F : A ⥤ B` induces a simplicial map
`nerveMapCross F : nerve A ⟶ nerve B`, both nerves in `SSet.{max u v}`
definitionally. A natural transformation induces a simplicial homotopy
with endpoint laws. Component formulas reuse `Functor.mapComposableArrows`,
the cylinder reuses `Prod.swap` with `Functor.uncurry.obj (ComposableArrows.mk₁ α)`,
and endpoints reuse `SSet.Homotopy`, matching the same-universe packet.

For categories whose objects live in one common ambient universe but whose
hom types live in independent universes, `nerveMapHomDown` gives the direct
map of nerves.  It has identity and composition laws, including mixed laws
with `nerveMap`, and natural transformations induce homotopies compatible
with pre- and postcomposition.  The intended application lowers the hom
universe, although the common-ambient construction itself is symmetric in
the two hom universes.

For `nerveMapCross`, the existing nonclaims remain: no Cross-Cross composition,
general ordinary/Cross bridge, up-universe, or pre/postcomposition family
beyond its two mixed laws.  The file introduces no second nerve representation,
realization, equivalence, or additivity claim.

For functors between categories in fully arbitrary universes,
`SSet.nerveMapULift` gives the `ULift`-conjugated nerve map between the
lifted nerves, with identity, shared-level composition, and vertex/edge
coordinate laws.  It agrees with the ordinary `nerveMap` and with
`nerveMapHomDown` / `nerveMapCross` wherever those apply (the lift squares
commute definitionally), so comma-level change-of-universe constructions can
be built on this adapter without restating it.
-/

@[expose] public section

open CategoryTheory Simplicial MonoidalCategory Opposite
open scoped CategoryTheory.Prod

universe v u w v₁ v₂ v₃

namespace CategoryTheory

variable {A : Type (max u v)} [Category.{v} A] {B : Type u} [Category.{v} B]

/-- Cross-universe nerve map for the down-universe direction. -/
def nerveMapCross (F : A ⥤ B) : nerve A ⟶ nerve B where
  app _ := ↾fun X => (F.mapComposableArrows _).obj X

/-- Action on a `mk₀` simplex. -/
theorem nerveMapCross_app_mk₀ (F : A ⥤ B) (x : A) :
    (nerveMapCross F).app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
      ComposableArrows.mk₀ (F.obj x) :=
  ComposableArrows.ext₀ rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Action on a `mk₁` simplex. -/
theorem nerveMapCross_app_mk₁ {F : A ⥤ B} {x y : A} (f : x ⟶ y) :
    (nerveMapCross F).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ (F.map f) :=
  ComposableArrows.ext₁ rfl rfl (by simp [nerveMapCross])

/-- Ordinary-then-Cross composition: `nerveMap` between `Type (max u v)` categories
followed by down-universe `nerveMapCross` into `Type u` collapses to `nerveMapCross`
of the composed functor. -/
theorem nerveMap_nerveMapCross_comp {X Y : Type (max u v)} [Category.{v} X]
    [Category.{v} Y] {Z : Type u} [Category.{v} Z] (F : X ⥤ Y) (G : Y ⥤ Z) :
    nerveMap F ≫ nerveMapCross G = nerveMapCross (F ⋙ G) := by
  ext Δ X
  rfl

/-- Cross-then-ordinary composition: down-universe `nerveMapCross` out of
`Type (max u v)` followed by same-universe `nerveMap` within `Type u` collapses to
`nerveMapCross` of the composed functor. -/
theorem nerveMapCross_nerveMap_comp {X : Type (max u v)} [Category.{v} X]
    {Y Z : Type u} [Category.{v} Y] [Category.{v} Z] (F : X ⥤ Y) (G : Y ⥤ Z) :
    nerveMapCross F ≫ nerveMap G = nerveMapCross (F ⋙ G) := by
  ext Δ X
  rfl

/-- At coinciding universes, the cross-universe nerve map is the ordinary
nerve map: both whisker with `Functor.mapComposableArrows`. -/
theorem nerveMapCross_eq_nerveMap {A B : Type u} [Category.{0} A]
    [Category.{0} B] (F : A ⥤ B) :
    nerveMapCross F = nerveMap F := by
  ext Δ X
  rfl

namespace NatTrans

variable {F G : A ⥤ B}

/-- The cross-universe cylinder functor classified by a natural transformation. -/
def nerveCylinderFunctorCross (α : F ⟶ G) : A × Fin 2 ⥤ B :=
  Prod.swap A (Fin 2) ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α)

/-- The cylinder functor agrees with `F` at the `0` endpoint. -/
@[simp]
lemma nerveCylinderFunctorCross_obj_zero (α : F ⟶ G) (X : A) :
    (nerveCylinderFunctorCross α).obj (X, 0) = F.obj X :=
  rfl

/-- The cylinder functor agrees with `G` at the `1` endpoint. -/
@[simp]
lemma nerveCylinderFunctorCross_obj_one (α : F ⟶ G) (X : A) :
    (nerveCylinderFunctorCross α).obj (X, 1) = G.obj X :=
  rfl

/-- The cylinder functor acts as `F` on morphisms over the `0` endpoint. -/
@[simp]
lemma nerveCylinderFunctorCross_map_zero (α : F ⟶ G) {X Y : A} (f : X ⟶ Y) :
    (nerveCylinderFunctorCross α).map (f ×ₘ 𝟙 (0 : Fin 2)) = F.map f := by
  simp only [nerveCylinderFunctorCross, Functor.comp_map, Prod.swap_map,
    Functor.uncurry_obj_map]
  change 𝟙 (F.obj X) ≫ F.map f = F.map f
  simp

/-- The cylinder functor acts as `G` on morphisms over the `1` endpoint. -/
@[simp]
lemma nerveCylinderFunctorCross_map_one (α : F ⟶ G) {X Y : A} (f : X ⟶ Y) :
    (nerveCylinderFunctorCross α).map (f ×ₘ 𝟙 (1 : Fin 2)) = G.map f := by
  simp only [nerveCylinderFunctorCross, Functor.comp_map, Prod.swap_map,
    Functor.uncurry_obj_map]
  change 𝟙 (G.obj X) ≫ G.map f = G.map f
  simp

/-- The cross-universe cylinder map on nerves. -/
def nerveHomotopyMapCross (α : F ⟶ G) : nerve A ⊗ Δ[1] ⟶ nerve B where
  app _ := ↾fun X =>
    ((nerveCylinderFunctorCross α).mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)

/-- The second component of the `ι₀` endpoint inclusion is constant `0`. -/
private lemma asOrderHomCross_ι₀_app_snd {Δ : SimplexCategoryᵒᵖ} (X : (nerve A).obj Δ) :
    (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor =
      (Functor.const (Fin (Δ.unop.len + 1))).obj (0 : Fin 2) := by
  rfl

/-- The second component of the `ι₁` endpoint inclusion is constant `1`. -/
private lemma asOrderHomCross_ι₁_app_snd {Δ : SimplexCategoryᵒᵖ} (X : (nerve A).obj Δ) :
    (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor =
      (Functor.const (Fin (Δ.unop.len + 1))).obj (1 : Fin 2) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation induces a simplicial homotopy between the
cross-universe nerve maps. -/
noncomputable def nerveHomotopyCross (α : F ⟶ G) :
    SSet.Homotopy (nerveMapCross F) (nerveMapCross G) where
  h := nerveHomotopyMapCross α
  h₀ := by
    change SSet.ι₀ ≫ nerveHomotopyMapCross α = nerveMapCross F
    ext Δ X
    change ((nerveCylinderFunctorCross α).mapComposableArrows _).obj
        ((SSet.ι₀.app Δ X).1.prod'
          (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor) =
      (F.mapComposableArrows _).obj X
    have hinput :
        (SSet.ι₀.app Δ X).1.prod'
            (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor =
          X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj (0 : Fin 2)) :=
      congrArg₂ (fun A B => A.prod' B) (SSet.ι₀_app_fst X)
        (asOrderHomCross_ι₀_app_snd X)
    rw [hinput]
    refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
    · rfl
    · simp only [ComposableArrows.map', Functor.mapComposableArrows_obj_map,
        Functor.prod'_map, Functor.const_obj_map, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      exact nerveCylinderFunctorCross_map_zero α _
  h₁ := by
    change SSet.ι₁ ≫ nerveHomotopyMapCross α = nerveMapCross G
    ext Δ X
    change ((nerveCylinderFunctorCross α).mapComposableArrows _).obj
        ((SSet.ι₁.app Δ X).1.prod'
          (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor) =
      (G.mapComposableArrows _).obj X
    have hinput :
        (SSet.ι₁.app Δ X).1.prod'
            (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor =
          X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj (1 : Fin 2)) :=
      congrArg₂ (fun A B => A.prod' B) (SSet.ι₁_app_fst X)
        (asOrderHomCross_ι₁_app_snd X)
    rw [hinput]
    refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
    · rfl
    · simp only [ComposableArrows.map', Functor.mapComposableArrows_obj_map,
        Functor.prod'_map, Functor.const_obj_map, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      exact nerveCylinderFunctorCross_map_one α _
  rel := by
    ext Δ X
    exact X.1.2.elim

end NatTrans

section HomDown

variable {C D : Type (max w v₁ v₂)} [Category.{v₁} C] [Category.{v₂} D]

/-- A functor between categories with a common ambient object universe and
independent hom universes induces a map of nerves.  The main application is
from a large-hom category to a small-hom category. -/
def nerveMapHomDown (F : C ⥤ D) : nerve C ⟶ nerve D where
  app _ := ↾fun X => (F.mapComposableArrows _).obj X

/-- `nerveMapHomDown` acts on vertices by the object map. -/
theorem nerveMapHomDown_app_mk₀ (F : C ⥤ D) (x : C) :
    (nerveMapHomDown F).app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
      ComposableArrows.mk₀ (F.obj x) :=
  ComposableArrows.ext₀ rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `nerveMapHomDown` acts on edges by the morphism map. -/
theorem nerveMapHomDown_app_mk₁ {F : C ⥤ D} {x y : C} (f : x ⟶ y) :
    (nerveMapHomDown F).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ (F.map f) :=
  ComposableArrows.ext₁ rfl rfl (by simp [nerveMapHomDown])

/-- When the hom universes agree, `nerveMapHomDown` is the ordinary
`nerveMap`. -/
theorem nerveMapHomDown_eq_nerveMap
    {C D : Type (max w v₁)} [Category.{v₁} C] [Category.{v₁} D]
    (F : C ⥤ D) :
    nerveMapHomDown F = nerveMap F := by
  ext Δ X
  rfl

/-- `nerveMapHomDown` sends an identity functor to the identity map. -/
@[simp]
theorem nerveMapHomDown_id
    {C : Type (max w v₁)} [Category.{v₁} C] :
    nerveMapHomDown (𝟭 C) = 𝟙 (nerve C) := by
  ext Δ X
  rfl

/-- `nerveMapHomDown` sends a composite of arbitrary-hom-universe functors
to the composite of their nerve maps.

The `nolint` is a documented false positive: the left-hand side pins
cross-universe `max`-levels, so simpNF's self-application check cannot match
it, but the lemma does fire at concrete universe levels (pinned by the
`LegacyCompatibility` test closing by `simp` alone). -/
@[simp, nolint simpNF]
theorem nerveMapHomDown_comp
    {C D E : Type (max w v₁ v₂ v₃)}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMapHomDown.{max w v₃, v₁, v₂} F ≫
        nerveMapHomDown.{max w v₁, v₂, v₃} G =
      nerveMapHomDown.{max w v₂, v₁, v₃} (F ⋙ G) := by
  ext Δ X
  rfl

/-- Ordinary-then-HomDown composition collapses to the HomDown map of the
composite functor. -/
theorem nerveMap_nerveMapHomDown_comp
    {C D E : Type (max w v₁ v₂)}
    [Category.{v₁} C] [Category.{v₁} D] [Category.{v₂} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMap F ≫ nerveMapHomDown G = nerveMapHomDown (F ⋙ G) := by
  ext Δ X
  rfl

/-- HomDown-then-ordinary composition collapses to the HomDown map of the
composite functor. -/
theorem nerveMapHomDown_nerveMap_comp
    {C D E : Type (max w v₁ v₂)}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₂} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMapHomDown F ≫ nerveMap G = nerveMapHomDown (F ⋙ G) := by
  ext Δ X
  rfl

namespace NatTrans

variable {F G : C ⥤ D}

/-- The common-ambient, mixed-hom-universe cylinder functor classified by a
natural transformation. -/
def nerveCylinderFunctorHomDown (α : F ⟶ G) : C × Fin 2 ⥤ D :=
  Prod.swap C (Fin 2) ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α)

/-- The HomDown cylinder functor agrees with `F` at the `0` endpoint. -/
@[simp]
lemma nerveCylinderFunctorHomDown_obj_zero (α : F ⟶ G) (X : C) :
    (nerveCylinderFunctorHomDown α).obj (X, 0) = F.obj X :=
  rfl

/-- The HomDown cylinder functor agrees with `G` at the `1` endpoint. -/
@[simp]
lemma nerveCylinderFunctorHomDown_obj_one (α : F ⟶ G) (X : C) :
    (nerveCylinderFunctorHomDown α).obj (X, 1) = G.obj X :=
  rfl

/-- The HomDown cylinder functor acts as `F` on morphisms at `0`. -/
@[simp]
lemma nerveCylinderFunctorHomDown_map_zero
    (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    (nerveCylinderFunctorHomDown α).map (f ×ₘ 𝟙 (0 : Fin 2)) = F.map f := by
  simp only [nerveCylinderFunctorHomDown, Functor.comp_map, Prod.swap_map,
    Functor.uncurry_obj_map]
  change 𝟙 (F.obj X) ≫ F.map f = F.map f
  simp

/-- The HomDown cylinder functor acts as `G` on morphisms at `1`. -/
@[simp]
lemma nerveCylinderFunctorHomDown_map_one
    (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    (nerveCylinderFunctorHomDown α).map (f ×ₘ 𝟙 (1 : Fin 2)) = G.map f := by
  simp only [nerveCylinderFunctorHomDown, Functor.comp_map, Prod.swap_map,
    Functor.uncurry_obj_map]
  change 𝟙 (G.obj X) ≫ G.map f = G.map f
  simp

/-- The mixed-hom-universe cylinder map on nerves. -/
def nerveHomotopyMapHomDown (α : F ⟶ G) : nerve C ⊗ Δ[1] ⟶ nerve D where
  app _ := ↾fun X =>
    ((nerveCylinderFunctorHomDown α).mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)

/-- The HomDown cylinder map commutes strictly with precomposition. -/
theorem nerveHomotopyMapHomDown_precomp
    {X C D : Type (max w v₁ v₂ v₃)}
    [Category.{v₁} X] [Category.{v₂} C] [Category.{v₃} D]
    {F G : C ⥤ D} (K : X ⥤ C) (α : F ⟶ G) :
    (nerveMapHomDown.{max w v₃, v₁, v₂} K ▷
        (Δ[1] : SSet.{max w v₁ v₂ v₃})) ≫
      nerveHomotopyMapHomDown.{max w v₁, v₂, v₃} α =
        nerveHomotopyMapHomDown.{max w v₂, v₁, v₃}
          (Functor.whiskerLeft K α) := by
  ext Δ X
  change ((nerveCylinderFunctorHomDown.{max w v₁, v₂, v₃}
      α).mapComposableArrows _).obj
      (((nerveMapHomDown.{max w v₃, v₁, v₂} K).app Δ X.1).prod'
        (SSet.stdSimplex.asOrderHom X.2).toFunctor) =
    ((nerveCylinderFunctorHomDown.{max w v₂, v₁, v₃}
      (Functor.whiskerLeft K α)).mapComposableArrows _).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)
  have h_cyl : nerveCylinderFunctorHomDown.{max w v₂, v₁, v₃}
        (Functor.whiskerLeft K α) =
      (K.prod (𝟭 (Fin 2))) ⋙
        nerveCylinderFunctorHomDown.{max w v₁, v₂, v₃} α := by
    apply Functor.hext
    · rintro ⟨X, i⟩
      fin_cases i <;> rfl
    · rintro ⟨X, i⟩ ⟨Y, j⟩ f
      rcases f with ⟨f, g⟩
      fin_cases i
      · fin_cases j
        · apply heq_of_eq
          simp [nerveCylinderFunctorHomDown, ComposableArrows.mk₁]
        · apply heq_of_eq
          simp [nerveCylinderFunctorHomDown, ComposableArrows.mk₁]
      · fin_cases j
        · exfalso
          have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom g
          omega
        · apply heq_of_eq
          simp [nerveCylinderFunctorHomDown, ComposableArrows.mk₁]
  rw [h_cyl]
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    apply heq_of_eq
    simp only [nerveMapHomDown]
    rfl

/-- The HomDown cylinder map commutes strictly with postcomposition. -/
theorem nerveHomotopyMapHomDown_postcomp
    {C D E : Type (max w v₁ v₂ v₃)}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    {F G : C ⥤ D} (α : F ⟶ G) (L : D ⥤ E) :
    nerveHomotopyMapHomDown.{max w v₃, v₁, v₂} α ≫
        nerveMapHomDown.{max w v₁, v₂, v₃} L =
      nerveHomotopyMapHomDown.{max w v₂, v₁, v₃}
        (Functor.whiskerRight α L) := by
  ext Δ X
  change ((L.mapComposableArrows _).obj
      (((nerveCylinderFunctorHomDown.{max w v₃, v₁, v₂}
        α).mapComposableArrows _).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor))) =
    ((nerveCylinderFunctorHomDown.{max w v₂, v₁, v₃}
      (Functor.whiskerRight α L)).mapComposableArrows _).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)
  have h_cyl : nerveCylinderFunctorHomDown.{max w v₂, v₁, v₃}
        (Functor.whiskerRight α L) =
      nerveCylinderFunctorHomDown.{max w v₃, v₁, v₂} α ⋙ L := by
    apply Functor.hext
    · rintro ⟨X, i⟩
      fin_cases i <;> rfl
    · rintro ⟨X, i⟩ ⟨Y, j⟩ f
      rcases f with ⟨f, g⟩
      fin_cases i
      · fin_cases j
        · apply heq_of_eq
          simp [nerveCylinderFunctorHomDown, ComposableArrows.mk₁]
        · apply heq_of_eq
          simp [nerveCylinderFunctorHomDown, ComposableArrows.mk₁]
      · fin_cases j
        · exfalso
          have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom g
          omega
        · apply heq_of_eq
          simp [nerveCylinderFunctorHomDown, ComposableArrows.mk₁]
  rw [h_cyl]
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    apply heq_of_eq
    rfl

/-- The second component of the HomDown `ι₀` endpoint is constant `0`. -/
private lemma asOrderHomHomDown_ι₀_app_snd
    {C₀ : Type u} [Category.{v} C₀]
    {Δ : SimplexCategoryᵒᵖ} (X : (nerve C₀).obj Δ) :
    (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor =
      (Functor.const (Fin (Δ.unop.len + 1))).obj (0 : Fin 2) := by
  rfl

/-- The second component of the HomDown `ι₁` endpoint is constant `1`. -/
private lemma asOrderHomHomDown_ι₁_app_snd
    {C₀ : Type u} [Category.{v} C₀]
    {Δ : SimplexCategoryᵒᵖ} (X : (nerve C₀).obj Δ) :
    (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor =
      (Functor.const (Fin (Δ.unop.len + 1))).obj (1 : Fin 2) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation induces a simplicial homotopy between the
common-ambient, mixed-hom-universe nerve maps. -/
noncomputable def nerveHomotopyHomDown (α : F ⟶ G) :
    SSet.Homotopy (nerveMapHomDown.{w, v₁, v₂} F)
      (nerveMapHomDown.{w, v₁, v₂} G) where
  h := nerveHomotopyMapHomDown.{w, v₁, v₂} α
  h₀ := by
    change SSet.ι₀ ≫ nerveHomotopyMapHomDown.{w, v₁, v₂} α =
      nerveMapHomDown.{w, v₁, v₂} F
    ext Δ X
    change ((nerveCylinderFunctorHomDown.{w, v₁, v₂}
      α).mapComposableArrows _).obj
        ((SSet.ι₀.app Δ X).1.prod'
          (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor) =
      (F.mapComposableArrows _).obj X
    have hinput :
        (SSet.ι₀.app Δ X).1.prod'
            (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor =
          X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj (0 : Fin 2)) :=
      congrArg₂ (fun A B => A.prod' B) (SSet.ι₀_app_fst X)
        (asOrderHomHomDown_ι₀_app_snd X)
    rw [hinput]
    refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
    · rfl
    · simp only [ComposableArrows.map', Functor.mapComposableArrows_obj_map,
        Functor.prod'_map, Functor.const_obj_map, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      exact nerveCylinderFunctorHomDown_map_zero α _
  h₁ := by
    change SSet.ι₁ ≫ nerveHomotopyMapHomDown.{w, v₁, v₂} α =
      nerveMapHomDown.{w, v₁, v₂} G
    ext Δ X
    change ((nerveCylinderFunctorHomDown.{w, v₁, v₂}
      α).mapComposableArrows _).obj
        ((SSet.ι₁.app Δ X).1.prod'
          (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor) =
      (G.mapComposableArrows _).obj X
    have hinput :
        (SSet.ι₁.app Δ X).1.prod'
            (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor =
          X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj (1 : Fin 2)) :=
      congrArg₂ (fun A B => A.prod' B) (SSet.ι₁_app_fst X)
        (asOrderHomHomDown_ι₁_app_snd X)
    rw [hinput]
    refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
    · rfl
    · simp only [ComposableArrows.map', Functor.mapComposableArrows_obj_map,
        Functor.prod'_map, Functor.const_obj_map, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      exact nerveCylinderFunctorHomDown_map_one α _
  rel := by
    ext Δ X
    exact X.1.2.elim

end NatTrans

end HomDown

section CommonValue

universe v₄

/-! The object levels are `max w v₁ v₂`, the hom levels are `max v₁ v₄`
and `max v₂ v₄`, and the original nerve value level is `max w v₁ v₂ v₄`.
The shared level `v₄` may lie above the object universe; `v₄ = 0` retains
the original common-ambient API. Maxing HomDown's hom levels also changes
its bundled category/functor object-universe parameters; Type cumulativity
does not supply the original functor at those new levels. These level combinations are part of the
contract, so the compiler's singleton-universe heuristic is disabled only
on the three constructors whose universe parameters all occur in these maxima. -/


variable {C D : Type (max w v₁ v₂)} [Category.{max v₁ v₄} C] [Category.{max v₂ v₄} D]

set_option linter.checkUnivs false in
/-- A functor between categories with a common ambient object universe and
independent hom universes induces a direction-independent map of nerves.
The actual core-to-pair application has hom levels `v → max u v`. -/
def nerveMapCommonValue (F : C ⥤ D) : nerve C ⟶ nerve D where
  app _ := ↾fun X => (F.mapComposableArrows _).obj X

/-- `nerveMapCommonValue` acts on vertices by the object map. -/
theorem nerveMapCommonValue_app_mk₀ (F : C ⥤ D) (x : C) :
    (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
      ComposableArrows.mk₀ (F.obj x) :=
  ComposableArrows.ext₀ rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `nerveMapCommonValue` acts on edges by the morphism map. -/
theorem nerveMapCommonValue_app_mk₁ {F : C ⥤ D} {x y : C} (f : x ⟶ y) :
    (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ (F.map f) :=
  ComposableArrows.ext₁ rfl rfl (by simp [nerveMapCommonValue])

/-- When the hom universes agree, `nerveMapCommonValue` is the ordinary
`nerveMap`. -/
theorem nerveMapCommonValue_eq_nerveMap
    {C D : Type (max w v₁)} [Category.{max v₁ v₄} C] [Category.{max v₁ v₄} D]
    (F : C ⥤ D) :
    nerveMapCommonValue.{w, v₁, v₁, v₄} F = nerveMap F := by
  ext Δ X
  rfl

/-- `nerveMapCommonValue` sends an identity functor to the identity map. -/
@[simp]
theorem nerveMapCommonValue_id
    {C : Type (max w v₁)} [Category.{max v₁ v₄} C] :
    nerveMapCommonValue.{w, v₁, v₁, v₄} (𝟭 C) = 𝟙 (nerve C) := by
  ext Δ X
  rfl

/-- `nerveMapCommonValue` sends a composite of arbitrary-hom-universe functors
to the composite of their nerve maps. Its universe levels are explicit, so
callers use this law directly rather than relying on universe inference by `simp`. -/
theorem nerveMapCommonValue_comp
    {C D E : Type (max w v₁ v₂ v₃)}
    [Category.{max v₁ v₄} C] [Category.{max v₂ v₄} D] [Category.{max v₃ v₄} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMapCommonValue.{max w v₃, v₁, v₂, v₄} F ≫
        nerveMapCommonValue.{max w v₁, v₂, v₃, v₄} G =
      nerveMapCommonValue.{max w v₂, v₁, v₃, v₄} (F ⋙ G) := by
  ext Δ X
  rfl

/-- Ordinary-then-CommonValue composition collapses to the CommonValue map of the
composite functor. -/
theorem nerveMap_nerveMapCommonValue_comp
    {C D E : Type (max w v₁ v₂)}
    [Category.{max v₁ v₄} C] [Category.{max v₁ v₄} D] [Category.{max v₂ v₄} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMap F ≫ nerveMapCommonValue.{w, v₁, v₂, v₄} G =
      nerveMapCommonValue.{w, v₁, v₂, v₄} (F ⋙ G) := by
  ext Δ X
  rfl

/-- CommonValue-then-ordinary composition collapses to the CommonValue map of the
composite functor. -/
theorem nerveMapCommonValue_nerveMap_comp
    {C D E : Type (max w v₁ v₂)}
    [Category.{max v₁ v₄} C] [Category.{max v₂ v₄} D] [Category.{max v₂ v₄} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMapCommonValue.{w, v₁, v₂, v₄} F ≫ nerveMap G =
      nerveMapCommonValue.{w, v₁, v₂, v₄} (F ⋙ G) := by
  ext Δ X
  rfl

namespace NatTrans

variable {F G : C ⥤ D}

set_option linter.checkUnivs false in
/-- The common-ambient, mixed-hom-universe cylinder functor classified by a
natural transformation. -/
def nerveCylinderFunctorCommonValue (α : F ⟶ G) : C × Fin 2 ⥤ D :=
  Prod.swap C (Fin 2) ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α)

/-- The CommonValue cylinder functor agrees with `F` at the `0` endpoint. -/
@[simp]
lemma nerveCylinderFunctorCommonValue_obj_zero (α : F ⟶ G) (X : C) :
    (nerveCylinderFunctorCommonValue.{w, v₁, v₂, v₄} α).obj (X, 0) = F.obj X :=
  rfl

/-- The CommonValue cylinder functor agrees with `G` at the `1` endpoint. -/
@[simp]
lemma nerveCylinderFunctorCommonValue_obj_one (α : F ⟶ G) (X : C) :
    (nerveCylinderFunctorCommonValue.{w, v₁, v₂, v₄} α).obj (X, 1) = G.obj X :=
  rfl

/-- The CommonValue cylinder functor acts as `F` on morphisms at `0`. -/
@[simp]
lemma nerveCylinderFunctorCommonValue_map_zero
    (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    (nerveCylinderFunctorCommonValue.{w, v₁, v₂, v₄} α).map (f ×ₘ 𝟙 (0 : Fin 2)) = F.map f := by
  simp only [nerveCylinderFunctorCommonValue, Functor.comp_map, Prod.swap_map,
    Functor.uncurry_obj_map]
  change 𝟙 (F.obj X) ≫ F.map f = F.map f
  simp

/-- The CommonValue cylinder functor acts as `G` on morphisms at `1`. -/
@[simp]
lemma nerveCylinderFunctorCommonValue_map_one
    (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    (nerveCylinderFunctorCommonValue.{w, v₁, v₂, v₄} α).map (f ×ₘ 𝟙 (1 : Fin 2)) = G.map f := by
  simp only [nerveCylinderFunctorCommonValue, Functor.comp_map, Prod.swap_map,
    Functor.uncurry_obj_map]
  change 𝟙 (G.obj X) ≫ G.map f = G.map f
  simp

set_option linter.checkUnivs false in
/-- The mixed-hom-universe cylinder map on nerves. -/
def nerveHomotopyMapCommonValue (α : F ⟶ G) : nerve C ⊗ Δ[1] ⟶ nerve D where
  app _ := ↾fun X =>
    ((nerveCylinderFunctorCommonValue.{w, v₁, v₂, v₄} α).mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)

/-- The CommonValue cylinder map commutes strictly with precomposition. -/
theorem nerveHomotopyMapCommonValue_precomp
    {X C D : Type (max w v₁ v₂ v₃)}
    [Category.{max v₁ v₄} X] [Category.{max v₂ v₄} C] [Category.{max v₃ v₄} D]
    {F G : C ⥤ D} (K : X ⥤ C) (α : F ⟶ G) :
    (nerveMapCommonValue.{max w v₃, v₁, v₂, v₄} K ▷
        (Δ[1] : SSet.{max w v₁ v₂ v₃ v₄})) ≫
      nerveHomotopyMapCommonValue.{max w v₁, v₂, v₃, v₄} α =
        nerveHomotopyMapCommonValue.{max w v₂, v₁, v₃, v₄}
          (Functor.whiskerLeft K α) := by
  ext Δ X
  change ((nerveCylinderFunctorCommonValue.{max w v₁, v₂, v₃, v₄}
      α).mapComposableArrows _).obj
      (((nerveMapCommonValue.{max w v₃, v₁, v₂, v₄} K).app Δ X.1).prod'
        (SSet.stdSimplex.asOrderHom X.2).toFunctor) =
    ((nerveCylinderFunctorCommonValue.{max w v₂, v₁, v₃, v₄}
      (Functor.whiskerLeft K α)).mapComposableArrows _).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)
  have h_cyl : nerveCylinderFunctorCommonValue.{max w v₂, v₁, v₃, v₄}
        (Functor.whiskerLeft K α) =
      (K.prod (𝟭 (Fin 2))) ⋙
        nerveCylinderFunctorCommonValue.{max w v₁, v₂, v₃, v₄} α := by
    apply Functor.hext
    · rintro ⟨X, i⟩
      fin_cases i <;> rfl
    · rintro ⟨X, i⟩ ⟨Y, j⟩ f
      rcases f with ⟨f, g⟩
      fin_cases i
      · fin_cases j
        · apply heq_of_eq
          simp [nerveCylinderFunctorCommonValue, ComposableArrows.mk₁]
        · apply heq_of_eq
          simp [nerveCylinderFunctorCommonValue, ComposableArrows.mk₁]
      · fin_cases j
        · exfalso
          have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom g
          omega
        · apply heq_of_eq
          simp [nerveCylinderFunctorCommonValue, ComposableArrows.mk₁]
  rw [h_cyl]
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    apply heq_of_eq
    simp only [nerveMapCommonValue]
    rfl

/-- The CommonValue cylinder map commutes strictly with postcomposition. -/
theorem nerveHomotopyMapCommonValue_postcomp
    {C D E : Type (max w v₁ v₂ v₃)}
    [Category.{max v₁ v₄} C] [Category.{max v₂ v₄} D] [Category.{max v₃ v₄} E]
    {F G : C ⥤ D} (α : F ⟶ G) (L : D ⥤ E) :
    nerveHomotopyMapCommonValue.{max w v₃, v₁, v₂, v₄} α ≫
        nerveMapCommonValue.{max w v₁, v₂, v₃, v₄} L =
      nerveHomotopyMapCommonValue.{max w v₂, v₁, v₃, v₄}
        (Functor.whiskerRight α L) := by
  ext Δ X
  change ((L.mapComposableArrows _).obj
      (((nerveCylinderFunctorCommonValue.{max w v₃, v₁, v₂, v₄}
        α).mapComposableArrows _).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor))) =
    ((nerveCylinderFunctorCommonValue.{max w v₂, v₁, v₃, v₄}
      (Functor.whiskerRight α L)).mapComposableArrows _).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)
  have h_cyl : nerveCylinderFunctorCommonValue.{max w v₂, v₁, v₃, v₄}
        (Functor.whiskerRight α L) =
      nerveCylinderFunctorCommonValue.{max w v₃, v₁, v₂, v₄} α ⋙ L := by
    apply Functor.hext
    · rintro ⟨X, i⟩
      fin_cases i <;> rfl
    · rintro ⟨X, i⟩ ⟨Y, j⟩ f
      rcases f with ⟨f, g⟩
      fin_cases i
      · fin_cases j
        · apply heq_of_eq
          simp [nerveCylinderFunctorCommonValue, ComposableArrows.mk₁]
        · apply heq_of_eq
          simp [nerveCylinderFunctorCommonValue, ComposableArrows.mk₁]
      · fin_cases j
        · exfalso
          have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom g
          omega
        · apply heq_of_eq
          simp [nerveCylinderFunctorCommonValue, ComposableArrows.mk₁]
  rw [h_cyl]
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    apply heq_of_eq
    rfl

/-- The second component of the CommonValue `ι₀` endpoint is constant `0`. -/
private lemma asOrderHomCommonValue_ι₀_app_snd
    {C₀ : Type u} [Category.{v₄} C₀]
    {Δ : SimplexCategoryᵒᵖ} (X : (nerve C₀).obj Δ) :
    (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor =
      (Functor.const (Fin (Δ.unop.len + 1))).obj (0 : Fin 2) := by
  rfl

/-- The second component of the CommonValue `ι₁` endpoint is constant `1`. -/
private lemma asOrderHomCommonValue_ι₁_app_snd
    {C₀ : Type u} [Category.{v₄} C₀]
    {Δ : SimplexCategoryᵒᵖ} (X : (nerve C₀).obj Δ) :
    (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor =
      (Functor.const (Fin (Δ.unop.len + 1))).obj (1 : Fin 2) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation induces a simplicial homotopy between the
common-ambient, mixed-hom-universe nerve maps. -/
noncomputable def nerveHomotopyCommonValue (α : F ⟶ G) :
    SSet.Homotopy (nerveMapCommonValue.{w, v₁, v₂, v₄} F)
      (nerveMapCommonValue.{w, v₁, v₂, v₄} G) where
  h := nerveHomotopyMapCommonValue.{w, v₁, v₂, v₄} α
  h₀ := by
    change SSet.ι₀ ≫ nerveHomotopyMapCommonValue.{w, v₁, v₂, v₄} α =
      nerveMapCommonValue.{w, v₁, v₂, v₄} F
    ext Δ X
    change ((nerveCylinderFunctorCommonValue.{w, v₁, v₂, v₄}
      α).mapComposableArrows _).obj
        ((SSet.ι₀.app Δ X).1.prod'
          (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor) =
      (F.mapComposableArrows _).obj X
    have hinput :
        (SSet.ι₀.app Δ X).1.prod'
            (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor =
          X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj (0 : Fin 2)) :=
      congrArg₂ (fun A B => A.prod' B) (SSet.ι₀_app_fst X)
        (asOrderHomCommonValue_ι₀_app_snd X)
    rw [hinput]
    refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
    · rfl
    · simp only [ComposableArrows.map', Functor.mapComposableArrows_obj_map,
        Functor.prod'_map, Functor.const_obj_map, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      exact nerveCylinderFunctorCommonValue_map_zero α _
  h₁ := by
    change SSet.ι₁ ≫ nerveHomotopyMapCommonValue.{w, v₁, v₂, v₄} α =
      nerveMapCommonValue.{w, v₁, v₂, v₄} G
    ext Δ X
    change ((nerveCylinderFunctorCommonValue.{w, v₁, v₂, v₄}
      α).mapComposableArrows _).obj
        ((SSet.ι₁.app Δ X).1.prod'
          (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor) =
      (G.mapComposableArrows _).obj X
    have hinput :
        (SSet.ι₁.app Δ X).1.prod'
            (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor =
          X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj (1 : Fin 2)) :=
      congrArg₂ (fun A B => A.prod' B) (SSet.ι₁_app_fst X)
        (asOrderHomCommonValue_ι₁_app_snd X)
    rw [hinput]
    refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
    · rfl
    · simp only [ComposableArrows.map', Functor.mapComposableArrows_obj_map,
        Functor.prod'_map, Functor.const_obj_map, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      exact nerveCylinderFunctorCommonValue_map_one α _
  rel := by
    ext Δ X
    exact X.1.2.elim

end NatTrans

end CommonValue


section CommonValueCompatibility

variable {C D : Type (max w v₁ v₂)} [Category.{v₁} C] [Category.{v₂} D]

/-- At shared morphism level zero, the common-value map is exactly the
original three-universe HomDown map. -/
theorem nerveMapCommonValue_eq_nerveMapHomDown (F : C ⥤ D) :
    nerveMapCommonValue.{w, v₁, v₂, 0} F = nerveMapHomDown.{w, v₁, v₂} F :=
  rfl

namespace NatTrans

variable {F G : C ⥤ D}

/-- At shared morphism level zero, the common-value cylinder map is exactly
the original three-universe HomDown cylinder map. -/
theorem nerveHomotopyMapCommonValue_eq_nerveHomotopyMapHomDown (α : F ⟶ G) :
    nerveHomotopyMapCommonValue.{w, v₁, v₂, 0} α =
      nerveHomotopyMapHomDown.{w, v₁, v₂} α :=
  rfl

/-- At shared morphism level zero, the common-value homotopy is exactly the
original three-universe HomDown homotopy, including its original endpoints. -/
theorem nerveHomotopyCommonValue_eq_nerveHomotopyHomDown (α : F ⟶ G) :
    nerveHomotopyCommonValue.{w, v₁, v₂, 0} α =
      nerveHomotopyHomDown.{w, v₁, v₂} α :=
  rfl

end NatTrans

end CommonValueCompatibility

end CategoryTheory

namespace SSet

universe oa va ob vb

section ULiftNerveAdapter

variable {A : Type oa} [Category.{va} A] {B : Type ob} [Category.{vb} B]

/-- Change-of-universe nerve map for an arbitrary functor: `ULift`-conjugated
postcomposition with `G`, landing in the pairwise common simplicial-set
universe. Both sides use a single `ULift`; the two target levels agree
definitionally. -/
def nerveMapULift (G : A ⥤ B) :
    (SSet.uliftFunctor.{max ob vb, max oa va}).obj (nerve A) ⟶
    (SSet.uliftFunctor.{max oa va, max ob vb}).obj (nerve B) where
  app Δ := ↾fun X => ULift.up ((G.mapComposableArrows _).obj X.down)

@[simp]
theorem nerveMapULift_app_down (G : A ⥤ B) (Δ : SimplexCategoryᵒᵖ)
    (X : ((SSet.uliftFunctor.{max ob vb, max oa va}).obj (nerve A)).obj Δ) :
    ((nerveMapULift G).app Δ X).down =
      (G.mapComposableArrows _).obj X.down :=
  rfl

/-- The adapter sends an identity functor to the identity map. -/
@[simp]
theorem nerveMapULift_id : nerveMapULift (𝟭 A) = 𝟙 _ := by
  ext Δ X
  rfl

/-- The adapter sends a composite of shared-level functors to the composite
of their adapter maps. (At genuinely mixed levels the two sides live in
different simplicial-set universes, so only the shared-level law is
statable.) -/
theorem nerveMapULift_comp {C D E : Type oa} [Category.{va} C]
    [Category.{va} D] [Category.{va} E] (G : C ⥤ D) (H : D ⥤ E) :
    nerveMapULift (G ⋙ H) = nerveMapULift G ≫ nerveMapULift H := by
  ext Δ X
  rfl

/-- Action on a lifted vertex. -/
theorem nerveMapULift_app_mk₀ (G : A ⥤ B) (x : A) :
    (nerveMapULift G).app (op ⦋0⦌) (ULift.up (ComposableArrows.mk₀ x)) =
      ULift.up (ComposableArrows.mk₀ (G.obj x)) := by
  change ULift.up _ = ULift.up _
  congr 1
  exact ComposableArrows.ext₀ rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Action on a lifted edge. -/
theorem nerveMapULift_app_mk₁ {G : A ⥤ B} {x y : A} (f : x ⟶ y) :
    (nerveMapULift G).app (op ⦋1⦌) (ULift.up (ComposableArrows.mk₁ f)) =
      ULift.up (ComposableArrows.mk₁ (G.map f)) := by
  change ULift.up _ = ULift.up _
  congr 1
  exact ComposableArrows.ext₁ rfl rfl (by simp)

end ULiftNerveAdapter

section ULiftBridge

variable {C D : Type oa} [Category.{va} C] [Category.{va} D]

/-- At shared levels, the adapter is the `ulift` of the ordinary nerve map. -/
theorem nerveMapULift_eq_ulift_map_nerveMap (G : C ⥤ D) :
    nerveMapULift G =
      SSet.uliftFunctor.{max oa va, max oa va}.map (nerveMap G) := by
  ext Δ X
  rfl

end ULiftBridge

section HomDownBridge

variable {C : Type (max w v₁ v₂)} [Category.{v₁} C]
variable {D : Type (max w v₁ v₂)} [Category.{v₂} D]

/-- In the common-ambient setting, the adapter is the `ulift` of
`nerveMapHomDown`. -/
theorem nerveMapULift_eq_ulift_map_nerveMapHomDown (G : C ⥤ D) :
    nerveMapULift G =
      SSet.uliftFunctor.{max w v₁ v₂, max w v₁ v₂}.map
        (CategoryTheory.nerveMapHomDown G) := by
  ext Δ X
  rfl

end HomDownBridge

section CrossBridge

universe uc vc

variable {A : Type (max uc vc)} [Category.{vc} A]
variable {B : Type uc} [Category.{vc} B]

/-- In the down-universe setting, the adapter is the `ulift` of
`nerveMapCross`. -/
theorem nerveMapULift_eq_ulift_map_nerveMapCross (G : A ⥤ B) :
    nerveMapULift G =
      SSet.uliftFunctor.{max uc vc, max uc vc}.map
        (CategoryTheory.nerveMapCross G) := by
  ext Δ X
  rfl

end CrossBridge

end SSet

end
