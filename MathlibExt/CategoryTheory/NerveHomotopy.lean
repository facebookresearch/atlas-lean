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


public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Functor.Currying
public import MathlibExt.CategoryTheory.NerveCommonHom

/-!
# Natural transformations induce homotopies of nerves

For α : F → G between functors C → D, its cylinder classifier C × Fin 2 → D gives a map N(C) ×
Δ¹ → N(D). On each simplex it applies the classifier to the product of a composable chain and
a monotone interval map. The endpoint restrictions are N(F) and N(G), giving a simplicial
homotopy. Precomposition and postcomposition agree with whiskering α.

More generally, a functor C × Fin (n+1) → D gives a prism N(C) × Δⁿ → N(D). Restricting a
parameter face restricts the prism. Two transformations α : F → G and β : G → H give a
triangular prism whose faces δ₂, δ₀ and δ₁ are the cylinders of α, β and α ≫ β, respectively.
The common-morphism-universe variants retain their separately stated source and target object
heights.
-/

@[expose] public section

open CategoryTheory Simplicial MonoidalCategory
open scoped CategoryTheory.Prod

universe v u w

namespace CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The nerve map of an identity functor.

The map induced by the identity functor of C is the identity of its nerve. -/
@[simp]
lemma nerveMap_id : nerveMap (𝟭 C) = 𝟙 (nerve C) := by
  ext Δ X
  rfl

/-- Composition of maps induced on nerves.

For F : C → D and G : D → E, the nerve map of F ⋙ G equals N(F) followed by N(G). -/
@[simp]
lemma nerveMap_comp {E : Type u} [Category.{v} E] (F : C ⥤ D) (G : D ⥤ E) :
    nerveMap F ≫ nerveMap G = nerveMap (F ⋙ G) := by
  ext Δ X
  rfl

namespace NatTrans

section CylinderClassifier

universe vSource uSource vTarget uTarget

variable {A : Type uSource} {B : Type uTarget}
  [Category.{vSource} A] [Category.{vTarget} B] {F G : A ⥤ B}

/-- The cylinder functor classified by a natural transformation.

For α : F → G between functors A → B, this functor A × Fin 2 → B restricts to F at 0 and G at
1, with the transition from 0 to 1 given by α. The source and target category object and
morphism universes are independent. -/
def nerveCylinderFunctor (α : F ⟶ G) : A × Fin 2 ⥤ B :=
  Prod.swap A (Fin 2) ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α)

/-- Objects on the initial cylinder face.

The cylinder functor classified by α : F → G sends (X,0) to F(X). -/
@[simp]
lemma nerveCylinderFunctor_obj_zero (α : F ⟶ G) (X : A) :
    (nerveCylinderFunctor α).obj (X, 0) = F.obj X :=
  rfl

/-- Objects on the terminal cylinder face.

The cylinder functor classified by α : F → G sends (X,1) to G(X). -/
@[simp]
lemma nerveCylinderFunctor_obj_one (α : F ⟶ G) (X : A) :
    (nerveCylinderFunctor α).obj (X, 1) = G.obj X :=
  rfl

/-- Morphisms on the initial cylinder face.

For f : X → Y in A, the cylinder functor sends (f,id₀) to F(f). -/
@[simp]
lemma nerveCylinderFunctor_map_zero (α : F ⟶ G) {X Y : A} (f : X ⟶ Y) :
    (nerveCylinderFunctor α).map (f ×ₘ 𝟙 (0 : Fin 2)) = F.map f := by
  simp only [nerveCylinderFunctor, Functor.comp_map, Prod.swap_map,
    Functor.uncurry_obj_map]
  change 𝟙 (F.obj X) ≫ F.map f = F.map f
  simp

/-- Morphisms on the terminal cylinder face.

For f : X → Y in A, the cylinder functor sends (f,id₁) to G(f). -/
@[simp]
lemma nerveCylinderFunctor_map_one (α : F ⟶ G) {X Y : A} (f : X ⟶ Y) :
    (nerveCylinderFunctor α).map (f ×ₘ 𝟙 (1 : Fin 2)) = G.map f := by
  simp only [nerveCylinderFunctor, Functor.comp_map, Prod.swap_map,
    Functor.uncurry_obj_map]
  change 𝟙 (G.obj X) ≫ G.map f = G.map f
  simp

end CylinderClassifier

variable {F G : C ⥤ D}

/-- The nerve cylinder map of a natural transformation.

For α : F → G, this map N(C) × Δ¹ → N(D) applies the cylinder functor to the product of a
composable chain in C and the monotone interval map represented by a simplex of Δ¹. -/
def nerveHomotopyMap (α : F ⟶ G) : nerve C ⊗ Δ[1] ⟶ nerve D where
  app _ := ↾fun X =>
    ((nerveCylinderFunctor α).mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)

section NativeConstantClassifier

universe vConst uConst vConstTarget uConstTarget

private theorem nerveCylinderFunctor_obj_const_eq
    {A : Type uConst} [Category.{vConst} A]
    {B : Type uConstTarget} [Category.{vConstTarget} B] {F G : A ⥤ B}
    (α : F ⟶ G) (c : A) (h : F.obj c = G.obj c) (i : Fin 2) :
    (nerveCylinderFunctor α).obj (c, i) = F.obj c := by
  fin_cases i
  · rfl
  · exact h.symm

private theorem nerveCylinderFunctor_map_const_heq
    {A : Type uConst} [Category.{vConst} A]
    {B : Type uConstTarget} [Category.{vConstTarget} B] {F G : A ⥤ B}
    (α : F ⟶ G) (c : A) (h : F.obj c = G.obj c)
    (hα : α.app c = eqToHom h) {i j : Fin 2} (f : i ⟶ j) :
    (nerveCylinderFunctor α).map ((𝟙 c) ×ₘ f) ≍ 𝟙 (F.obj c) := by
  fin_cases i
  · fin_cases j
    · apply heq_of_eq
      simp [nerveCylinderFunctor, ComposableArrows.mk₁]
    · have hcross : α.app c ≍ 𝟙 (F.obj c) :=
        (heq_of_eq hα).trans (eqToHom_heq_id_dom _ _ h)
      simpa [nerveCylinderFunctor, ComposableArrows.mk₁] using hcross
  · fin_cases j
    · exfalso
      have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom f
      omega
    · have hid : (𝟙 (G.obj c)) ≍ (𝟙 (F.obj c)) :=
        (eqToHom_heq_id_cod _ _ h).symm.trans
          (eqToHom_heq_id_dom _ _ h)
      simpa [nerveCylinderFunctor, ComposableArrows.mk₁] using hid

end NativeConstantClassifier

/-- The cylinder on a constant chain with an identity transition.

If F(c) = G(c) and α_c is the morphism transporting along that equality, the cylinder map on
the constant chain at c is the image of that chain under N(F), for every simplex of Δ¹. -/
theorem nerveHomotopyMap_const_apply_of_app_eqToHom
    (α : F ⟶ G) (c : C) (h : F.obj c = G.obj c)
    (hα : α.app c = eqToHom h) {Δ : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj Δ) :
    (nerveHomotopyMap α).app Δ
        ⟨(Functor.const (Fin (Δ.unop.len + 1))).obj c, t⟩ =
      (nerveMap F).app Δ
        ((Functor.const (Fin (Δ.unop.len + 1))).obj c) := by
  let K : Fin (Δ.unop.len + 1) ⥤ C :=
    (Functor.const (Fin (Δ.unop.len + 1))).obj c
  let T : Fin (Δ.unop.len + 1) ⥤ Fin 2 :=
    (SSet.stdSimplex.asOrderHom t).toFunctor
  change ((nerveCylinderFunctor α).mapComposableArrows _).obj (K.prod' T) =
    (F.mapComposableArrows _).obj K
  apply Functor.hext
  · intro i
    exact nerveCylinderFunctor_obj_const_eq α c h (T.obj i)
  · intro i j f
    simpa [K] using nerveCylinderFunctor_map_const_heq α c h hα (T.map f)

/-- Precomposition of nerve cylinder maps.

For K : B → C, precomposing the cylinder map of α by N(K) × id agrees with the cylinder map
classified by the left-whiskered transformation Kα. -/
lemma nerveHomotopyMap_precomp {B : Type u} [Category.{v} B] (K : B ⥤ C) (α : F ⟶ G) :
    (nerveMap K ▷ (Δ[1] : SSet.{max u v})) ≫ nerveHomotopyMap α =
      nerveHomotopyMap (Functor.whiskerLeft K α) := by
  ext Δ X
  change ((nerveCylinderFunctor α).mapComposableArrows _).obj
      (((nerveMap K).app Δ X.1).prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor) =
    ((nerveCylinderFunctor (Functor.whiskerLeft K α)).mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)
  have h_cyl : nerveCylinderFunctor (Functor.whiskerLeft K α) =
      (K.prod (𝟭 (Fin 2))) ⋙ nerveCylinderFunctor α := by
    apply Functor.hext
    · rintro ⟨X, i⟩
      fin_cases i <;> rfl
    · rintro ⟨X, i⟩ ⟨Y, j⟩ f
      rcases f with ⟨f, g⟩
      fin_cases i
      · fin_cases j
        · apply heq_of_eq
          simp [nerveCylinderFunctor, ComposableArrows.mk₁]
        · apply heq_of_eq
          simp [nerveCylinderFunctor, ComposableArrows.mk₁]
      · fin_cases j
        · exfalso
          have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom g
          omega
        · apply heq_of_eq
          simp [nerveCylinderFunctor, ComposableArrows.mk₁]
  rw [h_cyl]
  apply Functor.hext
  · intro i; rfl
  · intro i j f
    apply heq_of_eq
    simp only [nerveMap]
    rfl

/-- Postcomposition of nerve cylinder maps.

For L : D → E, the cylinder map of α followed by N(L) equals the cylinder map of the right-
whiskered transformation αL. -/
lemma nerveHomotopyMap_postcomp {E : Type u} [Category.{v} E] (α : F ⟶ G) (L : D ⥤ E) :
    nerveHomotopyMap α ≫ nerveMap L =
      nerveHomotopyMap (Functor.whiskerRight α L) := by
  ext Δ X
  change ((L.mapComposableArrows _).obj
      (((nerveCylinderFunctor α).mapComposableArrows _).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor))) =
    ((nerveCylinderFunctor (Functor.whiskerRight α L)).mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)
  have h_cyl : nerveCylinderFunctor (Functor.whiskerRight α L) =
      nerveCylinderFunctor α ⋙ L := by
    apply Functor.hext
    · rintro ⟨X, i⟩
      fin_cases i <;> rfl
    · rintro ⟨X, i⟩ ⟨Y, j⟩ f
      rcases f with ⟨f, g⟩
      fin_cases i
      · fin_cases j
        · apply heq_of_eq
          simp [nerveCylinderFunctor, ComposableArrows.mk₁]
        · apply heq_of_eq
          simp [nerveCylinderFunctor, ComposableArrows.mk₁]
      · fin_cases j
        · exfalso
          have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom g
          omega
        · apply heq_of_eq
          simp [nerveCylinderFunctor, ComposableArrows.mk₁]
  rw [h_cyl]
  apply Functor.hext
  · intro i; rfl
  · intro i j f
    apply heq_of_eq
    rfl

/-- The interval coordinate of the initial cylinder inclusion.

On a nerve simplex, the Δ¹-coordinate of the endpoint-0 inclusion represents the constant
monotone map with value 0. -/
lemma asOrderHom_ι₀_app_snd {Δ : SimplexCategoryᵒᵖ} (X : (nerve C).obj Δ) :
    (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor =
      (Functor.const (Fin (Δ.unop.len + 1))).obj (0 : Fin 2) := by
  rfl

/-- The interval coordinate of the terminal cylinder inclusion.

On a nerve simplex, the Δ¹-coordinate of the endpoint-1 inclusion represents the constant
monotone map with value 1. -/
lemma asOrderHom_ι₁_app_snd {Δ : SimplexCategoryᵒᵖ} (X : (nerve C).obj Δ) :
    (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor =
      (Functor.const (Fin (Δ.unop.len + 1))).obj (1 : Fin 2) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The simplicial homotopy induced by a natural transformation.

For α : F → G, the cylinder map N(C) × Δ¹ → N(D) restricts to N(F) at endpoint 0 and N(G) at
endpoint 1, giving a simplicial homotopy between the two nerve maps. -/
noncomputable def nerveHomotopy (α : F ⟶ G) :
    SSet.Homotopy (nerveMap F) (nerveMap G) where
  h := nerveHomotopyMap α
  h₀ := by
    change SSet.ι₀ ≫ nerveHomotopyMap α = nerveMap F
    ext Δ X
    change ((nerveCylinderFunctor α).mapComposableArrows _).obj
        ((SSet.ι₀.app Δ X).1.prod'
          (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor) =
      (F.mapComposableArrows _).obj X
    have hinput :
        (SSet.ι₀.app Δ X).1.prod'
            (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor =
          X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj (0 : Fin 2)) :=
      congrArg₂ (fun A B => A.prod' B) (SSet.ι₀_app_fst X)
        (asOrderHom_ι₀_app_snd X)
    rw [hinput]
    refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
    · rfl
    · simp only [ComposableArrows.map', Functor.mapComposableArrows_obj_map,
        Functor.prod'_map, Functor.const_obj_map, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      exact nerveCylinderFunctor_map_zero α _
  h₁ := by
    change SSet.ι₁ ≫ nerveHomotopyMap α = nerveMap G
    ext Δ X
    change ((nerveCylinderFunctor α).mapComposableArrows _).obj
        ((SSet.ι₁.app Δ X).1.prod'
          (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor) =
      (G.mapComposableArrows _).obj X
    have hinput :
        (SSet.ι₁.app Δ X).1.prod'
            (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor =
          X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj (1 : Fin 2)) :=
      congrArg₂ (fun A B => A.prod' B) (SSet.ι₁_app_fst X)
        (asOrderHom_ι₁_app_snd X)
    rw [hinput]
    refine ComposableArrows.ext (fun i => ?_) (fun i hi => ?_)
    · rfl
    · simp only [ComposableArrows.map', Functor.mapComposableArrows_obj_map,
        Functor.prod'_map, Functor.const_obj_map, eqToHom_refl,
        Category.id_comp, Category.comp_id]
      exact nerveCylinderFunctor_map_one α _
  rel := by
    ext Δ X
    exact X.1.2.elim

end NatTrans

/-!
# Finite-parameter prisms of nerves

A functor Φ : C × Fin (n+1) → D maps each product of a composable chain with a monotone
parameter chain to a chain in D. This defines the prism over Δⁿ, and its δᵢ-face is the prism
of Φ restricted along id_C × δᵢ.
-/

/-- The nerve prism of a finite-parameter functor.

For Φ : C × Fin (n+1) → D, this map N(C) × Δⁿ → N(D) applies Φ to the product of a composable
chain and the monotone finite-ordinal map represented by a simplex of Δⁿ. -/
def Functor.nervePrismMap {n : ℕ} (Φ : C × Fin (n + 1) ⥤ D) :
    nerve C ⊗ Δ[n] ⟶ nerve D where
  app _ := ↾fun X =>
    (Φ.mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)

/-- Product-chain coordinates of a nerve prism.

The prism of Φ sends a pair (c,t) to Φ applied to the product chain c × t, where t is the
order map of the standard-simplex coordinate. -/
@[simp]
lemma Functor.nervePrismMap_app {n : ℕ} (Φ : C × Fin (n + 1) ⥤ D)
    {Δ : SimplexCategoryᵒᵖ}
    (X : (nerve C).obj Δ ⊗ (Δ[n] : SSet.{max u v}).obj Δ) :
    ConcreteCategory.hom
        (X := (nerve C).obj Δ ⊗ (Δ[n] : SSet.{max u v}).obj Δ)
        (Y := (nerve D).obj Δ) (Φ.nervePrismMap.app Δ) X =
      (Φ.mapComposableArrows _).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor) :=
  rfl

/-- The order map of a face of a standard simplex is the face order
map composed with the order map. -/
private lemma asOrderHom_δ_app {n : ℕ} {Δ : SimplexCategoryᵒᵖ}
    (i : Fin (n + 2)) (t : (Δ[n] : SSet.{w}).obj Δ) :
    SSet.stdSimplex.asOrderHom ((SSet.stdSimplex.δ i).app Δ t) =
      (SimplexCategory.δ i).toOrderHom.comp
        (SSet.stdSimplex.asOrderHom t) :=
  OrderHom.ext _ _ (funext fun _ => rfl)

/-- Faces of nerve prisms by parameter restriction.

For Φ : C × Fin (n+2) → D, restricting its prism along the face δᵢ equals the prism of Φ
precomposed by id_C × δᵢ. -/
lemma Functor.whiskerLeft_δ_nervePrismMap {n : ℕ}
    (Φ : C × Fin (n + 2) ⥤ D) (i : Fin (n + 2)) :
    (nerve C ◁ SSet.stdSimplex.δ i) ≫ Φ.nervePrismMap =
      (((𝟭 C).prod (SimplexCategory.δ i).toOrderHom.toFunctor) ⋙
        Φ).nervePrismMap := by
  ext Δ X
  change (Φ.mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom
        ((SSet.stdSimplex.δ i).app Δ X.2)).toFunctor) = _
  rw [asOrderHom_δ_app]
  rfl

/-!
# Two natural transformations and a triangular prism

The chain F → G → H defines a functor C × Fin 3 → D. Omitting level 0 gives the cylinder of β,
omitting level 1 gives the cylinder of α ≫ β, and omitting level 2 gives the cylinder of α.
-/

/-- The functor classified by two composable natural transformations.

For F → G → H with transformations α and β, this functor C × Fin 3 → D has values F,G,H on the
three levels and transition maps α,β and α ≫ β. -/
def NatTrans.nerveChainFunctor {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) :
    C × Fin 3 ⥤ D :=
  Prod.swap C (Fin 3) ⋙ Functor.uncurry.obj (ComposableArrows.mk₂ α β)

/-- The prism of a cylinder classifier.

The one-dimensional nerve prism associated to the cylinder functor of α equals the nerve
cylinder map of α. -/
lemma NatTrans.nervePrismMap_nerveCylinderFunctor {F G : C ⥤ D}
    (α : F ⟶ G) :
    (NatTrans.nerveCylinderFunctor α).nervePrismMap =
      NatTrans.nerveHomotopyMap α :=
  rfl

/-- The composite-transformation face of the chain classifier.

Restricting the three-level chain functor along δ₁ : Fin 2 → Fin 3 omits the middle level and
gives the cylinder functor of α ≫ β. -/
lemma NatTrans.prod_δ_one_comp_nerveChainFunctor {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) :
    ((𝟭 C).prod (SimplexCategory.δ (1 : Fin 3)).toOrderHom.toFunctor) ⋙
        NatTrans.nerveChainFunctor α β =
      NatTrans.nerveCylinderFunctor (α ≫ β) :=
  congrArg (fun K => Prod.swap C (Fin 2) ⋙ Functor.uncurry.obj K)
    (CategoryTheory.nerve.δ₁_mk₂_eq α β)

/-- The first-transformation face of the chain classifier.

Restricting the chain functor along δ₂ omits the last level and gives the cylinder functor of
α. -/
lemma NatTrans.prod_δ_two_comp_nerveChainFunctor {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) :
    ((𝟭 C).prod (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFunctor) ⋙
        NatTrans.nerveChainFunctor α β =
      NatTrans.nerveCylinderFunctor α :=
  congrArg (fun K => Prod.swap C (Fin 2) ⋙ Functor.uncurry.obj K)
    (CategoryTheory.nerve.δ₂_mk₂_eq α β)

/-- The second-transformation face of the chain classifier.

Restricting the chain functor along δ₀ omits the first level and gives the cylinder functor of
β. -/
lemma NatTrans.prod_δ_zero_comp_nerveChainFunctor {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) :
    ((𝟭 C).prod (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFunctor) ⋙
        NatTrans.nerveChainFunctor α β =
      NatTrans.nerveCylinderFunctor β :=
  congrArg (fun K => Prod.swap C (Fin 2) ⋙ Functor.uncurry.obj K)
    (CategoryTheory.nerve.δ₀_mk₂_eq α β)

universe uId vId uId' vId'

/-- The cylinder classifier of an identity transformation.

For the identity transformation of F : A → B, the cylinder functor is the first projection A ×
Fin 2 → A followed by F, at the stated independent category universes. -/
lemma NatTrans.nerveCylinderFunctor_id
    {A : Type uId} [Category.{vId} A] {B : Type uId'} [Category.{vId'} B]
    {F : A ⥤ B} :
    NatTrans.nerveCylinderFunctor (𝟙 F) = Prod.fst A (Fin 2) ⋙ F := by
  apply Functor.hext
  · rintro ⟨X, i⟩
    fin_cases i <;> rfl
  · rintro ⟨X, i⟩ ⟨Y, j⟩ f
    rcases f with ⟨f, g⟩
    fin_cases i
    · fin_cases j
      · apply heq_of_eq
        simp [NatTrans.nerveCylinderFunctor, ComposableArrows.mk₁]
      · apply heq_of_eq
        simp [NatTrans.nerveCylinderFunctor, ComposableArrows.mk₁]
    · fin_cases j
      · exfalso
        have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom g
        omega
      · apply heq_of_eq
        simp [NatTrans.nerveCylinderFunctor, ComposableArrows.mk₁]

/-- The nerve prism of a parameter-independent functor.

For the first projection C × Fin 2 → C followed by F, the prism equals the first projection
N(C) × Δ¹ → N(C) followed by N(F). -/
lemma Functor.nervePrismMap_fst_comp {F : C ⥤ D} :
    (Prod.fst C (Fin 2) ⋙ F).nervePrismMap =
      SemiCartesianMonoidalCategory.fst (nerve C)
          (Δ[1] : SSet.{max u v}) ≫ nerveMap F := by
  ext Δ X
  rfl

end CategoryTheory

end

@[expose] public section

section CommonHomUp

universe uObj vObj wHom

open CategoryTheory Opposite CategoryTheory.MonoidalCategory
open scoped Simplicial MonoidalCategory CategoryTheory.Prod

namespace CategoryTheory.NatTrans

variable {A : Type uObj} [Category.{max vObj wHom} A]
  {B : Type (max uObj vObj)} [Category.{max vObj wHom} B] {F G : A ⥤ B}

/-- The cylinder map with a larger target object universe.

For A in object universe u and B in object universe max(u,v), with morphisms in their common
universe max(v,w), a transformation α : F → G gives N(A) × Δ¹ → N(B) by the same product-chain
cylinder formula. -/
def nerveHomotopyMapCommonHomUp (α : F ⟶ G) : nerve A ⊗ Δ[1] ⟶ nerve B where
  app _ := ↾fun X =>
    ((nerveCylinderFunctor α).mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)

/-- The nerve homotopy with a larger target object universe.

For the stated source and target object heights and common morphism universe, the cylinder
classified by α restricts to the nerve maps of F and G and gives their simplicial homotopy. -/
noncomputable def nerveHomotopyCommonHomUp (α : F ⟶ G) :
    SSet.Homotopy (nerveMapCommonHomUp.{uObj, vObj, wHom} F) (nerveMapCommonHomUp.{uObj, vObj,
      wHom} G) where
  h := nerveHomotopyMapCommonHomUp α
  h₀ := by
    change SSet.ι₀ ≫ nerveHomotopyMapCommonHomUp α = nerveMapCommonHomUp.{uObj, vObj, wHom} F
    ext Δ X
    change ((nerveCylinderFunctor α).mapComposableArrows _).obj
        ((SSet.ι₀.app Δ X).1.prod'
          (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor) =
      (F.mapComposableArrows _).obj X
    have hinput :
        (SSet.ι₀.app Δ X).1.prod'
            (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor =
          X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj (0 : Fin 2)) :=
      congrArg₂ (fun A B => A.prod' B) (SSet.ι₀_app_fst X)
        (asOrderHom_ι₀_app_snd X)
    rw [hinput]
    change (X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj
        (0 : Fin 2))) ⋙ nerveCylinderFunctor α = X ⋙ F
    refine CategoryTheory.Functor.hext (fun i => rfl) ?_
    intro i j f
    change HEq
      ((nerveCylinderFunctor α).map (X.map f ×ₘ 𝟙 (0 : Fin 2)))
      (F.map (X.map f))
    exact heq_of_eq (nerveCylinderFunctor_map_zero α (X.map f))
  h₁ := by
    change SSet.ι₁ ≫ nerveHomotopyMapCommonHomUp α = nerveMapCommonHomUp.{uObj, vObj, wHom} G
    ext Δ X
    change ((nerveCylinderFunctor α).mapComposableArrows _).obj
        ((SSet.ι₁.app Δ X).1.prod'
          (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor) =
      (G.mapComposableArrows _).obj X
    have hinput :
        (SSet.ι₁.app Δ X).1.prod'
            (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor =
          X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj (1 : Fin 2)) :=
      congrArg₂ (fun A B => A.prod' B) (SSet.ι₁_app_fst X)
        (asOrderHom_ι₁_app_snd X)
    rw [hinput]
    change (X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj
        (1 : Fin 2))) ⋙ nerveCylinderFunctor α = X ⋙ G
    refine CategoryTheory.Functor.hext (fun i => rfl) ?_
    intro i j f
    change HEq
      ((nerveCylinderFunctor α).map (X.map f ×ₘ 𝟙 (1 : Fin 2)))
      (G.map (X.map f))
    exact heq_of_eq (nerveCylinderFunctor_map_one α (X.map f))
  rel := by
    ext Δ X
    exact X.1.2.elim

end CategoryTheory.NatTrans

end CommonHomUp

end

@[expose] public section

section CommonHomDown

universe uObj vObj wHom

open CategoryTheory Opposite CategoryTheory.MonoidalCategory
open scoped Simplicial MonoidalCategory CategoryTheory.Prod

namespace CategoryTheory.NatTrans

variable {A : Type (max uObj vObj)} [Category.{max vObj wHom} A]
  {B : Type uObj} [Category.{max vObj wHom} B] {F G : A ⥤ B}

/-- The cylinder map with a larger source object universe.

For A in object universe max(u,v) and B in object universe u, with common morphism universe
max(v,w), the transformation α defines N(A) × Δ¹ → N(B) by applying its cylinder functor to
each product chain. -/
def nerveHomotopyMapCommonHom (α : F ⟶ G) : nerve A ⊗ Δ[1] ⟶ nerve B where
  app _ := ↾fun X =>
    ((nerveCylinderFunctor α).mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)

/-- The nerve homotopy with a larger source object universe.

The common-morphism-universe cylinder map for α gives a simplicial homotopy from the nerve map
of F to that of G, with the source and target object heights stated separately. -/
noncomputable def nerveHomotopyCommonHom (α : F ⟶ G) :
    SSet.Homotopy (nerveMapCommonHom.{uObj, vObj, wHom} F) (nerveMapCommonHom.{uObj, vObj,
      wHom} G) where
  h := nerveHomotopyMapCommonHom α
  h₀ := by
    change SSet.ι₀ ≫ nerveHomotopyMapCommonHom α = nerveMapCommonHom.{uObj, vObj, wHom} F
    ext Δ X
    change ((nerveCylinderFunctor α).mapComposableArrows _).obj
        ((SSet.ι₀.app Δ X).1.prod'
          (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor) =
      (F.mapComposableArrows _).obj X
    have hinput :
        (SSet.ι₀.app Δ X).1.prod'
            (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor =
          X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj (0 : Fin 2)) :=
      congrArg₂ (fun A B => A.prod' B) (SSet.ι₀_app_fst X)
        (asOrderHom_ι₀_app_snd X)
    rw [hinput]
    change (X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj
        (0 : Fin 2))) ⋙ nerveCylinderFunctor α = X ⋙ F
    refine CategoryTheory.Functor.hext (fun i => rfl) ?_
    intro i j f
    change HEq
      ((nerveCylinderFunctor α).map (X.map f ×ₘ 𝟙 (0 : Fin 2)))
      (F.map (X.map f))
    exact heq_of_eq (nerveCylinderFunctor_map_zero α (X.map f))
  h₁ := by
    change SSet.ι₁ ≫ nerveHomotopyMapCommonHom α = nerveMapCommonHom.{uObj, vObj, wHom} G
    ext Δ X
    change ((nerveCylinderFunctor α).mapComposableArrows _).obj
        ((SSet.ι₁.app Δ X).1.prod'
          (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor) =
      (G.mapComposableArrows _).obj X
    have hinput :
        (SSet.ι₁.app Δ X).1.prod'
            (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor =
          X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj (1 : Fin 2)) :=
      congrArg₂ (fun A B => A.prod' B) (SSet.ι₁_app_fst X)
        (asOrderHom_ι₁_app_snd X)
    rw [hinput]
    change (X.prod' ((Functor.const (Fin (Δ.unop.len + 1))).obj
        (1 : Fin 2))) ⋙ nerveCylinderFunctor α = X ⋙ G
    refine CategoryTheory.Functor.hext (fun i => rfl) ?_
    intro i j f
    change HEq
      ((nerveCylinderFunctor α).map (X.map f ×ₘ 𝟙 (1 : Fin 2)))
      (G.map (X.map f))
    exact heq_of_eq (nerveCylinderFunctor_map_one α (X.map f))
  rel := by
    ext Δ X
    exact X.1.2.elim

/-- Constant chains in the larger-source cylinder.

If F(c) = G(c) and α_c is the equality transport, the common-morphism-universe cylinder sends
a constant chain at c, for every interval simplex, to its image under the nerve map of F. -/
theorem nerveHomotopyMapCommonHom_const_apply_of_app_eqToHom
    (α : F ⟶ G) (c : A) (h : F.obj c = G.obj c)
    (hα : α.app c = eqToHom h) {Δ : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max uObj vObj wHom}).obj Δ) :
    (nerveHomotopyMapCommonHom.{uObj, vObj, wHom} α).app Δ
        ⟨(Functor.const (Fin (Δ.unop.len + 1))).obj c, t⟩ =
      (nerveMapCommonHom.{uObj, vObj, wHom} F).app Δ
        ((Functor.const (Fin (Δ.unop.len + 1))).obj c) := by
  let K : Fin (Δ.unop.len + 1) ⥤ A :=
    (Functor.const (Fin (Δ.unop.len + 1))).obj c
  let T : Fin (Δ.unop.len + 1) ⥤ Fin 2 :=
    (SSet.stdSimplex.asOrderHom t).toFunctor
  change ((nerveCylinderFunctor α).mapComposableArrows _).obj (K.prod' T) =
    (F.mapComposableArrows _).obj K
  apply Functor.hext
  · intro i
    exact nerveCylinderFunctor_obj_const_eq α c h (T.obj i)
  · intro i j f
    simpa [K] using nerveCylinderFunctor_map_const_heq α c h hα (T.map f)

end CategoryTheory.NatTrans

end CommonHomDown

end

@[expose] public section

section NativeClassifierPrecomposition

universe uPre vPre uMid vMid uOut vOut

open CategoryTheory Opposite CategoryTheory.MonoidalCategory
open scoped Simplicial MonoidalCategory CategoryTheory.Prod

namespace CategoryTheory.NatTrans

/-- Left whiskering of cylinder classifiers.

For K : X → A, the cylinder functor classified by Kα equals K × id on X × Fin 2 followed by
the cylinder functor classified by α. All category universes in this equality are independent. -/
theorem nerveCylinderFunctor_whiskerLeft
    {X : Type uPre} [Category.{vPre} X]
    {A : Type uMid} [Category.{vMid} A]
    {B : Type uOut} [Category.{vOut} B]
    {F G : A ⥤ B} (K : X ⥤ A) (α : F ⟶ G) :
    nerveCylinderFunctor (Functor.whiskerLeft K α) =
      (K.prod (𝟭 (Fin 2))) ⋙ nerveCylinderFunctor α := by
  apply Functor.hext
  · rintro ⟨x, i⟩
    fin_cases i <;> rfl
  · rintro ⟨x, i⟩ ⟨y, j⟩ f
    rcases f with ⟨f, g⟩
    fin_cases i
    · fin_cases j
      · apply heq_of_eq
        simp [nerveCylinderFunctor, ComposableArrows.mk₁]
      · apply heq_of_eq
        simp [nerveCylinderFunctor, ComposableArrows.mk₁]
    · fin_cases j
      · exfalso
        have hle : (1 : Fin 2) ≤ (0 : Fin 2) := leOfHom g
        omega
      · apply heq_of_eq
        simp [nerveCylinderFunctor, ComposableArrows.mk₁]

end CategoryTheory.NatTrans

end NativeClassifierPrecomposition

section NativeDownwardPrecomposition

universe uObj vObj wHom

open CategoryTheory Opposite CategoryTheory.MonoidalCategory
open scoped Simplicial MonoidalCategory CategoryTheory.Prod

namespace CategoryTheory.NatTrans

/-- Precomposition of the larger-source cylinder.

For K : X → A at the stated object and common morphism heights, precomposing the cylinder of α
by N(K) × id equals the cylinder of the left-whiskered transformation Kα. -/
theorem nerveHomotopyMapCommonHom_precomp
    {X A : Type (max uObj vObj)}
    [Category.{max vObj wHom} X] [Category.{max vObj wHom} A]
    {B : Type uObj} [Category.{max vObj wHom} B]
    {F G : A ⥤ B} (K : X ⥤ A) (α : F ⟶ G) :
    (nerveMap K ▷ (Δ[1] : SSet.{max uObj vObj wHom})) ≫
      nerveHomotopyMapCommonHom α =
        nerveHomotopyMapCommonHom (Functor.whiskerLeft K α) := by
  ext Δ x
  change ((nerveCylinderFunctor α).mapComposableArrows _).obj
      (((nerveMap K).app Δ x.1).prod'
        (SSet.stdSimplex.asOrderHom x.2).toFunctor) =
    ((nerveCylinderFunctor (Functor.whiskerLeft K α)).mapComposableArrows _).obj
      (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor)
  rw [nerveCylinderFunctor_whiskerLeft]
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    apply heq_of_eq
    simp only [nerveMap]
    rfl

end CategoryTheory.NatTrans

end NativeDownwardPrecomposition

end


noncomputable section

open CategoryTheory Opposite CategoryTheory.MonoidalCategory
open scoped Simplicial MonoidalCategory CategoryTheory.Prod

universe uPrismObj vPrismObj wPrismHom

namespace CategoryTheory

variable {A : Type uPrismObj} [Category.{max vPrismObj wPrismHom} A]
  {B : Type (max uPrismObj vPrismObj)} [Category.{max vPrismObj wPrismHom} B]

/-- A finite nerve prism with separate object universe heights.

For A in universe u, B in universe max(u,v) and a common morphism universe max(v,w), a functor
Φ : A × Fin (n+1) → B defines N(A) × Δⁿ → N(B) by its action on product chains. -/
public def Functor.nervePrismMapCommonHomUp {n : ℕ}
    (Φ : A × Fin (n + 1) ⥤ B) :
    nerve A ⊗ (Δ[n] : SSet.{max uPrismObj vPrismObj wPrismHom}) ⟶ nerve B where
  app _ := ↾fun x =>
    (Φ.mapComposableArrows _).obj
      (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor)

/-- Faces of finite prisms at the common morphism height.

For the stated source and target object heights, restricting the prism of Φ along δᵢ equals
the prism of Φ precomposed by id_A × δᵢ. -/
public theorem Functor.whiskerLeft_δ_nervePrismMapCommonHomUp {n : ℕ}
    (Φ : A × Fin (n + 2) ⥤ B) (i : Fin (n + 2)) :
    (nerve A ◁ SSet.stdSimplex.δ i) ≫
        Functor.nervePrismMapCommonHomUp Φ =
      Functor.nervePrismMapCommonHomUp
        (((𝟭 A).prod (SimplexCategory.δ i).toOrderHom.toFunctor) ⋙ Φ) := by
  ext Δ x
  change (Φ.mapComposableArrows _).obj
      (x.1.prod' (SSet.stdSimplex.asOrderHom
        ((SSet.stdSimplex.δ i).app Δ x.2)).toFunctor) = _
  rw [asOrderHom_δ_app]
  rfl

/-- The triangular composition prism at the stated universe heights.

For α : F → G and β : G → H, apply the common-morphism-universe nerve prism construction to
their three-level chain classifier. This gives N(A) × Δ² → N(B). -/
public def NatTrans.nerveCompositionPrismMapCommonHomUp
    {F G H : A ⥤ B} (α : F ⟶ G) (β : G ⟶ H) :
    nerve A ⊗ (Δ[2] : SSet.{max uPrismObj vPrismObj wPrismHom}) ⟶ nerve B :=
  Functor.nervePrismMapCommonHomUp
    (Prod.swap A (Fin 3) ⋙ Functor.uncurry.obj (ComposableArrows.mk₂ α β))

/-- The face of the composition prism determined by the first transformation.

Restricting the triangular composition prism along δ₂ gives the common-morphism-universe
cylinder map of α. -/
public theorem NatTrans.nerveCompositionPrismMapCommonHomUp_face_two
    {F G H : A ⥤ B} (α : F ⟶ G) (β : G ⟶ H) :
    (nerve A ◁ SSet.stdSimplex.δ (2 : Fin 3)) ≫
        NatTrans.nerveCompositionPrismMapCommonHomUp α β =
      NatTrans.nerveHomotopyMapCommonHomUp.{uPrismObj, vPrismObj, wPrismHom} α := by
  rw [NatTrans.nerveCompositionPrismMapCommonHomUp,
    Functor.whiskerLeft_δ_nervePrismMapCommonHomUp]
  have hClass :
      ((𝟭 A).prod (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFunctor) ⋙
          (Prod.swap A (Fin 3) ⋙ Functor.uncurry.obj (ComposableArrows.mk₂ α β)) =
        NatTrans.nerveCylinderFunctor α :=
    congrArg (fun K => Prod.swap A (Fin 2) ⋙ Functor.uncurry.obj K)
      (CategoryTheory.nerve.δ₂_mk₂_eq α β)
  rw [hClass]
  rfl

/-- The face of the composition prism determined by the second transformation.

Restricting the triangular composition prism along δ₀ gives the common-morphism-universe
cylinder map of β. -/
public theorem NatTrans.nerveCompositionPrismMapCommonHomUp_face_zero
    {F G H : A ⥤ B} (α : F ⟶ G) (β : G ⟶ H) :
    (nerve A ◁ SSet.stdSimplex.δ (0 : Fin 3)) ≫
        NatTrans.nerveCompositionPrismMapCommonHomUp α β =
      NatTrans.nerveHomotopyMapCommonHomUp.{uPrismObj, vPrismObj, wPrismHom} β := by
  rw [NatTrans.nerveCompositionPrismMapCommonHomUp,
    Functor.whiskerLeft_δ_nervePrismMapCommonHomUp]
  have hClass :
      ((𝟭 A).prod (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFunctor) ⋙
          (Prod.swap A (Fin 3) ⋙ Functor.uncurry.obj (ComposableArrows.mk₂ α β)) =
        NatTrans.nerveCylinderFunctor β :=
    congrArg (fun K => Prod.swap A (Fin 2) ⋙ Functor.uncurry.obj K)
      (CategoryTheory.nerve.δ₀_mk₂_eq α β)
  rw [hClass]
  rfl

/-- The face of the composition prism determined by the composite transformation.

Restricting the triangular composition prism along δ₁ gives the common-morphism-universe
cylinder map of α ≫ β. -/
public theorem NatTrans.nerveCompositionPrismMapCommonHomUp_face_one
    {F G H : A ⥤ B} (α : F ⟶ G) (β : G ⟶ H) :
    (nerve A ◁ SSet.stdSimplex.δ (1 : Fin 3)) ≫
        NatTrans.nerveCompositionPrismMapCommonHomUp α β =
      NatTrans.nerveHomotopyMapCommonHomUp.{uPrismObj, vPrismObj, wPrismHom} (α ≫ β) := by
  rw [NatTrans.nerveCompositionPrismMapCommonHomUp,
    Functor.whiskerLeft_δ_nervePrismMapCommonHomUp]
  have hClass :
      ((𝟭 A).prod (SimplexCategory.δ (1 : Fin 3)).toOrderHom.toFunctor) ⋙
          (Prod.swap A (Fin 3) ⋙ Functor.uncurry.obj (ComposableArrows.mk₂ α β)) =
        NatTrans.nerveCylinderFunctor (α ≫ β) :=
    congrArg (fun K => Prod.swap A (Fin 2) ⋙ Functor.uncurry.obj K)
      (CategoryTheory.nerve.δ₁_mk₂_eq α β)
  rw [hClass]
  rfl

/-- Cylinder maps under equality transport of endpoint functors.

For equalities F = F′ and G = G′, transporting α by eqToHom on both endpoints leaves its
common-morphism-universe cylinder map unchanged. -/
public theorem NatTrans.nerveHomotopyMapCommonHomUp_cast
    {F G F' G' : A ⥤ B} (α : F ⟶ G) (hF : F = F') (hG : G = G') :
    NatTrans.nerveHomotopyMapCommonHomUp.{uPrismObj, vPrismObj, wPrismHom}
        (eqToHom hF.symm ≫ α ≫ eqToHom hG) =
      NatTrans.nerveHomotopyMapCommonHomUp.{uPrismObj, vPrismObj, wPrismHom} α := by
  cases hF
  cases hG
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Precomposition of the larger-target cylinder.

For K : X → A, the common-morphism-universe cylinder of Kα equals N(K) × id followed by the
cylinder of α, at the stated source and target object heights. -/
public theorem NatTrans.nerveHomotopyMapCommonHomUp_precomp
    {X : Type uPrismObj} [Category.{max vPrismObj wPrismHom} X]
    {F G : A ⥤ B} (K : X ⥤ A) (α : F ⟶ G) :
    (nerveMap K ▷ (Δ[1] : SSet.{max uPrismObj vPrismObj wPrismHom})) ≫
        NatTrans.nerveHomotopyMapCommonHomUp.{uPrismObj, vPrismObj, wPrismHom} α =
      NatTrans.nerveHomotopyMapCommonHomUp.{uPrismObj, vPrismObj, wPrismHom}
        (Functor.whiskerLeft K α) := by
  ext Δ x
  change ((NatTrans.nerveCylinderFunctor α).mapComposableArrows _).obj
      (((nerveMap K).app Δ x.1).prod'
        (SSet.stdSimplex.asOrderHom x.2).toFunctor) =
    ((NatTrans.nerveCylinderFunctor (Functor.whiskerLeft K α)).mapComposableArrows _).obj
      (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor)
  rw [NatTrans.nerveCylinderFunctor_whiskerLeft]
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    apply heq_of_eq
    simp only [nerveMap]
    rfl

/-- The nerve map of canonical category transport.

Apply AsSmall.up : A → AsSmall A to each composable chain. The resulting map of nerves uses
the object and common morphism universe heights stated in the definition. -/
public def nerveMapAsSmallUp (A : Type uPrismObj)
    [Category.{max vPrismObj wPrismHom} A] :
    nerve A ⟶ nerve (AsSmall.{vPrismObj} A) where
  app _ := ↾fun x =>
    ((AsSmall.up : A ⥤ AsSmall.{vPrismObj} A).mapComposableArrows _).obj x

/-- The cylinder map after canonical category transport.

Precompose α by AsSmall.down : AsSmall A → A and apply its cylinder classifier to chains in
AsSmall A. This gives N(AsSmall A) × Δ¹ → N(B) at the specified object and morphism universe
levels. -/
public def NatTrans.nerveHomotopyMapAsSmallDown
    {F G : A ⥤ B} (α : F ⟶ G) :
    nerve (AsSmall.{vPrismObj} A) ⊗
      (Δ[1] : SSet.{max uPrismObj vPrismObj wPrismHom}) ⟶ nerve B where
  app _ := ↾fun x =>
    ((NatTrans.nerveCylinderFunctor
      (Functor.whiskerLeft
        (AsSmall.down : AsSmall.{vPrismObj} A ⥤ A) α)).mapComposableArrows _).obj
      (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor)

/-- Coordinates of the cylinder after canonical category transport.

On a chain c in AsSmall A and a monotone interval map t, the transported cylinder gives the
composable chain obtained by applying the cylinder classifier of AsSmall.down α to the product
chain (c,t). -/
public theorem NatTrans.nerveHomotopyMapAsSmallDown_app
    {F G : A ⥤ B} (α : F ⟶ G) (Δ : SimplexCategoryᵒᵖ)
    (x : (nerve (AsSmall.{vPrismObj} A) ⊗
      (Δ[1] : SSet.{max uPrismObj vPrismObj wPrismHom})).obj Δ) :
    (NatTrans.nerveHomotopyMapAsSmallDown.{uPrismObj, vPrismObj, wPrismHom} α).app Δ x =
      ((NatTrans.nerveCylinderFunctor
        (Functor.whiskerLeft (AsSmall.down : AsSmall.{vPrismObj} A ⥤ A) α)).mapComposableArrows Δ.unop.len).obj
        (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor) := by
  unfold NatTrans.nerveHomotopyMapAsSmallDown
  rfl

/-- Factorization of the cylinder through canonical category transport.

The larger-target cylinder map of α equals the nerve map of AsSmall.up on the first factor
followed by the cylinder classified by AsSmall.down α. -/
public theorem NatTrans.nerveHomotopyMapCommonHomUp_eq_asSmall
    {F G : A ⥤ B} (α : F ⟶ G) :
    NatTrans.nerveHomotopyMapCommonHomUp.{uPrismObj, vPrismObj, wPrismHom} α =
      (nerveMapAsSmallUp.{uPrismObj, vPrismObj, wPrismHom} A ▷
        (Δ[1] : SSet.{max uPrismObj vPrismObj wPrismHom})) ≫
          NatTrans.nerveHomotopyMapAsSmallDown.{uPrismObj, vPrismObj, wPrismHom} α := by
  ext Δ x
  change ((NatTrans.nerveCylinderFunctor α).mapComposableArrows _).obj
      (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor) =
    ((NatTrans.nerveCylinderFunctor
      (Functor.whiskerLeft (AsSmall.down : AsSmall.{vPrismObj} A ⥤ A) α)).mapComposableArrows _).obj
      (((nerveMapAsSmallUp.{uPrismObj, vPrismObj, wPrismHom} A).app Δ x.1).prod'
        (SSet.stdSimplex.asOrderHom x.2).toFunctor)
  rw [NatTrans.nerveCylinderFunctor_whiskerLeft]
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    apply heq_of_eq
    rfl

section OriginalFiniteObjectChart

universe uConcrete

/-- Canonical nerve transport for a universe-zero object category.

For C with objects in Type 0 and morphisms in universe u, applying AsSmall.up to chains equals
the common-morphism-universe nerve map of that functor. -/
public theorem nerveMapAsSmallUp_eq_nativeCommonHomUp
    (C : Type 0) [Category.{uConcrete} C] :
    nerveMapAsSmallUp.{0, uConcrete, 0} C =
      nerveMapCommonHomUp.{0, uConcrete, 0}
        (AsSmall.up : C ⥤ AsSmall.{uConcrete} C) := by
  ext Δ x
  rfl

/-- The transported cylinder for a universe-zero object category.

For C with objects in Type 0 and morphisms in universe u, and D with objects and morphisms in
universe u, the AsSmall.down cylinder equals the ordinary nerve cylinder of the left-whiskered
transformation. -/
public theorem NatTrans.nerveHomotopyMapAsSmallDown_eq_ordinary
    {C : Type 0} [Category.{uConcrete} C]
    {D : Type uConcrete} [Category.{uConcrete} D]
    {F G : C ⥤ D} (α : F ⟶ G) :
    let down : AsSmall.{uConcrete} C ⥤ C := AsSmall.down
    let Fdown : AsSmall.{uConcrete} C ⥤ D := down ⋙ F
    let Gdown : AsSmall.{uConcrete} C ⥤ D := down ⋙ G
    let αdown : Fdown ⟶ Gdown := Functor.whiskerLeft down α
    NatTrans.nerveHomotopyMapAsSmallDown.{0, uConcrete, 0} α =
      NatTrans.nerveHomotopyMap (C := AsSmall.{uConcrete} C) (D := D)
        (F := Fdown) (G := Gdown) αdown := by
  let down : AsSmall.{uConcrete} C ⥤ C := AsSmall.down
  let Fdown : AsSmall.{uConcrete} C ⥤ D := down ⋙ F
  let Gdown : AsSmall.{uConcrete} C ⥤ D := down ⋙ G
  let αdown : Fdown ⟶ Gdown := Functor.whiskerLeft down α
  change NatTrans.nerveHomotopyMapAsSmallDown.{0, uConcrete, 0} α =
    NatTrans.nerveHomotopyMap (C := AsSmall.{uConcrete} C) (D := D)
      (F := Fdown) (G := Gdown) αdown
  ext Δ x
  have hNative := NatTrans.nerveHomotopyMapAsSmallDown_app.{0, uConcrete, 0} α Δ x
  have hOrdinary :
      (NatTrans.nerveHomotopyMap (C := AsSmall.{uConcrete} C) (D := D)
        (F := Fdown) (G := Gdown) αdown).app Δ x =
        ((NatTrans.nerveCylinderFunctor αdown).mapComposableArrows Δ.unop.len).obj
          (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor) := by
    unfold NatTrans.nerveHomotopyMap
    rfl
  exact hNative.trans hOrdinary.symm

end OriginalFiniteObjectChart

end CategoryTheory

end


/-!
# Coordinates of the natural-transformation cylinder

For a nerve chain c of length m and a standard one-simplex t, the cylinder associated to α is
the chain obtained by applying its classifier C × Fin 2 → D to c × t.
-/

noncomputable section

open CategoryTheory Simplicial MonoidalCategory
open scoped CategoryTheory.Prod Simplicial MonoidalCategory

universe uCylinderValue vCylinderValue

namespace CategoryTheory.NatTrans

variable {C D : Type uCylinderValue} [Category.{vCylinderValue} C]
  [Category.{vCylinderValue} D]

private theorem originalNerveHomotopyCylinderChainValue
    {F G : C ⥤ D} (alpha : F ⟶ G) (Delta : SimplexCategoryᵒᵖ)
    (X : (nerve C ⊗ (Δ[1] : SSet.{max uCylinderValue vCylinderValue})).obj Delta) :
    (nerveHomotopyMap alpha).app Delta X =
      ((nerveCylinderFunctor alpha).mapComposableArrows Delta.unop.len).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor) := rfl

/-- Product-chain coordinates of the nerve cylinder.

In degree m, the cylinder sends a chain c and an interval simplex t to the image of the
product chain c × t under the cylinder functor classified by α. -/
public theorem nerveHomotopyMap_app_value
    {F G : C ⥤ D} (alpha : F ⟶ G) (Delta : SimplexCategoryᵒᵖ)
    (X : (nerve C ⊗ (Δ[1] : SSet.{max uCylinderValue vCylinderValue})).obj Delta) :
    (nerveHomotopyMap alpha).app Delta X =
      ((nerveCylinderFunctor alpha).mapComposableArrows Delta.unop.len).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor) :=
  originalNerveHomotopyCylinderChainValue alpha Delta X

end CategoryTheory.NatTrans

end


/-!
# The cylinder map underlying the nerve homotopy

The simplicial homotopy induced by α has underlying map nerveHomotopyMap α, with endpoint maps
N(F) and N(G).
-/

noncomputable section

open CategoryTheory Simplicial MonoidalCategory
open scoped CategoryTheory.Prod Simplicial MonoidalCategory

universe uHField vHField

namespace CategoryTheory.NatTrans

variable {C D : Type uHField} [Category.{vHField} C] [Category.{vHField} D]

private theorem originalNerveHomotopyHFieldValue
    {F G : C ⥤ D} (alpha : F ⟶ G) :
    (nerveHomotopy alpha).h = nerveHomotopyMap alpha := rfl

/-- The underlying map of the nerve homotopy.

The cylinder field h of the simplicial homotopy associated to α is nerveHomotopyMap α. -/
public theorem nerveHomotopy_h_value
    {F G : C ⥤ D} (alpha : F ⟶ G) :
    (nerveHomotopy alpha).h = nerveHomotopyMap alpha :=
  originalNerveHomotopyHFieldValue alpha

end CategoryTheory.NatTrans

end


/-!
# Coordinates at a common morphism universe

For the larger-source object-height variant, the homotopy cylinder in degree m is the image of
the product chain (c,t) under the classifier of α. The common morphism height and both object
heights remain as specified.
-/

noncomputable section

open CategoryTheory Simplicial MonoidalCategory
open scoped CategoryTheory.Prod Simplicial MonoidalCategory

universe uCommonHObj vCommonHObj wCommonHHom

namespace CategoryTheory.NatTrans

variable {A : Type (max uCommonHObj vCommonHObj)}
  [Category.{max vCommonHObj wCommonHHom} A]
  {B : Type uCommonHObj} [Category.{max vCommonHObj wCommonHHom} B]

private theorem originalCommonHomHWholeChainValue
    {F G : A ⥤ B} (alpha : F ⟶ G) (Delta : SimplexCategoryᵒᵖ)
    (X : (nerve A ⊗ (Δ[1] : SSet.{max uCommonHObj vCommonHObj wCommonHHom})).obj Delta) :
    (nerveHomotopyCommonHom.{uCommonHObj, vCommonHObj, wCommonHHom} alpha).h.app Delta X =
      ((nerveCylinderFunctor alpha).mapComposableArrows Delta.unop.len).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor) := rfl

/-- Product-chain coordinates of the larger-source homotopy.

In degree m, the cylinder field of the common-morphism-universe homotopy sends (c,t) to the
image of the product chain under the cylinder classifier of α, with the stated source and
target object heights. -/
public theorem nerveHomotopyCommonHom_h_app_value
    {F G : A ⥤ B} (alpha : F ⟶ G) (Delta : SimplexCategoryᵒᵖ)
    (X : (nerve A ⊗ (Δ[1] : SSet.{max uCommonHObj vCommonHObj wCommonHHom})).obj Delta) :
    (nerveHomotopyCommonHom.{uCommonHObj, vCommonHObj, wCommonHHom} alpha).h.app Delta X =
      ((nerveCylinderFunctor alpha).mapComposableArrows Delta.unop.len).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor) :=
  originalCommonHomHWholeChainValue alpha Delta X

end CategoryTheory.NatTrans

end


/-!
# Coordinates of a composition prism

The triangular prism of α : F → G and β : G → H applies their three-level classifier to each
product chain. This coordinate formula holds at the stated source object height, larger target
object height and common morphism height.
-/

noncomputable section

open CategoryTheory Opposite Simplicial MonoidalCategory
open scoped Simplicial

universe uCompositionValue vCompositionValue wCompositionValue

namespace CategoryTheory.NatTrans

variable {A : Type uCompositionValue} [Category.{max vCompositionValue wCompositionValue} A]
  {B : Type (max uCompositionValue vCompositionValue)}
  [Category.{max vCompositionValue wCompositionValue} B]

private theorem originalUpwardCompositionPrismValueComputed
    {F G H : A ⥤ B} (alpha : F ⟶ G) (beta : G ⟶ H) (Delta : SimplexCategoryᵒᵖ)
    (x : (nerve A ⊗
      (Δ[2] : SSet.{max uCompositionValue vCompositionValue wCompositionValue})).obj Delta) :
    (nerveCompositionPrismMapCommonHomUp.{uCompositionValue, vCompositionValue, wCompositionValue}
        alpha beta).app Delta x =
      ((Prod.swap A (Fin 3) ⋙
        Functor.uncurry.obj (ComposableArrows.mk₂ alpha beta)).mapComposableArrows
          Delta.unop.len).obj (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor) := rfl

/-- Product-chain coordinates of the composition prism.

In degree m, the triangular composition prism sends a chain c and a monotone map t to the
image of their product chain under the three-level classifier of α and β. -/
public theorem nerveCompositionPrismMapCommonHomUp_app_value
    {F G H : A ⥤ B} (alpha : F ⟶ G) (beta : G ⟶ H) (Delta : SimplexCategoryᵒᵖ)
    (x : (nerve A ⊗
      (Δ[2] : SSet.{max uCompositionValue vCompositionValue wCompositionValue})).obj Delta) :
    (nerveCompositionPrismMapCommonHomUp.{uCompositionValue, vCompositionValue, wCompositionValue}
        alpha beta).app Delta x =
      ((Prod.swap A (Fin 3) ⋙
        Functor.uncurry.obj (ComposableArrows.mk₂ alpha beta)).mapComposableArrows
          Delta.unop.len).obj (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor) :=
  originalUpwardCompositionPrismValueComputed alpha beta Delta x

end CategoryTheory.NatTrans

end
