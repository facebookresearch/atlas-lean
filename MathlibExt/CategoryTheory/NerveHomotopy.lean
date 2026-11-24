/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Functor.Currying
public import MathlibExt.CategoryTheory.NerveCommonHom

/-!
# Natural transformations and homotopies of nerves

A natural transformation between functors determines a simplicial homotopy
between the induced maps on nerves. We construct the cylinder map first, using
the functor on `C × Fin 2` classified by the natural transformation.
The cylinder map is strictly compatible with pre- and postcomposition.

The same construction generalizes from cylinders to prisms: a functor
`C × Fin (n + 1) ⥤ D` determines a prism `nerve C ⊗ Δ[n] ⟶ nerve D`
(`CategoryTheory.Functor.nervePrismMap`), whose faces are the prisms of the
restricted functors. For a chain of two natural transformations, the
classifying functor out of `C × Fin 3`
(`CategoryTheory.NatTrans.nerveChainFunctor`) has as its three faces the
cylinder functors of the two transformations and of their composite.
-/

@[expose] public section

open CategoryTheory Simplicial MonoidalCategory
open scoped CategoryTheory.Prod

universe v u w

namespace CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The nerve sends identity functors to identity maps. -/
@[simp]
lemma nerveMap_id : nerveMap (𝟭 C) = 𝟙 (nerve C) := by
  ext Δ X
  rfl

/-- The nerve sends composites of functors to composites of maps. -/
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

/-- The functor `A × Fin 2 ⥤ B` classified by a natural transformation
`F ⟶ G`. -/
def nerveCylinderFunctor (α : F ⟶ G) : A × Fin 2 ⥤ B :=
  Prod.swap A (Fin 2) ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α)

@[simp]
lemma nerveCylinderFunctor_obj_zero (α : F ⟶ G) (X : A) :
    (nerveCylinderFunctor α).obj (X, 0) = F.obj X :=
  rfl

@[simp]
lemma nerveCylinderFunctor_obj_one (α : F ⟶ G) (X : A) :
    (nerveCylinderFunctor α).obj (X, 1) = G.obj X :=
  rfl

@[simp]
lemma nerveCylinderFunctor_map_zero (α : F ⟶ G) {X Y : A} (f : X ⟶ Y) :
    (nerveCylinderFunctor α).map (f ×ₘ 𝟙 (0 : Fin 2)) = F.map f := by
  simp only [nerveCylinderFunctor, Functor.comp_map, Prod.swap_map,
    Functor.uncurry_obj_map]
  change 𝟙 (F.obj X) ≫ F.map f = F.map f
  simp

@[simp]
lemma nerveCylinderFunctor_map_one (α : F ⟶ G) {X Y : A} (f : X ⟶ Y) :
    (nerveCylinderFunctor α).map (f ×ₘ 𝟙 (1 : Fin 2)) = G.map f := by
  simp only [nerveCylinderFunctor, Functor.comp_map, Prod.swap_map,
    Functor.uncurry_obj_map]
  change 𝟙 (G.obj X) ≫ G.map f = G.map f
  simp

end CylinderClassifier

variable {F G : C ⥤ D}

/-- The cylinder map on nerves induced by a natural transformation. -/
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

/-- If the component of `α : F ⟶ G` at `c` is the equality transport
between `F.obj c` and `G.obj c`, then the nerve cylinder is constant in the
interval direction on the literal constant composable-arrow simplex at `c`.

The interval simplex is arbitrary; in particular, this includes simplices
whose associated order map crosses from `0` to `1`. -/
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

/-- The cylinder map commutes with precomposition. -/
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

/-- The cylinder map commutes with postcomposition. -/
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

lemma asOrderHom_ι₀_app_snd {Δ : SimplexCategoryᵒᵖ} (X : (nerve C).obj Δ) :
    (SSet.stdSimplex.asOrderHom ((SSet.ι₀.app Δ X).2)).toFunctor =
      (Functor.const (Fin (Δ.unop.len + 1))).obj (0 : Fin 2) := by
  rfl

lemma asOrderHom_ι₁_app_snd {Δ : SimplexCategoryᵒᵖ} (X : (nerve C).obj Δ) :
    (SSet.stdSimplex.asOrderHom ((SSet.ι₁.app Δ X).2)).toFunctor =
      (Functor.const (Fin (Δ.unop.len + 1))).obj (1 : Fin 2) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation induces a simplicial homotopy between the
corresponding maps on nerves. -/
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

/-! ## Prisms over nerves -/

/-- The prism `nerve C ⊗ Δ[n] ⟶ nerve D` determined by a functor
`Φ : C × Fin (n + 1) ⥤ D`: at a pair `(s, t)` it is `Φ` applied to the
composable arrows `s` paired with the simplex `t` of `Δ[n]` read as a
functor into `Fin (n + 1)`. For `n = 1` and `Φ` the cylinder functor
of a natural transformation this is
`CategoryTheory.NatTrans.nerveHomotopyMap`, by definition. -/
def Functor.nervePrismMap {n : ℕ} (Φ : C × Fin (n + 1) ⥤ D) :
    nerve C ⊗ Δ[n] ⟶ nerve D where
  app _ := ↾fun X =>
    (Φ.mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)

/-- The value of a nerve prism map at a simplex is `Φ` applied to the
first simplex paired with the order map of the second. -/
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

/-- Faces of nerve prisms: precomposing the prism of `Φ` with
`nerve C ◁ stdSimplex.δ i` is the prism of `Φ` precomposed with the
product of the identity functor and the `i`-th face functor
`Fin (n + 1) ⥤ Fin (n + 2)`. -/
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

/-! ## Chains of natural transformations as `Δ[2]`-prisms -/

/-- The functor `C × Fin 3 ⥤ D` classified by a chain of natural
transformations `α : F ⟶ G` and `β : G ⟶ H`: the composite of
`Prod.swap` with the uncurrying of `ComposableArrows.mk₂ α β`. Its
prism is a `2`-simplex of the functor object `Fun(nerve C, nerve D)`
through `SSet.ihomSimplexOfPrism`. -/
def NatTrans.nerveChainFunctor {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) :
    C × Fin 3 ⥤ D :=
  Prod.swap C (Fin 3) ⋙ Functor.uncurry.obj (ComposableArrows.mk₂ α β)

/-- The nerve prism of the cylinder functor of a natural
transformation is its nerve homotopy map, by definition. -/
lemma NatTrans.nervePrismMap_nerveCylinderFunctor {F G : C ⥤ D}
    (α : F ⟶ G) :
    (NatTrans.nerveCylinderFunctor α).nervePrismMap =
      NatTrans.nerveHomotopyMap α :=
  rfl

/-- The `δ₁` face of the nerve chain functor of `α` and `β` is the
cylinder functor of the composite `α ≫ β`, by
`CategoryTheory.nerve.δ₁_mk₂_eq` in the functor category. -/
lemma NatTrans.prod_δ_one_comp_nerveChainFunctor {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) :
    ((𝟭 C).prod (SimplexCategory.δ (1 : Fin 3)).toOrderHom.toFunctor) ⋙
        NatTrans.nerveChainFunctor α β =
      NatTrans.nerveCylinderFunctor (α ≫ β) :=
  congrArg (fun K => Prod.swap C (Fin 2) ⋙ Functor.uncurry.obj K)
    (CategoryTheory.nerve.δ₁_mk₂_eq α β)

/-- The `δ₂` face of the nerve chain functor of `α` and `β` is the
cylinder functor of `α`, by `CategoryTheory.nerve.δ₂_mk₂_eq` in the
functor category. -/
lemma NatTrans.prod_δ_two_comp_nerveChainFunctor {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) :
    ((𝟭 C).prod (SimplexCategory.δ (2 : Fin 3)).toOrderHom.toFunctor) ⋙
        NatTrans.nerveChainFunctor α β =
      NatTrans.nerveCylinderFunctor α :=
  congrArg (fun K => Prod.swap C (Fin 2) ⋙ Functor.uncurry.obj K)
    (CategoryTheory.nerve.δ₂_mk₂_eq α β)

/-- The `δ₀` face of the nerve chain functor of `α` and `β` is the
cylinder functor of `β`, by `CategoryTheory.nerve.δ₀_mk₂_eq` in the
functor category. -/
lemma NatTrans.prod_δ_zero_comp_nerveChainFunctor {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) :
    ((𝟭 C).prod (SimplexCategory.δ (0 : Fin 3)).toOrderHom.toFunctor) ⋙
        NatTrans.nerveChainFunctor α β =
      NatTrans.nerveCylinderFunctor β :=
  congrArg (fun K => Prod.swap C (Fin 2) ⋙ Functor.uncurry.obj K)
    (CategoryTheory.nerve.δ₀_mk₂_eq α β)

universe uId vId uId' vId'

/-- The cylinder functor of the identity natural transformation is
the first projection followed by the functor. -/
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

/-- The nerve prism of the first projection followed by `F` is the
first projection of simplicial sets followed by `nerveMap F`: the
constant prism at `nerveMap F`. -/
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

/-- The cross-universe cylinder map on nerves. -/
def nerveHomotopyMapCommonHomUp (α : F ⟶ G) : nerve A ⊗ Δ[1] ⟶ nerve B where
  app _ := ↾fun X =>
    ((nerveCylinderFunctor α).mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)

/-- A natural transformation induces a simplicial homotopy between the
cross-universe nerve maps. -/
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

/-- The downward native cylinder map on the original nerves. -/
def nerveHomotopyMapCommonHom (α : F ⟶ G) : nerve A ⊗ Δ[1] ⟶ nerve B where
  app _ := ↾fun X =>
    ((nerveCylinderFunctor α).mapComposableArrows _).obj
      (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor)

/-- A natural transformation induces a simplicial homotopy between the
downward native nerve maps without changing either category. -/
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

/-- An equality-transport component makes the native cylinder constant
on every constant source chain, including every interval crossing. -/
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

/-- Classifying a whiskered transformation uses the original product functor. -/
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

/-- The downward native cylinder is compatible with the original index functor. -/
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

/-- The actual finite-parameter native upward prism keeps its original
source object role, common Hom role and target object role separately. -/
public def Functor.nervePrismMapCommonHomUp {n : ℕ}
    (Φ : A × Fin (n + 1) ⥤ B) :
    nerve A ⊗ (Δ[n] : SSet.{max uPrismObj vPrismObj wPrismHom}) ⟶ nerve B where
  app _ := ↾fun x =>
    (Φ.mapComposableArrows _).obj
      (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor)

/-- Every literal face of the original native upward prism is the
prism of the SAME original functor restricted by that original face. -/
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

/-- The original composable TWO-arrow functor-category chain gives the
actual native upward two-simplex prism, without a lift or replacement map. -/
public def NatTrans.nerveCompositionPrismMapCommonHomUp
    {F G H : A ⥤ B} (α : F ⟶ G) (β : G ⟶ H) :
    nerve A ⊗ (Δ[2] : SSet.{max uPrismObj vPrismObj wPrismHom}) ⟶ nerve B :=
  Functor.nervePrismMapCommonHomUp
    (Prod.swap A (Fin 3) ⋙ Functor.uncurry.obj (ComposableArrows.mk₂ α β))

/-- The COMPLETE first short face is the SAME original α cylinder. -/
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

/-- The COMPLETE second short face is the SAME original β cylinder. -/
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

/-- The COMPLETE long face is the SAME original α≫β cylinder. -/
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

/-- Actual source/target functor equality transports retain the WHOLE
original native cylinder. No transformation or map is supplied as a replacement. -/
public theorem NatTrans.nerveHomotopyMapCommonHomUp_cast
    {F G F' G' : A ⥤ B} (α : F ⟶ G) (hF : F = F') (hG : G = G') :
    NatTrans.nerveHomotopyMapCommonHomUp.{uPrismObj, vPrismObj, wPrismHom}
        (eqToHom hF.symm ≫ α ≫ eqToHom hG) =
      NatTrans.nerveHomotopyMapCommonHomUp.{uPrismObj, vPrismObj, wPrismHom} α := by
  cases hF
  cases hG
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The WHOLE original upward cylinder commutes with the actual original
source functor on EVERY source simplex and parameter simplex. -/
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

/-- The canonical ORIGINAL AsSmall up chart acts on every original
simplex by the SAME object/Hom lifting functor. Both nerve carriers have
the actual max of the independent object and Hom roles. -/
public def nerveMapAsSmallUp (A : Type uPrismObj)
    [Category.{max vPrismObj wPrismHom} A] :
    nerve A ⟶ nerve (AsSmall.{vPrismObj} A) where
  app _ := ↾fun x =>
    ((AsSmall.up : A ⥤ AsSmall.{vPrismObj} A).mapComposableArrows _).obj x

/-- The canonical ORIGINAL AsSmall down-whiskered cylinder, retaining
its actual enlarged object/Hom chart and ORIGINAL lower target B.
The direct native value reader requires no shared-object/Hom collapse. -/
public def NatTrans.nerveHomotopyMapAsSmallDown
    {F G : A ⥤ B} (α : F ⟶ G) :
    nerve (AsSmall.{vPrismObj} A) ⊗
      (Δ[1] : SSet.{max uPrismObj vPrismObj wPrismHom}) ⟶ nerve B where
  app _ := ↾fun x =>
    ((NatTrans.nerveCylinderFunctor
      (Functor.whiskerLeft
        (AsSmall.down : AsSmall.{vPrismObj} A ⥤ A) α)).mapComposableArrows _).obj
      (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor)

/-- EVERY component of the actual down-whiskered chart cylinder is
the SAME original classifier value on the whole paired simplex. -/
public theorem NatTrans.nerveHomotopyMapAsSmallDown_app
    {F G : A ⥤ B} (α : F ⟶ G) (Δ : SimplexCategoryᵒᵖ)
    (x : (nerve (AsSmall.{vPrismObj} A) ⊗
      (Δ[1] : SSet.{max uPrismObj vPrismObj wPrismHom})).obj Δ) :
    (NatTrans.nerveHomotopyMapAsSmallDown.{uPrismObj, vPrismObj, wPrismHom} α).app Δ x =
      ((NatTrans.nerveCylinderFunctor
        (Functor.whiskerLeft (AsSmall.down : AsSmall.{vPrismObj} A ⥤ A) α)).mapComposableArrows
          Δ.unop.len).obj
        (x.1.prod' (SSet.stdSimplex.asOrderHom x.2).toFunctor) := by
  unfold NatTrans.nerveHomotopyMapAsSmallDown
  rfl

/-- The ORIGINAL up/down chart gives the ENTIRE native upward cylinder
with ALL independent object/Hom roles, every simplex/parameter and every
crossing arrow. AsSmall's enlarged Hom chart is retained explicitly. -/
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

/-- In the ACTUAL finite-GL object chart, the canonical up value reader
is the SAME original CommonHomUp map. This does not restrict the generic
independent-role cylinder theorem above. -/
public theorem nerveMapAsSmallUp_eq_nativeCommonHomUp
    (C : Type 0) [Category.{uConcrete} C] :
    nerveMapAsSmallUp.{0, uConcrete, 0} C =
      nerveMapCommonHomUp.{0, uConcrete, 0}
        (AsSmall.up : C ⥤ AsSmall.{uConcrete} C) := by
  ext Δ x
  rfl

/-- On the ACTUAL original finite-object/Ring-Hom source chart, the
canonical down value cylinder is the WHOLE original ordinary AsSmall
cylinder, with both actual categories/F/G/transformation pinned. -/
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
# Whole original natural-transformation cylinder chain value

The proper defining-owner value retains every original chain, product
factor, interval order map and actual cylinder classifier.
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

/-- Every original whole cylinder chain has its SAME classifying-functor, product and interval
  value. -/
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
# The exact original simplicial-homotopy cylinder field

This owned field value connects the existing original simplicial homotopy
with the same already defined nerveHomotopyMap. No homotopy is rebuilt.
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

/-- The SAME original simplicial homotopy has EXACTLY its original whole cylinder map as its h
  field. -/
public theorem nerveHomotopy_h_value
    {F G : C ⥤ D} (alpha : F ⟶ G) :
    (nerveHomotopy alpha).h = nerveHomotopyMap alpha :=
  originalNerveHomotopyHFieldValue alpha

end CategoryTheory.NatTrans

end


/-!
# Every original downward common-Hom simplicial-homotopy chain

This proper owned H.h app value retains the actual original downward
cylinder, every original chain and the exact original interval order map.
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

/-- EVERY original common-Hom H.h cylinder chain keeps its exact classifier, product and interval
  value. -/
public theorem nerveHomotopyCommonHom_h_app_value
    {F G : A ⥤ B} (alpha : F ⟶ G) (Delta : SimplexCategoryᵒᵖ)
    (X : (nerve A ⊗ (Δ[1] : SSet.{max uCommonHObj vCommonHObj wCommonHHom})).obj Delta) :
    (nerveHomotopyCommonHom.{uCommonHObj, vCommonHObj, wCommonHHom} alpha).h.app Delta X =
      ((nerveCylinderFunctor alpha).mapComposableArrows Delta.unop.len).obj
        (X.1.prod' (SSet.stdSimplex.asOrderHom X.2).toFunctor) :=
  originalCommonHomHWholeChainValue alpha Delta X

end CategoryTheory.NatTrans

end


/-! ## Whole value of the original native upward composition prism -/

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

/-- Every original upward composition-prism value retains its entire native chain classifier. -/
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
