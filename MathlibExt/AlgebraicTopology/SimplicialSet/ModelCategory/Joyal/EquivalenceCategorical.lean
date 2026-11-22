/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import Mathlib.CategoryTheory.Monoidal.Closed.Functor
public import MathlibExt.AlgebraicTopology.SimplicialSet.HoComp
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoFunctorCategorical
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalence

/-!
# Homotopy equivalences are categorical equivalences; the comparison functor
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite

open scoped Simplicial

universe u

namespace SSet

variable {X Y C W : SSet.{u}}

/-- **A map with a homotopy inverse up to isomorphism in the homotopy
categories of functor objects is a categorical equivalence.** If
`g : Y ⟶ X` is such that the vertices classified by `f ≫ g` and `𝟙 X` are
isomorphic in `SSet.hoFunctor.obj ((ihom X).obj X)` and the vertices
classified by `g ≫ f` and `𝟙 Y` are isomorphic in
`SSet.hoFunctor.obj ((ihom Y).obj Y)`, then `f` is a Joyal categorical
equivalence: for every quasicategory `C`, whiskering the given
isomorphisms through `SSet.hoComp` exhibits precomposition with `g` as a
quasi-inverse of precomposition with `f` on `h Fun(-, C)`. This is the
homotopy-equivalence condition of Stevenson, Definition 2.1, read in
ordinary homotopy categories; see the module header. -/
theorem categoricalEquivalences.of_hoCompIso {f : X ⟶ Y} (g : Y ⟶ X)
    (α : (HomotopyCategory.mk (ihomVertexEquiv X X (f ≫ g)) :
        hoFunctor.obj ((ihom X).obj X)) ≅
      HomotopyCategory.mk (ihomVertexEquiv X X (𝟙 X)))
    (β : (HomotopyCategory.mk (ihomVertexEquiv Y Y (g ≫ f)) :
        hoFunctor.obj ((ihom Y).obj Y)) ≅
      HomotopyCategory.mk (ihomVertexEquiv Y Y (𝟙 Y))) :
    categoricalEquivalences f := by
  intro C _
  let F : ((ihom Y).obj C).HomotopyCategory ⥤ ((ihom X).obj C).HomotopyCategory :=
    (hoFunctor.map ((pre f).app C)).toFunctor
  let G : ((ihom X).obj C).HomotopyCategory ⥤ ((ihom Y).obj C).HomotopyCategory :=
    (hoFunctor.map ((pre g).app C)).toFunctor
  have hα1 : hoCompSlice (C := C)
        (HomotopyCategory.mk (ihomVertexEquiv X X (f ≫ g))) = G ⋙ F := by
    rw [hoCompSlice_mk_ihomVertexEquiv_eq_hoPre]
    exact hoFunctor_pre_comp C f g
  have hα2 : hoCompSlice (C := C)
        (HomotopyCategory.mk (ihomVertexEquiv X X (𝟙 X))) =
      𝟭 ((ihom X).obj C).HomotopyCategory := by
    rw [hoCompSlice_mk_ihomVertexEquiv_eq_hoPre]
    exact hoFunctor_pre_id C
  have hβ1 : hoCompSlice (C := C)
        (HomotopyCategory.mk (ihomVertexEquiv Y Y (g ≫ f))) = F ⋙ G := by
    rw [hoCompSlice_mk_ihomVertexEquiv_eq_hoPre]
    exact hoFunctor_pre_comp C g f
  have hβ2 : hoCompSlice (C := C)
        (HomotopyCategory.mk (ihomVertexEquiv Y Y (𝟙 Y))) =
      𝟭 ((ihom Y).obj C).HomotopyCategory := by
    rw [hoCompSlice_mk_ihomVertexEquiv_eq_hoPre]
    exact hoFunctor_pre_id C
  have isoGF : G ⋙ F ≅ 𝟭 ((ihom X).obj C).HomotopyCategory :=
    (eqToIso hα1).symm ≪≫ hoCompSliceIso α ≪≫ (eqToIso hα2)
  have isoFG : F ⋙ G ≅ 𝟭 ((ihom Y).obj C).HomotopyCategory :=
    (eqToIso hβ1).symm ≪≫ hoCompSliceIso β ≪≫ (eqToIso hβ2)
  exact Functor.IsEquivalence.mk' G isoFG.symm isoGF

/-- The equivalence-edge form of
`SSet.categoricalEquivalences.of_hoCompIso`: the isomorphisms in the
homotopy categories of functor objects are represented by equivalence
edges, through `SSet.Edge.toHoHom`. -/
theorem categoricalEquivalences.of_isEquivalence_edges {f : X ⟶ Y} (g : Y ⟶ X)
    {eX : Edge (ihomVertexEquiv X X (f ≫ g)) (ihomVertexEquiv X X (𝟙 X))}
    (heX : eX.IsEquivalence)
    {eY : Edge (ihomVertexEquiv Y Y (g ≫ f)) (ihomVertexEquiv Y Y (𝟙 Y))}
    (heY : eY.IsEquivalence) :
    categoricalEquivalences f :=
  categoricalEquivalences.of_hoCompIso g (@asIso _ _ _ _ eX.toHoHom heX)
    (@asIso _ _ _ _ eY.toHoHom heY)

/-- The inverse-data form of
`SSet.categoricalEquivalences.of_isEquivalence_edges`: the equivalence
edges are given by edges equipped with `SSet.Edge.InvStruct` inverse
data. -/
theorem categoricalEquivalences.of_invStruct_edges {f : X ⟶ Y} (g : Y ⟶ X)
    {eX : Edge (ihomVertexEquiv X X (f ≫ g)) (ihomVertexEquiv X X (𝟙 X))}
    (hX : eX.InvStruct)
    {eY : Edge (ihomVertexEquiv Y Y (g ≫ f)) (ihomVertexEquiv Y Y (𝟙 Y))}
    (hY : eY.InvStruct) :
    categoricalEquivalences f :=
  categoricalEquivalences.of_isEquivalence_edges g hX.isEquivalence hY.isEquivalence

variable {Z : SSet.{u}} {D : Type u} [Category.{u} D]

/-!
## Descent, the counit, and the comparison functor
-/

/-- The product comparison of `SSet.hoFunctor` is the binary-product
functor of `2`-truncated homotopy categories. -/
private lemma prodComparison_hoFunctor_toFunctor (A B : SSet.{u}) :
    (CartesianMonoidalCategory.prodComparison hoFunctor A B).toFunctor =
      Truncated.HomotopyCategory.BinaryProduct.functor
        ((truncation 2).obj A) ((truncation 2).obj B) := rfl

/-- The inverse product comparison of `SSet.hoFunctor` is the
binary-product inverse of `2`-truncated homotopy categories. -/
private lemma inv_prodComparison_hoFunctor_toFunctor (A B : SSet.{u}) :
    (inv (CartesianMonoidalCategory.prodComparison hoFunctor A B)).toFunctor =
      Truncated.HomotopyCategory.BinaryProduct.inverse
        ((truncation 2).obj A) ((truncation 2).obj B) := by
  have h : inv (CartesianMonoidalCategory.prodComparison hoFunctor A B) =
      Cat.Hom.ofFunctor (Truncated.HomotopyCategory.BinaryProduct.inverse
        ((truncation 2).obj A) ((truncation 2).obj B)) := by
    apply IsIso.inv_eq_of_hom_inv_id
    ext1
    change (CartesianMonoidalCategory.prodComparison hoFunctor A B).toFunctor ⋙
        Truncated.HomotopyCategory.BinaryProduct.inverse
          ((truncation 2).obj A) ((truncation 2).obj B) = 𝟭 _
    rw [prodComparison_hoFunctor_toFunctor]
    exact Truncated.HomotopyCategory.BinaryProduct.functor_comp_inverse _ _
  rw [h]

/-- **The comparison functor** `h Fun(Z, nerve D) ⥤ (Z.HomotopyCategory ⥤ D)`
of the additional comparison obligation(b): the exponential comparison morphism of
`SSet.hoFunctor` at `Z` and `nerve D`, followed by postcomposition with
the counit of `CategoryTheory.nerveAdjunction`. Its object formula is
`SSet.hoFunNerveComparison_obj_mk_ihomVertexEquiv`; its morphism formula
and naturality are the additional comparison obligation and
the additional comparison obligation in the module header. -/
noncomputable def hoFunNerveComparison (Z : SSet.{u}) (D : Type u) [Category.{u} D] :
    ((ihom Z).obj (CategoryTheory.nerve D)).HomotopyCategory ⥤
      (Z.HomotopyCategory ⥤ D) :=
  ((CategoryTheory.expComparison hoFunctor Z).app
      (CategoryTheory.nerve D) ≫
    (ihom (hoFunctor.obj Z)).map
      (CategoryTheory.nerveAdjunction.counit.app (Cat.of D))).toFunctor

/-- Uncurrying the comparison morphism in `Cat` gives the inverse product
comparison followed by evaluation and the counit, by
`CategoryTheory.uncurry_expComparison`. -/
private lemma uncurry_hoFunNerveComparison :
    MonoidalClosed.uncurry
        ((CategoryTheory.expComparison hoFunctor Z).app
            (CategoryTheory.nerve D) ≫
          (ihom (hoFunctor.obj Z)).map
            (CategoryTheory.nerveAdjunction.counit.app (Cat.of D))) =
      inv (CartesianMonoidalCategory.prodComparison hoFunctor Z
          ((ihom Z).obj (CategoryTheory.nerve D))) ≫
        hoFunctor.map ((ihom.ev Z).app (CategoryTheory.nerve D)) ≫
          CategoryTheory.nerveAdjunction.counit.app (Cat.of D) :=
  calc MonoidalClosed.uncurry
        ((CategoryTheory.expComparison hoFunctor Z).app
            (CategoryTheory.nerve D) ≫
          (ihom (hoFunctor.obj Z)).map
            (CategoryTheory.nerveAdjunction.counit.app (Cat.of D)))
      = (hoFunctor.obj Z ◁
            (CategoryTheory.expComparison hoFunctor Z).app
              (CategoryTheory.nerve D)) ≫
          MonoidalClosed.uncurry
            ((ihom (hoFunctor.obj Z)).map
              (CategoryTheory.nerveAdjunction.counit.app (Cat.of D))) :=
        MonoidalClosed.uncurry_natural_left _ _
    _ = (hoFunctor.obj Z ◁
            (CategoryTheory.expComparison hoFunctor Z).app
              (CategoryTheory.nerve D)) ≫
          ((ihom.ev (hoFunctor.obj Z)).app _ ≫
            CategoryTheory.nerveAdjunction.counit.app (Cat.of D)) :=
        congrArg _ (MonoidalClosed.uncurry_ihom_map _ _)
    _ = ((hoFunctor.obj Z ◁
            (CategoryTheory.expComparison hoFunctor Z).app
              (CategoryTheory.nerve D)) ≫ (ihom.ev (hoFunctor.obj Z)).app _) ≫
          CategoryTheory.nerveAdjunction.counit.app (Cat.of D) :=
        (Category.assoc _ _ _).symm
    _ = MonoidalClosed.uncurry
            ((CategoryTheory.expComparison hoFunctor Z).app
              (CategoryTheory.nerve D)) ≫
          CategoryTheory.nerveAdjunction.counit.app (Cat.of D) :=
        congrArg (· ≫ _) (MonoidalClosed.uncurry_eq _).symm
    _ = (inv (CartesianMonoidalCategory.prodComparison hoFunctor Z
            ((ihom Z).obj (CategoryTheory.nerve D))) ≫
          hoFunctor.map ((ihom.ev Z).app (CategoryTheory.nerve D))) ≫
          CategoryTheory.nerveAdjunction.counit.app (Cat.of D) :=
        congrArg (· ≫ _) (CategoryTheory.uncurry_expComparison _ _ _)
    _ = inv (CartesianMonoidalCategory.prodComparison hoFunctor Z
            ((ihom Z).obj (CategoryTheory.nerve D))) ≫
          hoFunctor.map ((ihom.ev Z).app (CategoryTheory.nerve D)) ≫
            CategoryTheory.nerveAdjunction.counit.app (Cat.of D) :=
        Category.assoc _ _ _

/-- The functor underlying the uncurried comparison morphism is the
binary-product inverse followed by evaluation on homotopy categories and
the descent of the identity of the nerve. -/
private lemma uncurry_hoFunNerveComparison_toFunctor :
    (MonoidalClosed.uncurry
        ((CategoryTheory.expComparison hoFunctor Z).app
            (CategoryTheory.nerve D) ≫
          (ihom (hoFunctor.obj Z)).map
            (CategoryTheory.nerveAdjunction.counit.app (Cat.of D)))).toFunctor =
      Truncated.HomotopyCategory.BinaryProduct.inverse
          ((truncation 2).obj Z)
          ((truncation 2).obj ((ihom Z).obj (CategoryTheory.nerve D))) ⋙
        mapHomotopyCategory ((ihom.ev Z).app (CategoryTheory.nerve D)) ⋙
          descNerve (𝟙 (CategoryTheory.nerve D)) := by
  have h1 : (MonoidalClosed.uncurry
        ((CategoryTheory.expComparison hoFunctor Z).app
            (CategoryTheory.nerve D) ≫
          (ihom (hoFunctor.obj Z)).map
            (CategoryTheory.nerveAdjunction.counit.app (Cat.of D)))).toFunctor =
      (inv (CartesianMonoidalCategory.prodComparison hoFunctor Z
          ((ihom Z).obj (CategoryTheory.nerve D)))).toFunctor ⋙
        (hoFunctor.map ((ihom.ev Z).app (CategoryTheory.nerve D))).toFunctor ⋙
          (CategoryTheory.nerveAdjunction.counit.app (Cat.of D)).toFunctor :=
    congrArg Cat.Hom.toFunctor uncurry_hoFunNerveComparison
  rw [h1, inv_prodComparison_hoFunctor_toFunctor,
    nerveAdjunction_counit_app_toFunctor]
  rfl

/-- Transport of `CategoryTheory.nerve.homEquiv` along endpoint
equalities. -/
private lemma nerve_homEquiv_eq_of_edge_eq {a₁ a₂ b₁ b₂ : (CategoryTheory.nerve D) _⦋0⦌}
    {e₁ : Edge a₁ b₁} {e₂ : Edge a₂ b₂}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (h : e₁.edge = e₂.edge) :
    CategoryTheory.nerve.homEquiv e₁ =
      eqToHom (congrArg CategoryTheory.nerveEquiv ha) ≫
        CategoryTheory.nerve.homEquiv e₂ ≫
          eqToHom (congrArg CategoryTheory.nerveEquiv hb).symm := by
  subst ha
  subst hb
  rw [Edge.ext h]
  simp

/-- Objects of an exponential in `Cat` are computed by uncurrying:
evaluation is definitional. -/
private lemma cat_uncurry_toFunctor_obj {Pc Qc Rc : Type u} [Category.{u} Pc]
    [Category.{u} Qc] [Category.{u} Rc]
    (φ : Cat.of Pc ⟶ (ihom (Cat.of Qc)).obj (Cat.of Rc)) (a : Pc) (b : Qc) :
    (φ.toFunctor.obj a).obj b =
      (MonoidalClosed.uncurry φ).toFunctor.obj (b, a) := rfl

/-- Morphisms of an exponential in `Cat` are computed by uncurrying. -/
private lemma cat_uncurry_toFunctor_map {Pc Qc Rc : Type u} [Category.{u} Pc]
    [Category.{u} Qc] [Category.{u} Rc]
    (φ : Cat.of Pc ⟶ (ihom (Cat.of Qc)).obj (Cat.of Rc)) (a : Pc) {b₀ b₁ : Qc}
    (ψ : b₀ ⟶ b₁) :
    (φ.toFunctor.obj a).map ψ =
      (MonoidalClosed.uncurry φ).toFunctor.map (Prod.mkHom ψ (𝟙 a)) := by
  change (φ.toFunctor.obj a).map ψ =
    (Functor.uncurry.obj φ.toFunctor.flip).map (Prod.mkHom ψ (𝟙 a))
  simp [Functor.uncurry]

/-- **Object formula for the comparison functor:** the vertex of
`h Fun(Z, nerve D)` classified by `m : Z ⟶ nerve D` maps to the descent
`SSet.descNerve m`. -/
theorem hoFunNerveComparison_obj_mk_ihomVertexEquiv (m : Z ⟶ CategoryTheory.nerve D) :
    (hoFunNerveComparison Z D).obj
        (HomotopyCategory.mk (ihomVertexEquiv Z _ m)) = descNerve m := by
  have hobj : ∀ z : Z _⦋0⦌,
      ((hoFunNerveComparison Z D).obj
          (HomotopyCategory.mk (ihomVertexEquiv Z _ m))).obj
            (HomotopyCategory.mk z) =
        (descNerve m).obj (HomotopyCategory.mk z) := by
    intro z
    have h1 : ((hoFunNerveComparison Z D).obj
          (HomotopyCategory.mk (ihomVertexEquiv Z _ m))).obj
            (HomotopyCategory.mk z) =
        (MonoidalClosed.uncurry
          ((CategoryTheory.expComparison hoFunctor Z).app
              (CategoryTheory.nerve D) ≫
            (ihom (hoFunctor.obj Z)).map
              (CategoryTheory.nerveAdjunction.counit.app (Cat.of D)))).toFunctor.obj
          (HomotopyCategory.mk z, HomotopyCategory.mk (ihomVertexEquiv Z _ m)) :=
      cat_uncurry_toFunctor_obj _ _ _
    rw [h1, uncurry_hoFunNerveComparison_toFunctor]
    change (descNerve (𝟙 (CategoryTheory.nerve D))).obj
        (HomotopyCategory.mk
          (((ihom.ev Z).app (CategoryTheory.nerve D)).app (op ⦋0⦌)
            (z, ihomVertexEquiv Z _ m))) = _
    rw [descNerve_obj_mk, descNerve_obj_mk, ihom_ev_app_zero_ihomVertexEquiv]
    rfl
  apply Truncated.HomotopyCategory.functor_ext hobj
  intro z₀ z₁ ε
  let e : Edge z₀ z₁ := Edge.ofTruncated (X := Z) ε
  have hmap : ((hoFunNerveComparison Z D).obj
        (HomotopyCategory.mk (ihomVertexEquiv Z _ m))).map
          (HomotopyCategory.homMk e) =
      (MonoidalClosed.uncurry
          ((CategoryTheory.expComparison hoFunctor Z).app
              (CategoryTheory.nerve D) ≫
            (ihom (hoFunctor.obj Z)).map
              (CategoryTheory.nerveAdjunction.counit.app (Cat.of D)))).toFunctor.map
        (Prod.mkHom (HomotopyCategory.homMk e)
          (𝟙 (HomotopyCategory.mk (ihomVertexEquiv Z _ m)))) :=
    cat_uncurry_toFunctor_map _ _ _
  have hcongr : (MonoidalClosed.uncurry
          ((CategoryTheory.expComparison hoFunctor Z).app
              (CategoryTheory.nerve D) ≫
            (ihom (hoFunctor.obj Z)).map
              (CategoryTheory.nerveAdjunction.counit.app (Cat.of D)))).toFunctor.map
        (Prod.mkHom (HomotopyCategory.homMk e)
          (𝟙 (HomotopyCategory.mk (ihomVertexEquiv Z _ m)))) =
      eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
          (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫
        (Truncated.HomotopyCategory.BinaryProduct.inverse
            ((truncation 2).obj Z)
            ((truncation 2).obj ((ihom Z).obj (CategoryTheory.nerve D))) ⋙
          mapHomotopyCategory ((ihom.ev Z).app (CategoryTheory.nerve D)) ⋙
            descNerve (𝟙 (CategoryTheory.nerve D))).map
          (Prod.mkHom (HomotopyCategory.homMk e)
            (𝟙 (HomotopyCategory.mk (ihomVertexEquiv Z _ m)))) ≫
          eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
            (HomotopyCategory.mk z₁,
              HomotopyCategory.mk (ihomVertexEquiv Z _ m))).symm :=
    Functor.congr_hom uncurry_hoFunNerveComparison_toFunctor _
  have hrhs : (Truncated.HomotopyCategory.BinaryProduct.inverse
        ((truncation 2).obj Z)
        ((truncation 2).obj ((ihom Z).obj (CategoryTheory.nerve D))) ⋙
      mapHomotopyCategory ((ihom.ev Z).app (CategoryTheory.nerve D)) ⋙
        descNerve (𝟙 (CategoryTheory.nerve D))).map
      (Prod.mkHom (HomotopyCategory.homMk e)
        (𝟙 (HomotopyCategory.mk (ihomVertexEquiv Z _ m)))) =
      CategoryTheory.nerve.homEquiv
        (((e.tensor (Edge.id (ihomVertexEquiv Z _ m))).map
          ((ihom.ev Z).app (CategoryTheory.nerve D))).map
          (𝟙 (CategoryTheory.nerve D))) := by
    change (descNerve (𝟙 (CategoryTheory.nerve D))).map
        (HomotopyCategory.homMk
          ((e.tensor (Edge.id (ihomVertexEquiv Z _ m))).map
            ((ihom.ev Z).app (CategoryTheory.nerve D)))) = _
    rw [descNerve_map_homMk]
  have htr : CategoryTheory.nerve.homEquiv
        (((e.tensor (Edge.id (ihomVertexEquiv Z _ m))).map
          ((ihom.ev Z).app (CategoryTheory.nerve D))).map
          (𝟙 (CategoryTheory.nerve D))) =
      eqToHom (congrArg CategoryTheory.nerveEquiv
          (ihom_ev_app_zero_ihomVertexEquiv m z₀)) ≫
        CategoryTheory.nerve.homEquiv (e.map m) ≫
          eqToHom (congrArg CategoryTheory.nerveEquiv
            (ihom_ev_app_zero_ihomVertexEquiv m z₁)).symm :=
    nerve_homEquiv_eq_of_edge_eq (ihom_ev_app_zero_ihomVertexEquiv m z₀)
      (ihom_ev_app_zero_ihomVertexEquiv m z₁)
      (ihom_ev_app_one_ihomVertexEquiv m e)
  have hdesc : (descNerve m).map (HomotopyCategory.homMk e) =
      CategoryTheory.nerve.homEquiv (e.map m) :=
    descNerve_map_homMk m e
  have e1 : eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
        (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫
      eqToHom (congrArg CategoryTheory.nerveEquiv
        (ihom_ev_app_zero_ihomVertexEquiv m z₀)) = eqToHom (hobj z₀) :=
    eqToHom_trans _ _
  have e2 : eqToHom (congrArg CategoryTheory.nerveEquiv
        (ihom_ev_app_zero_ihomVertexEquiv m z₁)).symm ≫
      eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
        (HomotopyCategory.mk z₁, HomotopyCategory.mk (ihomVertexEquiv Z _ m))).symm =
      eqToHom (hobj z₁).symm :=
    eqToHom_trans _ _
  change ((hoFunNerveComparison Z D).obj
        (HomotopyCategory.mk (ihomVertexEquiv Z _ m))).map
          (HomotopyCategory.homMk e) =
      eqToHom (hobj z₀) ≫ (descNerve m).map (HomotopyCategory.homMk e) ≫
        eqToHom (hobj z₁).symm
  have s3 : eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
        (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫
      (Truncated.HomotopyCategory.BinaryProduct.inverse
          ((truncation 2).obj Z)
          ((truncation 2).obj ((ihom Z).obj (CategoryTheory.nerve D))) ⋙
        mapHomotopyCategory ((ihom.ev Z).app (CategoryTheory.nerve D)) ⋙
          descNerve (𝟙 (CategoryTheory.nerve D))).map
        (Prod.mkHom (HomotopyCategory.homMk e)
          (𝟙 (HomotopyCategory.mk (ihomVertexEquiv Z _ m)))) ≫
        eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
          (HomotopyCategory.mk z₁,
            HomotopyCategory.mk (ihomVertexEquiv Z _ m))).symm =
      eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
        (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫
      ((eqToHom (congrArg CategoryTheory.nerveEquiv
            (ihom_ev_app_zero_ihomVertexEquiv m z₀)) ≫
          CategoryTheory.nerve.homEquiv (e.map m) ≫
            eqToHom (congrArg CategoryTheory.nerveEquiv
              (ihom_ev_app_zero_ihomVertexEquiv m z₁)).symm) ≫
        eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
          (HomotopyCategory.mk z₁,
            HomotopyCategory.mk (ihomVertexEquiv Z _ m))).symm) :=
    congrArg (fun t => eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
          (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫ t ≫
        eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
          (HomotopyCategory.mk z₁,
            HomotopyCategory.mk (ihomVertexEquiv Z _ m))).symm) (hrhs.trans htr)
  have s4 : eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
        (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫
      ((eqToHom (congrArg CategoryTheory.nerveEquiv
            (ihom_ev_app_zero_ihomVertexEquiv m z₀)) ≫
          CategoryTheory.nerve.homEquiv (e.map m) ≫
            eqToHom (congrArg CategoryTheory.nerveEquiv
              (ihom_ev_app_zero_ihomVertexEquiv m z₁)).symm) ≫
        eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
          (HomotopyCategory.mk z₁,
            HomotopyCategory.mk (ihomVertexEquiv Z _ m))).symm) =
      eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
        (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫
      (eqToHom (congrArg CategoryTheory.nerveEquiv
          (ihom_ev_app_zero_ihomVertexEquiv m z₀)) ≫
        ((CategoryTheory.nerve.homEquiv (e.map m) ≫
            eqToHom (congrArg CategoryTheory.nerveEquiv
              (ihom_ev_app_zero_ihomVertexEquiv m z₁)).symm) ≫
          eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
            (HomotopyCategory.mk z₁,
              HomotopyCategory.mk (ihomVertexEquiv Z _ m))).symm)) :=
    congrArg (fun t => eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
          (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫ t)
      (Category.assoc _ _ _)
  have s5 : eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
        (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫
      (eqToHom (congrArg CategoryTheory.nerveEquiv
          (ihom_ev_app_zero_ihomVertexEquiv m z₀)) ≫
        ((CategoryTheory.nerve.homEquiv (e.map m) ≫
            eqToHom (congrArg CategoryTheory.nerveEquiv
              (ihom_ev_app_zero_ihomVertexEquiv m z₁)).symm) ≫
          eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
            (HomotopyCategory.mk z₁,
              HomotopyCategory.mk (ihomVertexEquiv Z _ m))).symm)) =
      eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
        (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫
      (eqToHom (congrArg CategoryTheory.nerveEquiv
          (ihom_ev_app_zero_ihomVertexEquiv m z₀)) ≫
        (CategoryTheory.nerve.homEquiv (e.map m) ≫
          (eqToHom (congrArg CategoryTheory.nerveEquiv
              (ihom_ev_app_zero_ihomVertexEquiv m z₁)).symm ≫
            eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
              (HomotopyCategory.mk z₁,
                HomotopyCategory.mk (ihomVertexEquiv Z _ m))).symm))) :=
    congrArg (fun t => eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
          (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫
        (eqToHom (congrArg CategoryTheory.nerveEquiv
            (ihom_ev_app_zero_ihomVertexEquiv m z₀)) ≫ t)) (Category.assoc _ _ _)
  have s6 : eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
        (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫
      (eqToHom (congrArg CategoryTheory.nerveEquiv
          (ihom_ev_app_zero_ihomVertexEquiv m z₀)) ≫
        (CategoryTheory.nerve.homEquiv (e.map m) ≫
          (eqToHom (congrArg CategoryTheory.nerveEquiv
              (ihom_ev_app_zero_ihomVertexEquiv m z₁)).symm ≫
            eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
              (HomotopyCategory.mk z₁,
                HomotopyCategory.mk (ihomVertexEquiv Z _ m))).symm))) =
      (eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
        (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫
      eqToHom (congrArg CategoryTheory.nerveEquiv
          (ihom_ev_app_zero_ihomVertexEquiv m z₀))) ≫
      (CategoryTheory.nerve.homEquiv (e.map m) ≫
        (eqToHom (congrArg CategoryTheory.nerveEquiv
            (ihom_ev_app_zero_ihomVertexEquiv m z₁)).symm ≫
          eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
            (HomotopyCategory.mk z₁,
              HomotopyCategory.mk (ihomVertexEquiv Z _ m))).symm)) :=
    (Category.assoc _ _ _).symm
  have s7 : (eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
        (HomotopyCategory.mk z₀, HomotopyCategory.mk (ihomVertexEquiv Z _ m))) ≫
      eqToHom (congrArg CategoryTheory.nerveEquiv
          (ihom_ev_app_zero_ihomVertexEquiv m z₀))) ≫
      (CategoryTheory.nerve.homEquiv (e.map m) ≫
        (eqToHom (congrArg CategoryTheory.nerveEquiv
            (ihom_ev_app_zero_ihomVertexEquiv m z₁)).symm ≫
          eqToHom (Functor.congr_obj uncurry_hoFunNerveComparison_toFunctor
            (HomotopyCategory.mk z₁,
              HomotopyCategory.mk (ihomVertexEquiv Z _ m))).symm)) =
      eqToHom (hobj z₀) ≫ (descNerve m).map (HomotopyCategory.homMk e) ≫
        eqToHom (hobj z₁).symm := by
    rw [e1, e2, hdesc]
    rfl
  exact hmap.trans (hcongr.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))

end SSet

end
