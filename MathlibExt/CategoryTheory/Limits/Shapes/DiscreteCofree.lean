/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Cofree diagrams from products

For categories I and C, right Kan extension along the inclusion Discrete I → I
is the cofree diagram functor. At an object i, its value is the product of
the coefficient objects indexed by pairs (j, f), where f : i → j. Distinct
parallel arrows give distinct coordinates. The coordinate of the adjunction
unit at (j, f) is the given diagram map F(f), and transitions reindex these
coordinates by precomposition.

Products over each outgoing slice supply the pointwise right Kan extension.
The comparison of its global limit with the product of all coefficient
objects separately requires I-shaped limits and products indexed by I.
The index, object and morphism universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable (I : Type u₁) [Category.{v₁} I]

/-- The inclusion Discrete I → I is the identity on objects and retains only identity arrows. -/
@[implicit_reducible]
def discreteCofreeInclusion : Discrete I ⥤ I := Discrete.functor id

variable {I}

/-- The outgoing product index at i consists of a target j and a morphism i → j. -/
abbrev discreteCofreeIndex (i : I) : Type (max u₁ v₁) := Σ j : I, i ⟶ j

/-- A target-arrow pair defines the corresponding object of the structured-arrow slice at i. -/
@[implicit_reducible]
def discreteCofreeIndexToArrow (i : I) :
    Discrete (discreteCofreeIndex i) ⥤ StructuredArrow i (discreteCofreeInclusion I) :=
  Discrete.functor fun p ↦ StructuredArrow.mk (Y := Discrete.mk p.1) p.2

/-- The target and structure map recover an outgoing pair from the structured-arrow slice. -/
@[implicit_reducible]
def discreteCofreeArrowToIndex (i : I) :
    StructuredArrow i (discreteCofreeInclusion I) ⥤ Discrete (discreteCofreeIndex i) where
  obj x := Discrete.mk ⟨x.right.as, x.hom⟩
  map {x y} f := by
    have hr : x.right = y.right := Discrete.ext (Discrete.eq_of_hom f.right)
    have hxy : x = y := by
      apply StructuredArrow.obj_ext x y hr
      have hf : eqToHom hr = f.right := Subsingleton.elim _ _
      rw [hf]
      exact StructuredArrow.w f
    exact Discrete.eqToHom (congrArg
      (fun x : StructuredArrow i (discreteCofreeInclusion I) ↦
        (⟨x.right.as, x.hom⟩ : discreteCofreeIndex i)) hxy)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The structured-arrow slice at i is equivalent to the discrete category of outgoing
target-arrow pairs. -/
@[implicit_reducible]
def discreteCofreeIndexEquivalence (i : I) :
    Discrete (discreteCofreeIndex i) ≌ StructuredArrow i (discreteCofreeInclusion I) :=
  Equivalence.mk (discreteCofreeIndexToArrow i) (discreteCofreeArrowToIndex i)
    (Discrete.natIso fun p ↦ Discrete.eqToIso (by
      rcases p with ⟨⟨j, f⟩⟩
      rfl))
    (NatIso.ofComponents
      (fun x ↦ StructuredArrow.isoMk (Discrete.eqToIso (by rfl)) (by
        change x.hom ≫ 𝟙 _ = x.hom
        exact Category.comp_id _))
      (fun {_ _} f ↦ by
        apply StructuredArrow.hom_ext
        exact Subsingleton.elim _ _))

variable (A : Type u₂) [Category.{v₂} A]

/-- Products indexed by the outgoing pairs at i give limits over the structured-arrow slice at i. -/
instance discreteCofreeSliceHasLimits (i : I)
    [HasProductsOfShape (discreteCofreeIndex i) A] :
    HasLimitsOfShape (StructuredArrow i (discreteCofreeInclusion I)) A :=
  hasLimitsOfShape_of_equivalence (discreteCofreeIndexEquivalence i)

/-- Products over every outgoing slice give the pointwise right Kan extension of a discrete
coefficient diagram. -/
instance discreteCofreeHasPointwiseRightKanExtension
    [∀ i : I, HasProductsOfShape (discreteCofreeIndex i) A] (V : Discrete I ⥤ A) :
    Functor.HasPointwiseRightKanExtension (discreteCofreeInclusion I) V :=
  fun i ↦ by
    have : HasLimitsOfShape (StructuredArrow i (discreteCofreeInclusion I)) A :=
      discreteCofreeSliceHasLimits A i
    infer_instance

/-- Restriction along Discrete I → I retains the object family of an I-shaped diagram. -/
abbrev discreteCofreeRestriction : (I ⥤ A) ⥤ (Discrete I ⥤ A) :=
  (Functor.whiskeringLeft (Discrete I) I A).obj (discreteCofreeInclusion I)

/-- Restriction to the discrete object family is faithful because a diagram morphism is determined
by its components. -/
instance discreteCofreeRestrictionFaithful :
    (discreteCofreeRestriction (I := I) A).Faithful where
  map_injective h := NatTrans.ext (funext fun i ↦ congr_app h (Discrete.mk i))

section Ran

variable [∀ V : Discrete I ⥤ A,
  Functor.HasRightKanExtension (discreteCofreeInclusion I) V]

/-- Right Kan extension along Discrete I → I is the cofree functor on discrete coefficient
diagrams. -/
abbrev discreteCofreeFunctor : (Discrete I ⥤ A) ⥤ (I ⥤ A) :=
  (discreteCofreeInclusion I).ran

/-- The adjunction unit maps a diagram to the cofree diagram on its discrete object family. -/
abbrev discreteCofreeUnit : 𝟭 (I ⥤ A) ⟶
    discreteCofreeRestriction (I := I) A ⋙ discreteCofreeFunctor (I := I) A :=
  ((discreteCofreeInclusion I).ranAdjunction A).unit

/-- The outgoing coordinate (j, f) is the cofree diagram map along f followed by the counit at j. -/
abbrev discreteCofreeπ (V : Discrete I ⥤ A) (i : I) (p : discreteCofreeIndex i) :
    ((discreteCofreeFunctor (I := I) A).obj V).obj i ⟶ V.obj (Discrete.mk p.1) :=
  ((discreteCofreeFunctor (I := I) A).obj V).map p.2 ≫
    ((discreteCofreeInclusion I).ranCounit.app V).app (Discrete.mk p.1)

/-- A cofree transition along g : i → i′ sends the coordinate indexed by f : i′ → j to the
coordinate indexed by g ≫ f. -/
@[reassoc]
theorem discreteCofree_transition_π (V : Discrete I ⥤ A) {i i' : I} (g : i ⟶ i')
    (p : discreteCofreeIndex i') :
    ((discreteCofreeFunctor (I := I) A).obj V).map g ≫ discreteCofreeπ A V i' p =
      discreteCofreeπ A V i ⟨p.1, g ≫ p.2⟩ := by
  simp only [discreteCofreeπ, Functor.map_comp, Category.assoc]

/-- The unit followed by the outgoing coordinate (j, f) is the given diagram map along f : i → j. -/
@[reassoc]
theorem discreteCofreeUnit_app_π (M : I ⥤ A) (i : I) (p : discreteCofreeIndex i) :
    ((discreteCofreeUnit (I := I) A).app M).app i ≫
        discreteCofreeπ A (discreteCofreeInclusion I ⋙ M) i p = M.map p.2 := by
  have h := ((discreteCofreeUnit (I := I) A).app M).naturality p.2
  have ht := (discreteCofreeInclusion I).ranCounit_app_app_ranAdjunction_unit_app_app
    M (Discrete.mk p.1)
  change M.map p.2 ≫ ((discreteCofreeUnit (I := I) A).app M).app p.1 =
    ((discreteCofreeUnit (I := I) A).app M).app i ≫
      ((discreteCofreeFunctor (I := I) A).obj (discreteCofreeInclusion I ⋙ M)).map p.2 at h
  calc
    _ = M.map p.2 ≫
        (((discreteCofreeUnit (I := I) A).app M).app p.1 ≫
          ((discreteCofreeInclusion I).ranCounit.app
            (discreteCofreeInclusion I ⋙ M)).app (Discrete.mk p.1)) := by
      simpa only [discreteCofreeπ, Category.assoc] using
        (congrArg (fun k ↦ k ≫ ((discreteCofreeInclusion I).ranCounit.app
          (discreteCofreeInclusion I ⋙ M)).app (Discrete.mk p.1)) h).symm
    _ = _ := by
      change ((discreteCofreeUnit (I := I) A).app M).app p.1 ≫
          ((discreteCofreeInclusion I).ranCounit.app
            (discreteCofreeInclusion I ⋙ M)).app (Discrete.mk p.1) =
        𝟙 (M.obj p.1) at ht
      simpa only [Category.comp_id] using
        congrArg (fun k ↦ M.map p.2 ≫ k) ht

/-- When the pointwise right Kan extension and the outgoing product exist, the cofree value at i
is canonically isomorphic to that product. -/
def discreteCofreeObjIso (V : Discrete I ⥤ A)
    [Functor.HasPointwiseRightKanExtension (discreteCofreeInclusion I) V] (i : I)
    [HasProductsOfShape (discreteCofreeIndex i) A] :
    ((discreteCofreeFunctor (I := I) A).obj V).obj i ≅
      ∏ᶜ fun p : discreteCofreeIndex i ↦ V.obj (Discrete.mk p.1) :=
  let P := Discrete.functor fun p : discreteCofreeIndex i ↦ V.obj (Discrete.mk p.1)
  let G := StructuredArrow.proj i (discreteCofreeInclusion I) ⋙ V
  let e := discreteCofreeIndexEquivalence i
  let w : e.functor ⋙ G ≅ P := Discrete.natIso fun _ ↦ Iso.refl _
  (discreteCofreeInclusion I).ranObjObjIsoLimit V i ≪≫
    (HasLimit.isoOfEquivalence e w).symm

/-- The product comparison followed by the projection at (j, f) is the cofree coordinate given by
f and the counit at j. -/
@[reassoc]
theorem discreteCofreeObjIso_hom_π (V : Discrete I ⥤ A)
    [Functor.HasPointwiseRightKanExtension (discreteCofreeInclusion I) V] (i : I)
    [HasProductsOfShape (discreteCofreeIndex i) A] (p : discreteCofreeIndex i) :
    (discreteCofreeObjIso A V i).hom ≫ Pi.π _ p = discreteCofreeπ A V i p := by
  dsimp only [discreteCofreeObjIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    HasLimit.isoOfEquivalence_inv_π, Discrete.natIso_hom_app, Iso.refl_hom]
  change ((discreteCofreeInclusion I).ranObjObjIsoLimit V i).hom ≫
      limit.π _ ((discreteCofreeIndexToArrow i).obj (Discrete.mk p)) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  simpa only [discreteCofreeπ, discreteCofreeIndexToArrow, Discrete.functor_obj,
    StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self] using
      (discreteCofreeInclusion I).ranObjObjIsoLimit_hom_π V i
        ((discreteCofreeIndexToArrow i).obj (Discrete.mk p))

section GlobalLimit

variable [HasLimitsOfShape I A] [HasProductsOfShape I A]

/-- Assuming I-shaped limits, I-indexed products and right Kan extensions, the limit of a cofree
diagram is the product of its discrete coefficient objects. -/
def discreteCofreeLimitIso (V : Discrete I ⥤ A) :
    limit ((discreteCofreeFunctor (I := I) A).obj V) ≅
      ∏ᶜ fun j : I ↦ V.obj (Discrete.mk j) :=
  ((discreteCofreeInclusion I).ranCompLimIso (H := A)).app V ≪≫
    HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := V))

/-- The global limit comparison followed by the coefficient projection at j is the diagram limit
projection at j followed by the counit. -/
@[reassoc]
theorem discreteCofreeLimitIso_hom_π (V : Discrete I ⥤ A) (j : I) :
    (discreteCofreeLimitIso A V).hom ≫ Pi.π _ j =
      limit.π ((discreteCofreeFunctor (I := I) A).obj V) j ≫
        ((discreteCofreeInclusion I).ranCounit.app V).app (Discrete.mk j) := by
  dsimp only [discreteCofreeLimitIso]
  simp only [Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π,
    Discrete.natIsoFunctor_hom_app, Category.comp_id]
  change (((discreteCofreeFunctor (I := I) A).obj V).limitIsoOfIsRightKanExtension
    ((discreteCofreeInclusion I).ranCounit.app V)).hom ≫ limit.π V (Discrete.mk j) = _
  exact Functor.limitIsoOfIsRightKanExtension_hom_π _ _ (Discrete.mk j)

end GlobalLimit
end Ran

end CategoryTheory.Limits

end
