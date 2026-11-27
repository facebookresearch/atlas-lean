/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Cofree inverse sequences

Let C be a category with finite products and F : ℕᵒᵖ → C an inverse sequence.
Right Kan extension of its discrete object family gives a cofree envelope.
Its value at n is the product of F(m) over 0 ≤ m ≤ n, since the outgoing
structured-arrow slice at n is a finite discrete prefix.

The adjunction unit is monic. Its component at n has coordinates given by the
maps F(n) → F(m), and projection onto m = n is a retraction of that component.
The cofree transition from n + 1 to n drops the last coordinate. When C has
zero morphisms, insertion of zero supplies a section of this transition.
The component retractions need not assemble into a retraction of diagrams.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe u v

/-- The inclusion of the discrete object family of ℕᵒᵖ is the identity on objects. -/
@[implicit_reducible]
def sequentialDiscreteInclusion : Discrete ℕᵒᵖ ⥤ ℕᵒᵖ :=
  Discrete.functor id

/-- The discrete inclusion sends an index to its underlying object of ℕᵒᵖ. -/
@[simp]
theorem sequentialDiscreteInclusion_obj (X : Discrete ℕᵒᵖ) :
    sequentialDiscreteInclusion.obj X = X.as := rfl

/-- An index m ≤ n gives the outgoing structured arrow from n to m in ℕᵒᵖ. -/
@[implicit_reducible]
def sequentialPrefixToComma (n : ℕ) :
    Discrete (Fin (n + 1)) ⥤ StructuredArrow (op n) sequentialDiscreteInclusion :=
  Discrete.functor fun i =>
    StructuredArrow.mk (Y := Discrete.mk (op i.val))
      (homOfLE (Nat.le_of_lt_succ i.isLt)).op

/-- An outgoing structured arrow at n recovers its target index m in the finite prefix 0 ≤ m ≤ n. -/
@[implicit_reducible]
def sequentialCommaToPrefix (n : ℕ) :
    StructuredArrow (op n) sequentialDiscreteInclusion ⥤ Discrete (Fin (n + 1)) where
  obj f := Discrete.mk
    ⟨f.right.as.unop, Nat.lt_succ_of_le (leOfHom f.hom.unop)⟩
  map {X Y} f := Discrete.eqToHom (by
    apply Fin.ext
    exact congrArg unop (Discrete.eq_of_hom f.right))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The outgoing structured-arrow slice at n is equivalent to the discrete finite prefix Fin (n +
1). -/
@[implicit_reducible]
def sequentialPrefixIndexEquivalence (n : ℕ) :
    Discrete (Fin (n + 1)) ≌ StructuredArrow (op n) sequentialDiscreteInclusion :=
  Equivalence.mk (sequentialPrefixToComma n) (sequentialCommaToPrefix n)
    (Discrete.natIso fun i => Discrete.eqToIso (by
      apply Fin.ext
      rfl))
    (NatIso.ofComponents
      (fun f => StructuredArrow.isoMk
        (Discrete.eqToIso (by rfl)) (Subsingleton.elim _ _))
      (fun _ => by
        apply StructuredArrow.hom_ext
        exact Subsingleton.elim _ _))

/-- The forward slice equivalence sends m ≤ n to the inverse-sequence arrow from n to m. -/
@[simp]
theorem sequentialPrefixIndexEquivalence_obj (n : ℕ) (i : Fin (n + 1)) :
    (sequentialPrefixIndexEquivalence n).functor.obj (Discrete.mk i) =
      StructuredArrow.mk (Y := Discrete.mk (op i.val))
        (homOfLE (Nat.le_of_lt_succ i.isLt)).op := rfl

variable (C : Type u) [Category.{v} C]

/-- Finite products in C give limits over each outgoing structured-arrow slice of the discrete
inclusion of ℕᵒᵖ. -/
instance sequentialCommaHasLimits [HasFiniteProducts C] (n : ℕ) :
    HasLimitsOfShape (StructuredArrow (op n) sequentialDiscreteInclusion) C :=
  hasLimitsOfShape_of_equivalence (sequentialPrefixIndexEquivalence n)

/-- Finite products give the pointwise right Kan extension of any discrete family indexed by ℕᵒᵖ. -/
instance sequentialDiscreteHasPointwiseRightKanExtension [HasFiniteProducts C]
    (F : Discrete ℕᵒᵖ ⥤ C) :
    Functor.HasPointwiseRightKanExtension sequentialDiscreteInclusion F :=
  fun X => by
    have : HasLimitsOfShape (StructuredArrow X sequentialDiscreteInclusion) C :=
      sequentialCommaHasLimits C X.unop
    infer_instance

/-- Restriction retains every object of an inverse sequence and forgets its transition maps. -/
abbrev sequentialRestriction : (ℕᵒᵖ ⥤ C) ⥤ (Discrete ℕᵒᵖ ⥤ C) :=
  (Functor.whiskeringLeft (Discrete ℕᵒᵖ) ℕᵒᵖ C).obj sequentialDiscreteInclusion

/-- A morphism of inverse sequences is determined by its components, so discrete restriction is
faithful. -/
instance sequentialRestrictionFaithful : (sequentialRestriction C).Faithful where
  map_injective h := NatTrans.ext (funext fun X => congr_app h (Discrete.mk X))

variable [HasFiniteProducts C]

/-- The cofree envelope of an inverse sequence is the right Kan extension of its discrete object
family. -/
abbrev sequentialCofreeFunctor : (ℕᵒᵖ ⥤ C) ⥤ (ℕᵒᵖ ⥤ C) :=
  sequentialRestriction C ⋙ sequentialDiscreteInclusion.ran

/-- The adjunction unit maps an inverse sequence into its cofree envelope. -/
abbrev sequentialCofreeUnit : 𝟭 (ℕᵒᵖ ⥤ C) ⟶ sequentialCofreeFunctor C :=
  (sequentialDiscreteInclusion.ranAdjunction C).unit

/-- The cofree unit is a monomorphism of inverse sequences because discrete restriction is
faithful. -/
instance sequentialCofreeUnitMono (F : ℕᵒᵖ ⥤ C) :
    Mono ((sequentialCofreeUnit C).app F) :=
  Adjunction.unit_mono_of_L_faithful (sequentialDiscreteInclusion.ranAdjunction C) F

/-- The cofree value at n is canonically isomorphic to the product of the given sequence over 0 ≤
m ≤ n. -/
def sequentialCofreePrefixIso (F : ℕᵒᵖ ⥤ C) (n : ℕ) :
    ((sequentialCofreeFunctor C).obj F).obj (op n) ≅
      ∏ᶜ fun i : Fin (n + 1) => F.obj (op i.val) :=
  let P := Discrete.functor fun i : Fin (n + 1) => F.obj (op i.val)
  let G := StructuredArrow.proj (op n) sequentialDiscreteInclusion ⋙
    (sequentialDiscreteInclusion ⋙ F)
  let e := sequentialPrefixIndexEquivalence n
  let w : e.functor ⋙ G ≅ P := Discrete.natIso fun _ => Iso.refl _
  sequentialDiscreteInclusion.ranObjObjIsoLimit
      (sequentialDiscreteInclusion ⋙ F) (op n) ≪≫
    (HasLimit.isoOfEquivalence e w).symm

/-- A finite-prefix coordinate of the cofree value is the diagram map to that index followed by
the counit. -/
@[reassoc (attr := simp)]
theorem sequentialCofreePrefixIso_hom_π (F : ℕᵒᵖ ⥤ C) (n : ℕ)
    (i : Fin (n + 1)) :
    (sequentialCofreePrefixIso C F n).hom ≫ Pi.π _ i =
      ((sequentialCofreeFunctor C).obj F).map
          (homOfLE (Nat.le_of_lt_succ i.isLt)).op ≫
        (sequentialDiscreteInclusion.ranCounit.app
          (sequentialDiscreteInclusion ⋙ F)).app (Discrete.mk (op i.val)) := by
  dsimp only [sequentialCofreePrefixIso, sequentialCofreeFunctor, sequentialRestriction,
    Functor.comp_obj, Functor.whiskeringLeft_obj_obj]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    HasLimit.isoOfEquivalence_inv_π, Discrete.natIso_hom_app,
    Iso.refl_hom]
  dsimp only [sequentialPrefixIndexEquivalence_obj, StructuredArrow.proj_obj,
    StructuredArrow.mk_right, sequentialDiscreteInclusion_obj]
  let p : limit (StructuredArrow.proj (op n) sequentialDiscreteInclusion ⋙
      sequentialDiscreteInclusion ⋙ F) ⟶ F.obj (op i.val) :=
    limit.π _ (StructuredArrow.mk (Y := Discrete.mk (op i.val))
      (homOfLE (Nat.le_of_lt_succ i.isLt)).op)
  change (sequentialDiscreteInclusion.ranObjObjIsoLimit
    (sequentialDiscreteInclusion ⋙ F) (op n)).hom ≫ p ≫ 𝟙 _ = _
  rw [Category.comp_id]
  simpa only [sequentialPrefixToComma, Discrete.functor_obj,
    StructuredArrow.mk_hom_eq_self, StructuredArrow.mk_right] using
      sequentialDiscreteInclusion.ranObjObjIsoLimit_hom_π
        (sequentialDiscreteInclusion ⋙ F) (op n)
        ((sequentialPrefixToComma n).obj (Discrete.mk i))

/-- The component of the unit at n, followed by the projection at m ≤ n, is the given
inverse-sequence map from n to m. -/
@[reassoc]
theorem sequentialCofreeUnit_app_π (F : ℕᵒᵖ ⥤ C) (n : ℕ)
    (i : Fin (n + 1)) :
    ((sequentialCofreeUnit C).app F).app (op n) ≫
        (sequentialCofreePrefixIso C F n).hom ≫ Pi.π _ i =
      F.map (homOfLE (Nat.le_of_lt_succ i.isLt)).op := by
  rw [sequentialCofreePrefixIso_hom_π]
  have h := ((sequentialCofreeUnit C).app F).naturality
    (homOfLE (Nat.le_of_lt_succ i.isLt)).op
  have ht := sequentialDiscreteInclusion.ranCounit_app_app_ranAdjunction_unit_app_app
    F (Discrete.mk (op i.val))
  dsimp only [sequentialCofreeFunctor, sequentialRestriction,
    Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.id_obj,
    sequentialDiscreteInclusion_obj] at h ht ⊢
  calc
    _ = F.map (homOfLE (Nat.le_of_lt_succ i.isLt)).op ≫
        (((sequentialCofreeUnit C).app F).app (op i.val) ≫
          (sequentialDiscreteInclusion.ranCounit.app
            (sequentialDiscreteInclusion ⋙ F)).app (Discrete.mk (op i.val))) := by
      simpa only [Category.assoc] using
        (congrArg (fun f => f ≫ (sequentialDiscreteInclusion.ranCounit.app
          (sequentialDiscreteInclusion ⋙ F)).app (Discrete.mk (op i.val))) h).symm
    _ = _ := by rw [ht, Category.comp_id]

/-- Projection onto the last coordinate retracts the component of the cofree unit at n. This is a
retraction in C, not a retraction of diagrams. -/
def sequentialCofreeUnitStageSplitMono (F : ℕᵒᵖ ⥤ C) (n : ℕ) :
    SplitMono (((sequentialCofreeUnit C).app F).app (op n)) where
  retraction := (sequentialCofreePrefixIso C F n).hom ≫ Pi.π _ (Fin.last n)
  id := by
    have h := sequentialCofreeUnit_app_π C F n (Fin.last n)
    have hi : (homOfLE (Nat.le_of_lt_succ (Fin.last n).isLt)).op = 𝟙 (op n) :=
      Subsingleton.elim _ _
    rw [hi, F.map_id] at h
    dsimp only [Functor.id_obj, Fin.last] at h ⊢
    exact h

/-- Each component of the cofree unit is a split monomorphism, with retraction given by its
last-coordinate projection. -/
instance sequentialCofreeUnitStageIsSplitMono (F : ℕᵒᵖ ⥤ C) (n : ℕ) :
    IsSplitMono (((sequentialCofreeUnit C).app F).app (op n)) :=
  IsSplitMono.mk' (sequentialCofreeUnitStageSplitMono C F n)

/-- The projection from the prefix through n + 1 to the prefix through n drops the last
coordinate. -/
abbrev sequentialCofreePrefixProjection (F : ℕᵒᵖ ⥤ C) (n : ℕ) :
    (∏ᶜ fun i : Fin (n + 2) => F.obj (op i.val)) ⟶
      ∏ᶜ fun i : Fin (n + 1) => F.obj (op i.val) :=
  Pi.lift (fun i : Fin (n + 1) => Pi.π _ i.castSucc)

/-- A successor transition of the cofree inverse sequence preserves each coordinate in the
preceding finite prefix. -/
@[reassoc]
theorem sequentialCofreeTransition_π (F : ℕᵒᵖ ⥤ C) (n : ℕ) (i : Fin (n + 1)) :
    ((sequentialCofreeFunctor C).obj F).map (homOfLE (Nat.le_succ n)).op ≫
        (sequentialCofreePrefixIso C F n).hom ≫ Pi.π _ i =
      (sequentialCofreePrefixIso C F (n + 1)).hom ≫ Pi.π _ i.castSucc := by
  rw [sequentialCofreePrefixIso_hom_π, sequentialCofreePrefixIso_hom_π]
  have hc : (homOfLE (Nat.le_succ n)).op ≫
      (homOfLE (Nat.le_of_lt_succ i.isLt)).op =
      (homOfLE (Nat.le_of_lt_succ i.castSucc.isLt)).op :=
    Subsingleton.elim _ _
  have h := ((sequentialCofreeFunctor C).obj F).map_comp
    (homOfLE (Nat.le_succ n)).op (homOfLE (Nat.le_of_lt_succ i.isLt)).op
  rw [hc] at h
  dsimp only [sequentialCofreeFunctor, sequentialRestriction,
    Functor.comp_obj, Functor.whiskeringLeft_obj_obj] at h ⊢
  have h' := congrArg (fun f => f ≫ (sequentialDiscreteInclusion.ranCounit.app
    (sequentialDiscreteInclusion ⋙ F)).app (Discrete.mk (op i.val))) h
  dsimp only [Functor.id_obj, Functor.comp_obj, sequentialDiscreteInclusion_obj] at h' ⊢
  simpa only [Category.assoc, Fin.val_castSucc] using h'.symm

/-- Under the finite-prefix product comparisons, the cofree successor transition is the projection
dropping the last coordinate. -/
theorem sequentialCofreeTransition_prefix (F : ℕᵒᵖ ⥤ C) (n : ℕ) :
    ((sequentialCofreeFunctor C).obj F).map (homOfLE (Nat.le_succ n)).op ≫
        (sequentialCofreePrefixIso C F n).hom =
      (sequentialCofreePrefixIso C F (n + 1)).hom ≫
        sequentialCofreePrefixProjection C F n := by
  apply Pi.hom_ext
  intro i
  simpa only [sequentialCofreePrefixProjection, Category.assoc,
    Pi.lift_comp_π] using sequentialCofreeTransition_π C F n i

section ZeroSections

variable [HasZeroMorphisms C]

/-- With zero morphisms in C, inserting zero as the new last coordinate gives a section of the
finite-prefix projection. -/
def sequentialCofreePrefixSection (F : ℕᵒᵖ ⥤ C) (n : ℕ) :
    (∏ᶜ fun i : Fin (n + 1) => F.obj (op i.val)) ⟶
      ∏ᶜ fun i : Fin (n + 2) => F.obj (op i.val) :=
  Pi.lift (Fin.lastCases
    (0 : (∏ᶜ fun i : Fin (n + 1) => F.obj (op i.val)) ⟶ F.obj (op (n + 1)))
    (fun i : Fin (n + 1) => Pi.π _ i))

/-- Zero insertion followed by the finite-prefix projection is the identity on the shorter prefix. -/
@[reassoc (attr := simp)]
theorem sequentialCofreePrefixSection_projection (F : ℕᵒᵖ ⥤ C) (n : ℕ) :
    sequentialCofreePrefixSection C F n ≫ sequentialCofreePrefixProjection C F n =
      𝟙 (∏ᶜ fun i : Fin (n + 1) => F.obj (op i.val)) := by
  apply Pi.hom_ext
  intro i
  simp only [sequentialCofreePrefixProjection, sequentialCofreePrefixSection,
    Category.assoc, Pi.lift_comp_π, Fin.lastCases_castSucc, Category.id_comp]

/-- The finite-prefix comparisons transport zero insertion to a section of the cofree successor
transition. -/
def sequentialCofreeTransitionSection (F : ℕᵒᵖ ⥤ C) (n : ℕ) :
    ((sequentialCofreeFunctor C).obj F).obj (op n) ⟶
      ((sequentialCofreeFunctor C).obj F).obj (op (n + 1)) :=
  (sequentialCofreePrefixIso C F n).hom ≫ sequentialCofreePrefixSection C F n ≫
    (sequentialCofreePrefixIso C F (n + 1)).inv

/-- With zero morphisms in C, each cofree successor transition is a split epimorphism with the
transported zero-insertion section. -/
def sequentialCofreeTransitionSplitEpi (F : ℕᵒᵖ ⥤ C) (n : ℕ) :
    SplitEpi (((sequentialCofreeFunctor C).obj F).map (homOfLE (Nat.le_succ n)).op) where
  section_ := sequentialCofreeTransitionSection C F n
  id := by
    apply (cancel_mono (sequentialCofreePrefixIso C F n).hom).1
    simp only [sequentialCofreeTransitionSection, Category.assoc,
      sequentialCofreeTransition_prefix, Iso.inv_hom_id_assoc,
      sequentialCofreePrefixSection_projection, Category.id_comp, Category.comp_id]

/-- Finite products and zero morphisms make every successor transition of a cofree inverse
sequence a split epimorphism. -/
instance sequentialCofreeTransitionIsSplitEpi (F : ℕᵒᵖ ⥤ C) (n : ℕ) :
    IsSplitEpi (((sequentialCofreeFunctor C).obj F).map (homOfLE (Nat.le_succ n)).op) :=
  IsSplitEpi.mk' (sequentialCofreeTransitionSplitEpi C F n)

end ZeroSections

end CategoryTheory.Limits
