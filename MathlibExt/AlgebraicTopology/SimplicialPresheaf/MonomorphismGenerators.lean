/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialPresheaf.Basic
public import MathlibExt.CategoryTheory.Presentable.PresheafMonomorphismFiltration
public import MathlibExt.CategoryTheory.Presentable.BoundedPresheafMonomorphismFamily
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import Mathlib.CategoryTheory.Types.Monomorphisms

/-!
# Genuine generators for all original simplicial-presheaf monomorphisms

Flatten in the ordered site/simplex coordinates. The accepted literal bounded
family and cyclic filtration give every original monomorphism in the generated
left class. Native monomorphism closure and the exact-cardinal small-object
argument prove the reverse inclusion and give the first WFS and its functorial
factorization. Original sites are normalized only through the actual small-model
equivalence, keeping the coefficient universe and whole original Arrow maps.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w vC uC

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MorphismProperty Opposite

namespace SimplicialPresheaf

/-- Ordered flattening of the literal small site: the site coordinate precedes the simplex. -/
def typePresheafEquivalence (D : Type u) [SmallCategory D] :
    SimplicialPresheaf.{u} D ≌ ((D × SimplexCategory)ᵒᵖ ⥤ Type u) := by
  let p : (D × SimplexCategory)ᵒᵖ ≌ Dᵒᵖ × SimplexCategoryᵒᵖ := prodOpEquiv D
  exact Functor.currying.trans p.congrLeft.symm

/-- Flattening preserves the original value in every ordered bidegree. -/
theorem typePresheafEquivalence_obj (D : Type u) [SmallCategory D]
    (X : SimplicialPresheaf.{u} D) (d : D) (n : SimplexCategory) :
    ((typePresheafEquivalence D).functor.obj X).obj (op (d, n)) =
      (X.obj (op d)).obj (op n) := rfl

/-- Flattening preserves each component of the supplied original natural map. -/
theorem typePresheafEquivalence_map (D : Type u) [SmallCategory D]
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) (d : D) (n : SimplexCategory) :
    ((typePresheafEquivalence D).functor.map f).app (op (d, n)) =
      (f.app (op d)).app (op n) := rfl

/-- An original outer/inner operator keeps both coordinates in their source order. -/
theorem typePresheafEquivalence_operator (D : Type u) [SmallCategory D]
    (X : SimplicialPresheaf.{u} D) {a b : Dᵒᵖ} {n m : SimplexCategoryᵒᵖ}
    (f : a ⟶ b) (g : n ⟶ m) :
    ((typePresheafEquivalence D).functor.obj X).map
        (Quiver.Hom.op (CategoryTheory.Prod.mkHom f.unop g.unop)) =
      (X.map f).app n ≫ (X.obj b).map g := rfl

/-- Original carrier normalization followed by ordered flattening, with coefficients still in u. -/
def normalizedTypePresheafEquivalence (D : Type w) [Category.{v} D]
    [Small.{u} D] [LocallySmall.{u} D] :
    SimplicialPresheaf.{u} D ≌ ((SmallModel.{u} D × SimplexCategory)ᵒᵖ ⥤ Type u) :=
  (smallModelTransport (D := D)).trans (typePresheafEquivalence (SmallModel.{u} D))

/-- Normalization evaluates the original diagram at the actual inverse-site object. -/
theorem normalizedTypePresheafEquivalence_obj (D : Type w) [Category.{v} D]
    [Small.{u} D] [LocallySmall.{u} D] (X : SimplicialPresheaf.{u} D)
    (d : SmallModel.{u} D) (n : SimplexCategory) :
    ((normalizedTypePresheafEquivalence D).functor.obj X).obj (op (d, n)) =
      (X.obj (op ((equivSmallModel.{u} D).inverse.obj d))).obj (op n) := rfl

private def boundsAlong {E : Type u} [SmallCategory E]
    {C : Type uC} [Category.{vC} C] (e : C ≌ (Eᵒᵖ ⥤ Type u)) :
    ObjectProperty (Arrow C) := fun a =>
  Mono a.hom ∧
    Cardinal.mk (e.functor.mapArrow.obj a).left.Elements ≤
      max Cardinal.aleph0 (Cardinal.mk (Arrow E)) ∧
    Cardinal.mk (e.functor.mapArrow.obj a).right.Elements ≤
      max Cardinal.aleph0 (Cardinal.mk (Arrow E))

/-- Literal Mono Arrows bounded on their original ordered site/simplex total elements. -/
def boundedMonomorphismArrows (D : Type u) [SmallCategory D] :
    ObjectProperty (Arrow (SimplicialPresheaf.{u} D)) := fun a =>
  Mono a.hom ∧
    Cardinal.mk ((typePresheafEquivalence D).functor.mapArrow.obj a).left.Elements ≤
      max Cardinal.aleph0 (Cardinal.mk (Arrow (D × SimplexCategory))) ∧
    Cardinal.mk ((typePresheafEquivalence D).functor.mapArrow.obj a).right.Elements ≤
      max Cardinal.aleph0 (Cardinal.mk (Arrow (D × SimplexCategory)))

/-- Bounds on the actual normalized small site, while the Mono and its endpoints remain original.
This does not assert that a categorical site equivalence preserves literal element counts. -/
def normalizedBoundedMonomorphismArrows (D : Type w) [Category.{v} D]
    [Small.{u} D] [LocallySmall.{u} D] :
    ObjectProperty (Arrow (SimplicialPresheaf.{u} D)) := fun a =>
  Mono a.hom ∧
    Cardinal.mk ((normalizedTypePresheafEquivalence D).functor.mapArrow.obj a).left.Elements ≤
      max Cardinal.aleph0 (Cardinal.mk (Arrow (SmallModel.{u} D × SimplexCategory))) ∧
    Cardinal.mk ((normalizedTypePresheafEquivalence D).functor.mapArrow.obj a).right.Elements ≤
      max Cardinal.aleph0 (Cardinal.mk (Arrow (SmallModel.{u} D × SimplexCategory)))

private instance functor_monos_cobase {A : Type uC} [Category.{vC} A]
    {B : Type w} [Category.{v} B] [HasPullbacks B] [HasPushouts B]
    [(monomorphisms B).IsStableUnderCobaseChange] :
    (monomorphisms (A ⥤ B)).IsStableUnderCobaseChange := by
  rw [← MorphismProperty.functorCategory_monomorphisms (C := B) A]
  infer_instance

private instance functor_monos_transfinite {A : Type uC} [Category.{vC} A]
    {B : Type w} [Category.{v} B] [HasPullbacks B] [HasColimitsOfSize.{u, u} B]
    [IsStableUnderTransfiniteComposition.{u} (monomorphisms B)] :
    IsStableUnderTransfiniteComposition.{u} (monomorphisms (A ⥤ B)) where

private theorem bounded_of_arrow_iso {E : Type u} [SmallCategory E]
    {a b : Arrow (Eᵒᵖ ⥤ Type u)} (e : a ≅ b)
    (hb : CategoryTheory.Presheaf.boundedMonoArrows E b) :
    CategoryTheory.Presheaf.boundedMonoArrows E a := by
  let eL : a.left ≅ b.left := Arrow.leftFunc.mapIso e
  let eR : a.right ≅ b.right := Arrow.rightFunc.mapIso e
  exact ⟨((monomorphisms (Eᵒᵖ ⥤ Type u)).arrow_iso_iff e).2 hb.1,
    (CategoryTheory.Functor.mk_elements_le_of_mono eL.hom).trans hb.2.1,
    (CategoryTheory.Functor.mk_elements_le_of_mono eR.hom).trans hb.2.2⟩

private theorem along_to_bounded {E : Type u} [SmallCategory E]
    {C : Type uC} [Category.{vC} C] (e : C ≌ (Eᵒᵖ ⥤ Type u))
    (a : Arrow C) (ha : boundsAlong e a) :
    CategoryTheory.Presheaf.boundedMonoArrows E (e.functor.mapArrow.obj a) := by
  let _ : Mono a.hom := ha.1
  refine ⟨?_, ha.2⟩
  change Mono (e.functor.map a.hom)
  infer_instance

open scoped PresheafMonomorphismFiltration in
private theorem exists_generators_along {E : Type u} [SmallCategory E]
    {C : Type uC} [Category.{vC} C] [LocallySmall.{u} C]
    [HasColimitsOfSize.{u, u} C]
    [(monomorphisms C).IsStableUnderCobaseChange]
    [IsStableUnderCoproducts.{u} (monomorphisms C)]
    [IsStableUnderTransfiniteComposition.{u} (monomorphisms C)]
    (e : C ≌ (Eᵒᵖ ⥤ Type u)) :
    ∃ (K : Type u) (F : K → Arrow C) (κ : Cardinal.{u})
      (hκ : Fact κ.IsRegular) (hbot : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hbot
      max Cardinal.aleph0 (Cardinal.mk (Arrow E)) < κ ∧
        (∀ k, boundsAlong e (F k)) ∧
        (∀ a, boundsAlong e a → ∃ k, Nonempty (a ≅ F k)) ∧
        (∀ k, IsCardinalPresentable (F k).left κ ∧ IsCardinalPresentable (F k).right κ) ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).IsSmall.{u} ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).IsCardinalForSmallObjectArgument κ ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).HasSmallObjectArgument.{u} ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp.llp = monomorphisms C ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp = (monomorphisms C).rlp ∧
        IsWeakFactorizationSystem (monomorphisms C) (monomorphisms C).rlp ∧
        Nonempty (FunctorialFactorizationData (monomorphisms C) (monomorphisms C).rlp) := by
  obtain ⟨K, F₀, κ, hκ, hbot, hθ, hF₀, hcover₀, hends₀, _, _, _, _⟩ :=
    CategoryTheory.Presheaf.exists_bounded_mono_family E
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hbot
  let F : K → Arrow C := fun k => e.inverse.mapArrow.obj (F₀ k)
  let I := MorphismProperty.ofHoms (fun k => (F k).hom)
  let L := I.rlp.llp
  have hF (k : K) : boundsAlong e (F k) := by
    let _ : Mono (F₀ k).hom := (hF₀ k).1
    have hb : CategoryTheory.Presheaf.boundedMonoArrows E
        (e.functor.mapArrow.obj (F k)) :=
      bounded_of_arrow_iso ((Functor.mapArrowEquivalence e).counitIso.app (F₀ k)) (hF₀ k)
    refine ⟨?_, hb.2⟩
    change Mono (e.inverse.map (F₀ k).hom)
    infer_instance
  have hcover (a : Arrow C) (ha : boundsAlong e a) :
      ∃ k, Nonempty (a ≅ F k) := by
    obtain ⟨k, ⟨ei⟩⟩ := hcover₀ (e.functor.mapArrow.obj a) (along_to_bounded e a ha)
    exact ⟨k, ⟨(Functor.mapArrowEquivalence e).unitIso.app a ≪≫ e.inverse.mapArrow.mapIso ei⟩⟩
  have hends (k : K) : IsCardinalPresentable (F k).left κ ∧
      IsCardinalPresentable (F k).right κ := by
    let _ : IsCardinalPresentable (F₀ k).left κ := (hends₀ k).1
    let _ : IsCardinalPresentable (F₀ k).right κ := (hends₀ k).2
    exact ⟨isCardinalPresentable_of_equivalence (F₀ k).left κ e.symm,
      isCardinalPresentable_of_equivalence (F₀ k).right κ e.symm⟩
  let _ : I.IsSmall.{u} := inferInstance
  have heligible : I.IsCardinalForSmallObjectArgument κ :=
    { isSmall := inferInstance
      locallySmall := inferInstance
      hasPushouts := inferInstance
      hasCoproducts := inferInstance
      hasIterationOfShape := inferInstance
      preservesColimit := by
        intro A B X Y i hi p c
        change MorphismProperty.ofHoms (fun k => (F k).hom) i at hi
        cases hi with
        | mk k =>
          let _ : IsCardinalPresentable (F k).left κ := (hends k).1
          let _ : PreservesColimitsOfShape κ.ord.ToType (coyoneda.obj (op (F k).left)) :=
            preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
              (F k).left κ κ.ord.ToType
          infer_instance }
  let _ := heligible
  have hsoa : I.HasSmallObjectArgument.{u} := ⟨κ, inferInstance, inferInstance, heligible⟩
  have hcell : CategoryTheory.MorphismProperty.boundedPresheafMonomorphisms E ≤
      L.inverseImage e.inverse := by
    intro X Y i hi
    have hb : CategoryTheory.Presheaf.boundedMonoArrows E (Arrow.mk i) := hi
    obtain ⟨k, ⟨ei⟩⟩ := hcover₀ (Arrow.mk i) hb
    let ei' : Arrow.mk (e.inverse.map i) ≅ F k := e.inverse.mapArrow.mapIso ei
    have hk : L (F k).hom := I.le_llp_rlp _ (MorphismProperty.ofHoms.mk k)
    exact (L.arrow_iso_iff ei').2 hk
  have hpush : (CategoryTheory.MorphismProperty.boundedPresheafMonomorphisms E).pushouts ≤
      L.inverseImage e.inverse := by
    rintro X Y f ⟨A, B, i, a, b, hi, sq⟩
    exact L.of_isPushout (sq.map e.inverse) (hcell _ hi)
  have hforward : monomorphisms C ≤ L := by
    intro X Y f hf
    let _ : Mono f := hf
    let _ : Mono (e.functor.map f) := inferInstance
    let h := CategoryTheory.Subfunctor.presheafMonomorphismFiltration (e.functor.map f)
    let _ : PreservesWellOrderContinuousOfShape
        (Set.Iic (⊤ : CategoryTheory.Subfunctor.PresheafSectionIndex (e.functor.obj Y)))
        e.inverse := { preservesColimitsOfShape := fun _ _ => inferInstance }
    let hm := (h.ofLE hpush).map
    let ei : Arrow.mk (e.inverse.map (e.functor.map f)) ≅ Arrow.mk f :=
      Arrow.isoMk (e.unitIso.symm.app X) (e.unitIso.symm.app Y) (by
        simpa only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Iso.app_hom, Iso.symm_hom,
          Functor.comp_map, Functor.id_map] using (e.unitIso.inv.naturality f).symm)
    exact L.transfiniteCompositionsOfShape_le _ _ ⟨hm.ofArrowIso ei⟩
  have hI : I ≤ monomorphisms C := (MorphismProperty.ofHoms_le_iff _ _).2 (fun k => (hF k).1)
  have hreverse : L ≤ monomorphisms C := by
    change I.rlp.llp ≤ monomorphisms C
    rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument' I κ]
    have hc : MorphismProperty.coproducts.{u} I ≤ monomorphisms C :=
      (MorphismProperty.coproducts_monotone hI).trans (monomorphisms C).coproducts_le
    have hp : (MorphismProperty.coproducts.{u} I).pushouts ≤ monomorphisms C :=
      (MorphismProperty.pushouts_monotone hc).trans (monomorphisms C).pushouts_le
    have ht : (MorphismProperty.coproducts.{u} I).pushouts.transfiniteCompositionsOfShape
        κ.ord.ToType ≤ monomorphisms C :=
      (MorphismProperty.transfiniteCompositionsOfShape_monotone _ hp).trans
        ((monomorphisms C).transfiniteCompositionsOfShape_le _)
    exact (MorphismProperty.retracts_monotone ht).trans (monomorphisms C).retracts_le
  have heq : I.rlp.llp = monomorphisms C := le_antisymm hreverse hforward
  have hr : I.rlp = (monomorphisms C).rlp := by
    rw [← heq, I.rlp_llp_rlp]
  let data : FunctorialFactorizationData (monomorphisms C) (monomorphisms C).rlp :=
    (SmallObject.functorialFactorizationData I κ).ofLE heq.le hr.le
  let _ : HasFunctorialFactorization (monomorphisms C) (monomorphisms C).rlp := ⟨⟨data⟩⟩
  have hwfs : IsWeakFactorizationSystem (monomorphisms C) (monomorphisms C).rlp :=
    IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hp i hi)
  exact ⟨K, F, κ, hκ, hbot, hθ, hF, hcover, hends, inferInstance, heligible, hsoa,
    heq, hr, hwfs, ⟨data⟩⟩

/-- The complete literal-small-site package, with raw theta on the actual D × Delta site. -/
theorem exists_monomorphism_generators_raw (D : Type u) [SmallCategory D] :
    ∃ (K : Type u) (F : K → Arrow (SimplicialPresheaf.{u} D)) (κ : Cardinal.{u})
      (hκ : Fact κ.IsRegular) (hbot : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hbot
      max Cardinal.aleph0 (Cardinal.mk (Arrow (D × SimplexCategory))) < κ ∧
        (∀ k, boundedMonomorphismArrows D (F k)) ∧
        (∀ a, boundedMonomorphismArrows D a → ∃ k, Nonempty (a ≅ F k)) ∧
        (∀ k, IsCardinalPresentable (F k).left κ ∧ IsCardinalPresentable (F k).right κ) ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).IsSmall.{u} ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).IsCardinalForSmallObjectArgument κ ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).HasSmallObjectArgument.{u} ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp.llp =
          monomorphisms (SimplicialPresheaf.{u} D) ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp =
          (monomorphisms (SimplicialPresheaf.{u} D)).rlp ∧
        IsWeakFactorizationSystem (monomorphisms (SimplicialPresheaf.{u} D))
          (monomorphisms (SimplicialPresheaf.{u} D)).rlp ∧
        Nonempty (FunctorialFactorizationData (monomorphisms (SimplicialPresheaf.{u} D))
          (monomorphisms (SimplicialPresheaf.{u} D)).rlp) := by
  let _ : LocallySmall.{u} (SimplicialPresheaf.{u} D) := locallySmall (D := D)
  exact exists_generators_along (typePresheafEquivalence D)

/-- Every original small-on-objects/Homs site has the complete genuine generator, first-WFS
and functorial-factorization package in the fixed coefficient universe. Bounds are measured
on its actual normalized small site; original maps and both absolute endpoint ranks remain. -/
theorem exists_monomorphism_generators (D : Type w) [Category.{v} D]
    [Small.{u} D] [LocallySmall.{u} D] :
    ∃ (K : Type u) (F : K → Arrow (SimplicialPresheaf.{u} D)) (κ : Cardinal.{u})
      (hκ : Fact κ.IsRegular) (hbot : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hbot
      max Cardinal.aleph0 (Cardinal.mk (Arrow (SmallModel.{u} D × SimplexCategory))) < κ ∧
        (∀ k, normalizedBoundedMonomorphismArrows D (F k)) ∧
        (∀ a, normalizedBoundedMonomorphismArrows D a → ∃ k, Nonempty (a ≅ F k)) ∧
        (∀ k, IsCardinalPresentable (F k).left κ ∧ IsCardinalPresentable (F k).right κ) ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).IsSmall.{u} ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).IsCardinalForSmallObjectArgument κ ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).HasSmallObjectArgument.{u} ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp.llp =
          monomorphisms (SimplicialPresheaf.{u} D) ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp =
          (monomorphisms (SimplicialPresheaf.{u} D)).rlp ∧
        IsWeakFactorizationSystem (monomorphisms (SimplicialPresheaf.{u} D))
          (monomorphisms (SimplicialPresheaf.{u} D)).rlp ∧
        Nonempty (FunctorialFactorizationData (monomorphisms (SimplicialPresheaf.{u} D))
          (monomorphisms (SimplicialPresheaf.{u} D)).rlp) := by
  let _ : LocallySmall.{u} (SimplicialPresheaf.{u} D) := locallySmall (D := D)
  exact exists_generators_along (normalizedTypePresheafEquivalence D)

/-- The literal family tests the original whole-square lifting property, including empty indices. -/
theorem rlp_generator_family_iff (D : Type w) [Category.{v} D]
    {K : Type u} (F : K → Arrow (SimplicialPresheaf.{u} D))
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y) :
    (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp p ↔
      ∀ k, HasLiftingProperty (F k).hom p := by
  constructor
  · intro hp k
    exact hp _ (MorphismProperty.ofHoms.mk k)
  · intro hp A B i hi
    cases hi with
    | mk k => exact hp k

end SimplicialPresheaf
