/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.MorphismProperty.BoundedPresheafMonomorphisms
public import MathlibExt.CategoryTheory.Presentable.CyclicPresheafSections
public import MathlibExt.CategoryTheory.Subfunctor.UnionPushout
public import MathlibExt.CategoryTheory.Subfunctor.TransfiniteUnion
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Order.WithBot
import Mathlib.Tactic.ScopedNS

/-!
# The original cyclic-section filtration of a presheaf monomorphism

Well-order the actual target elements and append a final sentinel. The native
strict-prefix construction starts at the original range. Every successor is
the literal cyclic intersection/union pushout, with both cell endpoints bounded
by the site arrows. The native transfinite witness is transported back to the
supplied monomorphism through its original range map and final inclusion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory.Limits

namespace CategoryTheory.Subfunctor

variable {E : Type u} [SmallCategory E]

/-- A chosen well-order of the literal total-section type. -/
@[instance_reducible, local instance]
def presheafElementsLinearOrder (B : Eᵒᵖ ⥤ Type u) : LinearOrder B.Elements :=
  Classical.choose (exists_wellFoundedLT B.Elements)

/-- The chosen order of original elements is well-founded. -/
@[local instance]
theorem presheafElementsWellFoundedLT (B : Eᵒᵖ ⥤ Type u) : WellFoundedLT B.Elements :=
  Classical.choose_spec (exists_wellFoundedLT B.Elements)

/-- The native successor operation of the chosen well-order. -/
@[instance_reducible, local instance]
def presheafElementsSuccOrder (B : Eᵒᵖ ⥤ Type u) : SuccOrder B.Elements :=
  SuccOrder.ofLinearWellFoundedLT B.Elements

/-- Original target elements with one actual final stage, in the same universe. -/
abbrev PresheafSectionIndex (B : Eᵒᵖ ⥤ Type u) : Type u := WithTop B.Elements

/-- Even an empty enumeration has a least stage: the extended index contains top. -/
@[instance_reducible, local instance]
def presheafSectionIndexOrderBot (B : Eᵒᵖ ⥤ Type u) :
    OrderBot (PresheafSectionIndex B) :=
  WellFoundedLT.toOrderBot (PresheafSectionIndex B)

/-- Every actual section gives its original cyclic image; the sentinel has no seed. -/
def presheafSectionSeed (B : Eᵒᵖ ⥤ Type u) : PresheafSectionIndex B → Subfunctor B
  | none => ⊥
  | some s => ofSection s.val

variable {A B : Eᵒᵖ ⥤ Type u}

/-- The original range and precisely the cyclic seeds strictly before this stage. -/
def presheafMonoPrefix (f : A ⟶ B) : PresheafSectionIndex B → Subfunctor B :=
  strictPrefixUnion (range f) (presheafSectionSeed B)

/-- Every original prefix includes into every later prefix. -/
theorem presheafMonoPrefix_mono (f : A ⟶ B) : Monotone (presheafMonoPrefix f) :=
  strictPrefixUnion_mono (range f) (presheafSectionSeed B)

/-- The least prefix is exactly the image of the supplied map. -/
theorem presheafMonoPrefix_bot (f : A ⟶ B) : presheafMonoPrefix f ⊥ = range f :=
  strictPrefixUnion_bot (range f) (presheafSectionSeed B)

/-- A genuine limit is the literal union of the original earlier prefixes. -/
theorem presheafMonoPrefix_limit (f : A ⟶ B) (j : PresheafSectionIndex B)
    (hj : Order.IsSuccLimit j) :
    presheafMonoPrefix f j = ⨆ k : Set.Iio j, presheafMonoPrefix f k.1 :=
  strictPrefixUnion_limit (range f) (presheafSectionSeed B) j hj

/-- A nonmaximum successor adds exactly its original seed to the earlier prefix. -/
theorem presheafMonoPrefix_succ (f : A ⟶ B) (j : PresheafSectionIndex B)
    (hj : ¬ IsMax j) :
    presheafMonoPrefix f (Order.succ j) =
      presheafMonoPrefix f j ⊔ presheafSectionSeed B j := by
  apply le_antisymm
  · apply sup_le
    · exact le_sup_left.trans le_sup_left
    · apply iSup_le
      rintro ⟨k, hk⟩
      rcases lt_or_eq_of_le ((Order.lt_succ_iff_of_not_isMax hj).mp hk) with hk | rfl
      · have hs : presheafSectionSeed B k ≤
            ⨆ t : Set.Iio j, presheafSectionSeed B t.1 :=
          le_iSup_of_le (⟨k, hk⟩ : Set.Iio j) le_rfl
        exact (hs.trans (show _ ≤ presheafMonoPrefix f j from le_sup_right)).trans
          le_sup_left
      · exact le_sup_right
  · apply sup_le
    · exact presheafMonoPrefix_mono f (Order.le_succ j)
    · have hs : presheafSectionSeed B j ≤
          ⨆ t : Set.Iio (Order.succ j), presheafSectionSeed B t.1 :=
        le_iSup_of_le (⟨j, Order.lt_succ_of_not_isMax hj⟩ : Set.Iio (Order.succ j)) le_rfl
      exact hs.trans le_sup_right

/-- The original seed belongs to its actual next prefix, including a last seed. -/
theorem presheafSectionSeed_le_succ (f : A ⟶ B) (j : PresheafSectionIndex B)
    (hj : ¬ IsMax j) :
    presheafSectionSeed B j ≤ presheafMonoPrefix f (Order.succ j) := by
  rw [presheafMonoPrefix_succ f j hj]
  exact le_sup_right

/-- The real final sentinel includes every original section of the target. -/
theorem presheafMonoPrefix_top (f : A ⟶ B) : presheafMonoPrefix f ⊤ = ⊤ := by
  apply top_unique
  intro a x _
  let s : B.Elements := Functor.elementsMk B a x
  have hs : presheafSectionSeed B (s : PresheafSectionIndex B) ≤
      ⨆ k : Set.Iio (⊤ : PresheafSectionIndex B), presheafSectionSeed B k.1 :=
    le_iSup_of_le
      (⟨(s : PresheafSectionIndex B), WithTop.coe_lt_top s⟩ :
        Set.Iio (⊤ : PresheafSectionIndex B)) le_rfl
  have h : presheafSectionSeed B (s : PresheafSectionIndex B) ≤
      presheafMonoPrefix f ⊤ := hs.trans le_sup_right
  exact h a (mem_ofSection_obj x)

/-- The final comparison is the original ambient inclusion, which is an iso. -/
instance presheafMonoPrefix_final_isIso (f : A ⟶ B) :
    IsIso (presheafMonoPrefix f ⊤).ι :=
  (eq_top_iff_isIso _).mp (presheafMonoPrefix_top f)

/-- The attaching cell is the original prefix/cyclic-image intersection inclusion. -/
def presheafMonoCell (f : A ⟶ B) (j : PresheafSectionIndex B) :
    Arrow (Eᵒᵖ ⥤ Type u) :=
  Arrow.mk (homOfLe (show presheafMonoPrefix f j ⊓ presheafSectionSeed B j ≤
    presheafSectionSeed B j from inf_le_right))

/-- Both endpoints of every genuine attaching cell have the explicit same site bound. -/
theorem presheafMonoCell_bounded (f : A ⟶ B) (j : PresheafSectionIndex B)
    (hj : ¬ IsMax j) :
    MorphismProperty.boundedPresheafMonomorphisms E (presheafMonoCell f j).hom := by
  simp only [MorphismProperty.boundedPresheafMonomorphisms, presheafMonoCell, Arrow.mk_left,
    Arrow.mk_right, Arrow.mk_hom]
  refine ⟨inferInstance, ?_⟩
  cases j with
  | none => exact (hj isMax_top).elim
  | some s => exact cyclicSectionArrow_bounds s.val (presheafMonoPrefix f (some s))

private theorem prefixEquality_hom_ι {U V : Subfunctor B} (h : U = V) :
    (eqToIso (congrArg (fun S : Subfunctor B => S.toFunctor) h)).hom ≫ V.ι = U.ι := by
  cases h
  simp

/-- Each original successor is the literal pushout of its actual cyclic cell. -/
theorem presheafMonoSuccessor_isPushout (f : A ⟶ B) (j : PresheafSectionIndex B)
    (hj : ¬ IsMax j) :
    IsPushout (presheafMonoCell f j).hom
      (homOfLe (show presheafMonoPrefix f j ⊓ presheafSectionSeed B j ≤
        presheafMonoPrefix f j from inf_le_left))
      (homOfLe (presheafSectionSeed_le_succ f j hj))
      (homOfLe (presheafMonoPrefix_mono f (Order.le_succ j))) := by
  simp only [presheafMonoCell, Arrow.mk_hom]
  let e : (presheafMonoPrefix f j ⊔ presheafSectionSeed B j).toFunctor ≅
      (presheafMonoPrefix f (Order.succ j)).toFunctor :=
    eqToIso (congrArg (fun S : Subfunctor B => S.toFunctor)
      (presheafMonoPrefix_succ f j hj).symm)
  have he : e.hom ≫ (presheafMonoPrefix f (Order.succ j)).ι =
      (presheafMonoPrefix f j ⊔ presheafSectionSeed B j).ι :=
    prefixEquality_hom_ι (presheafMonoPrefix_succ f j hj).symm
  apply (isPushout_inf_sup (presheafMonoPrefix f j) (presheafSectionSeed B j)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e
  · simp
  · simp
  · apply (cancel_mono (presheafMonoPrefix f (Order.succ j)).ι).mp
    simp only [Iso.refl_hom, Category.id_comp, Category.assoc, he, homOfLe_ι]
  · apply (cancel_mono (presheafMonoPrefix f (Order.succ j)).ι).mp
    simp only [Iso.refl_hom, Category.id_comp, Category.assoc, he, homOfLe_ι]

/-- Genuine step membership is derived from the bounded cell and its original square. -/
theorem presheafMonoSuccessor_mem_pushouts (f : A ⟶ B) (j : PresheafSectionIndex B)
    (hj : ¬ IsMax j) :
    (MorphismProperty.boundedPresheafMonomorphisms E).pushouts
      (homOfLe (presheafMonoPrefix_mono f (Order.le_succ j))) :=
  (MorphismProperty.boundedPresheafMonomorphisms E).pushouts_mk
    (presheafMonoSuccessor_isPushout f j hj).flip (presheafMonoCell_bounded f j hj)

/-- The complete original Arrow comparison uses the native range iso and final inclusion. -/
def presheafMonoPrefixArrowIso (f : A ⟶ B) [Mono f] :
    Arrow.mk (homOfLe (show range f ≤ presheafMonoPrefix f ⊤ from le_sup_left)) ≅
      Arrow.mk f := by
  refine Arrow.isoMk (asIso (toRange f)).symm
    (asIso (presheafMonoPrefix f ⊤).ι) ?_
  change inv (toRange f) ≫ f =
    homOfLe (show range f ≤ presheafMonoPrefix f ⊤ from le_sup_left) ≫
      (presheafMonoPrefix f ⊤).ι
  calc
    inv (toRange f) ≫ f = inv (toRange f) ≫ (toRange f ≫ (range f).ι) :=
      congrArg (fun k => inv (toRange f) ≫ k) (toRange_ι f).symm
    _ = (range f).ι := by simp
    _ = _ := (homOfLe_ι (show range f ≤ presheafMonoPrefix f ⊤ from le_sup_left)).symm

/-- The supplied Mono itself is a native transfinite composite of the bounded-cell pushouts.
The original diagram, all inclusions, limit cocones and factor equation are retained. -/
def presheafMonomorphismFiltration (f : A ⟶ B) [Mono f] :
    (MorphismProperty.boundedPresheafMonomorphisms E).pushouts.TransfiniteCompositionOfShape
      (Set.Iic (⊤ : PresheafSectionIndex B)) f :=
  (strictPrefixTransfinite (range f) (presheafSectionSeed B)
    (MorphismProperty.boundedPresheafMonomorphisms E).pushouts
    (presheafMonoSuccessor_mem_pushouts f) ⊤).ofArrowIso (presheafMonoPrefixArrowIso f)

end CategoryTheory.Subfunctor

/-! The filtration's chosen order is available only through an explicit scope.
The four public values also remain available to callers who want to name them. -/
scoped[PresheafMonomorphismFiltration] attribute [instance]
  CategoryTheory.Subfunctor.presheafElementsLinearOrder
  CategoryTheory.Subfunctor.presheafElementsWellFoundedLT
  CategoryTheory.Subfunctor.presheafElementsSuccOrder
  CategoryTheory.Subfunctor.presheafSectionIndexOrderBot
