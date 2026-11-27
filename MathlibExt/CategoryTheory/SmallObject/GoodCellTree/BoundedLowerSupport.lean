/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.OrderBounds
public import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Original bounded lower supports and their endpoint presentation

Bounded supports retain the original labels and inherited order. Their
actual unions prove cardinal filteredness. The original selected lower
colimits then give a native presentation of the same original endpoint.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w v u uI

namespace CategoryTheory.SmallObject.BoundedLowerSupport

open CategoryTheory.Limits LowerSetColimits

variable {P : Type w} [PartialOrder P] (κ : Cardinal.{w})

/-- The actual original lower supports of cardinal strictly below the given rank. -/
abbrev Carrier : Type w :=
  {B : LowerSet P // HasCardinalLT (B : Set P) κ}

/-- The same inherited-order inclusion, retaining every original support. -/
abbrev toLower : Carrier (P := P) κ ⥤ LowerSet P :=
  inclusion {B : LowerSet P | HasCardinalLT (B : Set P) κ}

@[simp]
theorem toLower_obj (B : Carrier (P := P) κ) : (toLower κ).obj B = B.1 := rfl

@[simp]
theorem toLower_map {B D : Carrier (P := P) κ} (f : B ⟶ D) :
    (toLower κ).map f = homOfLE (leOfHom f) := rfl

variable {C : Type u} [Category.{v} C] {Y : P ⥤ C}

/-- The given original lower-colimit functor restricted to these same bounded supports. -/
abbrev diagram (L : LowerSetColimitData Y) : Carrier (P := P) κ ⥤ C :=
  toLower κ ⋙ L.functor

@[simp]
theorem diagram_obj (L : LowerSetColimitData Y) (B : Carrier (P := P) κ) :
    (diagram κ L).obj B = L.obj B.1 := rfl

@[simp]
theorem diagram_map (L : LowerSetColimitData Y) {B D : Carrier (P := P) κ} (f : B ⟶ D) :
    (diagram κ L).map f = L.map (leOfHom f) := rfl

variable [Fact κ.IsRegular]

/-- The actual empty support is bounded at every regular rank. -/
def empty : Carrier (P := P) κ :=
  ⟨⊥, by
    change HasCardinalLT (∅ : Set P) κ
    exact hasCardinalLT_of_finite (∅ : Set P) κ (Fact.out : κ.IsRegular).aleph0_le⟩

/-- A binary union retains both actual original lower supports. -/
def union (B D : Carrier (P := P) κ) : Carrier (P := P) κ :=
  ⟨B.1 ⊔ D.1, hasCardinalLT_union (Fact.out : κ.IsRegular).aleph0_le B.2 D.2⟩

@[simp]
theorem union_val (B D : Carrier (P := P) κ) : (union κ B D).1 = B.1 ⊔ D.1 := rfl

theorem le_union_left (B D : Carrier (P := P) κ) : B ≤ union κ B D := by
  change B.1 ≤ B.1 ⊔ D.1
  exact le_sup_left

theorem le_union_right (B D : Carrier (P := P) κ) : D ≤ union κ B D := by
  change D.1 ≤ B.1 ⊔ D.1
  exact le_sup_right

/-- The actual union of a genuinely bounded family of original supports. -/
def indexedUnion {I : Type uI} (B : I → Carrier (P := P) κ)
    (hI : HasCardinalLT I κ) : Carrier (P := P) κ :=
  ⟨⨆ i, (B i).1, GoodOrderBounds.indexedUnionLt κ (fun i => (B i).1) hI (fun i => (B i).2)⟩

@[simp]
theorem indexedUnion_val {I : Type uI} (B : I → Carrier (P := P) κ)
    (hI : HasCardinalLT I κ) : (indexedUnion κ B hI).1 = ⨆ i, (B i).1 := rfl

/-- Each given source support maps to its original value in the actual bounded union. -/
theorem le_indexedUnion {I : Type uI} (B : I → Carrier (P := P) κ)
    (hI : HasCardinalLT I κ) (i : I) : B i ≤ indexedUnion κ B hI := by
  change (B i).1 ≤ ⨆ j, (B j).1
  exact le_iSup (fun j => (B j).1) i

/-- Genuine cardinal filteredness follows from actual unions of bounded families. -/
instance cardinalFiltered : IsCardinalFiltered (Carrier (P := P) κ) κ :=
  isCardinalFiltered_preorder (Carrier (P := P) κ) κ (fun {I} B hI => by
    have h : HasCardinalLT I κ := (hasCardinalLT_iff_cardinal_mk_lt I κ).2 hI
    exact ⟨indexedUnion κ B h, fun i => le_indexedUnion κ B h i⟩)

/-- The same bounded support category has its genuine ordinary filtered dictionary. -/
instance filtered : IsFiltered (Carrier (P := P) κ) :=
  isFiltered_of_isCardinalFiltered (Carrier (P := P) κ) κ

/-- The original principal support is bounded by the recorded strict-predecessor bound. -/
def principal (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ) (a : P) :
    Carrier (P := P) κ :=
  ⟨LowerSet.Iic a, GoodOrderBounds.principalLt κ hPred a⟩

/-- Every original label occurs in these bounded supports, even for an unbounded total index. -/
theorem covered (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ) :
    (⨆ B : Carrier (P := P) κ, B.1) = (⊤ : LowerSet P) := by
  ext a
  constructor
  · intro _
    trivial
  · intro _
    apply LowerSet.mem_iSup_iff.2
    exact ⟨principal κ hPred a, by change a ≤ a; exact le_refl a⟩

/-- Countable union is bounded with precisely the genuine uncountability premise. -/
def countableUnion (hκ : Cardinal.aleph0 < κ) (B : ℕ → Carrier (P := P) κ) :
    Carrier (P := P) κ :=
  indexedUnion κ B (GoodOrderBounds.natLt κ hκ)

@[simp]
theorem countableUnion_val (hκ : Cardinal.aleph0 < κ) (B : ℕ → Carrier (P := P) κ) :
    (countableUnion κ hκ B).1 = ⨆ n, (B n).1 := rfl

section Presentation

variable (L : LowerSetColimitData Y)

/-- The SAME original filtered-union colimit stored as a native presentation. -/
def unionPresentation :
    ColimitPresentation (Carrier (P := P) κ) (L.obj (⨆ B : Carrier (P := P) κ, B.1)) where
  diag := diagram κ L
  ι := (L.filteredCocone (toLower κ)).ι
  isColimit := L.isColimitFilteredCocone (B := toLower κ)

/-- Transport the given union presentation to its proved original full lower support. -/
def fullPresentation (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ) :
    ColimitPresentation (Carrier (P := P) κ) (L.obj ⊤) :=
  (unionPresentation κ L).ofIso (eqToIso (congrArg L.obj (covered κ hPred)))

@[simp]
theorem fullPresentation_diag (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ) :
    (fullPresentation κ L hPred).diag = diagram κ L := rfl

/-- The actual full-presentation leg is precisely the original selected lower map. -/
theorem fullPresentation_leg (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ)
    (B : Carrier (P := P) κ) : (fullPresentation κ L hPred).ι.app B = L.map (le_top : B.1 ≤ ⊤) := by
  change L.map (le_iSup (fun D : Carrier (P := P) κ => D.1) B) ≫
    eqToHom (congrArg L.obj (covered κ hPred)) = L.map (le_top : B.1 ≤ ⊤)
  have he : eqToHom (congrArg L.obj (covered κ hPred)) =
      L.map (leOfHom (eqToHom (covered κ hPred))) :=
    (eqToHom_map L.functor (covered κ hPred)).symm
  rw [he, L.map_comp]

/-- The whole full-presentation leg FUNCTION retains the original lower-map choices. -/
theorem fullPresentation_leg_function (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ) :
    (fun B : Carrier (P := P) κ => (fullPresentation κ L hPred).ι.app B) =
      (fun B : Carrier (P := P) κ => L.map (le_top : B.1 ≤ ⊤)) := by
  funext B
  exact fullPresentation_leg κ L hPred B

/-- Transport with the GIVEN original endpoint Iso using the same native presentation API. -/
def endpointPresentation (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ)
    {E : C} (γ : L.obj ⊤ ≅ E) : ColimitPresentation (Carrier (P := P) κ) E :=
  (fullPresentation κ L hPred).ofIso γ

@[simp]
theorem endpointPresentation_diag (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ)
    {E : C} (γ : L.obj ⊤ ≅ E) :
    (endpointPresentation κ L hPred γ).diag = diagram κ L := rfl

/-- Every original endpoint leg keeps its selected lower map and original endpoint function. -/
theorem endpointPresentation_leg (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ)
    {E : C} (γ : L.obj ⊤ ≅ E) (B : Carrier (P := P) κ) :
    (endpointPresentation κ L hPred γ).ι.app B =
      L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom := by
  change (fullPresentation κ L hPred).ι.app B ≫ γ.hom =
    L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom
  exact congrArg (fun p : L.obj B.1 ⟶ L.obj ⊤ => p ≫ γ.hom)
    (fullPresentation_leg κ L hPred B)

/-- The entire original endpoint leg FUNCTION is proved from the genuine leg equations. -/
theorem endpointPresentation_leg_function (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ)
    {E : C} (γ : L.obj ⊤ ≅ E) :
    (fun B : Carrier (P := P) κ => (endpointPresentation κ L hPred γ).ι.app B) =
      (fun B : Carrier (P := P) κ => L.map (le_top : B.1 ≤ ⊤) ≫ γ.hom) := by
  funext B
  exact endpointPresentation_leg κ L hPred γ B

end Presentation

end CategoryTheory.SmallObject.BoundedLowerSupport
