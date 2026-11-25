/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.Data.Fin.Tuple.Basic
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorInterfaces
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.OrderedTensor
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.Fubini
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Small.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.Limits.Sifted
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive

/-!
# FiniteTensorColimits

Finite tensor colimits and diagonal finality for filtered and reflexive diagrams.
-/

/- Source proof segment: FiniteTupleCurrying -/
section source_FiniteTupleCurrying
/-!
# Currying a finite tuple functor at its last coordinate

The actual tuple functor appends one object and one component map.
Currying an arbitrary functor on finite tuples gives the tail and
last-coordinate slice functors used in separate-colimit descent.
-/

@[expose] public section

set_option autoImplicit false

universe vC uC vD uD

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- Append the component map in the last slot, with the exact
`Fin.snoc` object identifications. -/
def snocMap {n : ℕ} {X Y : Fin n → C} {x y : C}
    (f : X ⟶ Y) (g : x ⟶ y) (i : Fin (n + 1)) : Fin.snoc (α := fun _ =>
      C) X x i ⟶ Fin.snoc (α := fun _ => C) Y y i :=
      by
  cases i using Fin.lastCases with
  | last =>
    exact eqToHom (@Fin.snoc_last n (fun _ => C) x X) ≫ g ≫
      eqToHom (@Fin.snoc_last n (fun _ => C) y Y).symm
  | cast i =>
    exact eqToHom (@Fin.snoc_castSucc n (fun _ => C) x X i) ≫ f i ≫
      eqToHom (@Fin.snoc_castSucc n (fun _ => C) y Y i).symm

theorem snocMap_id {n : ℕ} (X : Fin n → C) (x : C) :
    snocMap (𝟙 X) (𝟙 x) = 𝟙 (Fin.snoc (α := fun _ => C) X x) := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [snocMap]
  | cast i => simp [snocMap]

theorem snocMap_comp {n : ℕ} {X Y Z : Fin n → C} {x y z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : x ⟶ y) (b : y ⟶ z) :
    snocMap (f ≫ g) (a ≫ b) = (fun i => snocMap f a i ≫ snocMap g b i) := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [snocMap, Category.assoc]
  | cast i => simp [snocMap, Category.assoc]

@[simp]
theorem snocMap_last {n : ℕ} {X Y : Fin n → C} {x y : C}
    (f : X ⟶ Y) (g : x ⟶ y) :
    HEq (snocMap f g (Fin.last n)) g := by
  simp [snocMap]

@[simp]
theorem snocMap_castSucc {n : ℕ} {X Y : Fin n → C} {x y : C}
    (f : X ⟶ Y) (g : x ⟶ y) (i : Fin n) :
    HEq (snocMap f g i.castSucc) (f i) := by
  simp [snocMap]

/-- Append the actual last object and last component morphism to
a finite tuple. -/
def snocFunctor (n : ℕ) :
    (Fin n → C) × C ⥤ (Fin (n + 1) → C) where
  obj p := Fin.snoc (α := fun _ => C) p.1 p.2
  map f := snocMap f.1 f.2
  map_id p := snocMap_id p.1 p.2
  map_comp f g := snocMap_comp f.1 g.1 f.2 g.2

/-- The curried finite tuple functor, with the original first `n`
coordinates and original last coordinate kept in their positions. -/
def curryLast {n : ℕ} (F : (Fin (n + 1) → C) ⥤ D) : (Fin n → C) ⥤ C ⥤ D :=
  Functor.curry.obj (snocFunctor (C := C) n ⋙ F)

@[simp]
theorem curryLast_obj {n : ℕ} (F : (Fin (n + 1) → C) ⥤ D)
    (X : Fin n → C) (Y : C) : ((curryLast F).obj X).obj Y = F.obj (Fin.snoc (α := fun _
      => C) X Y) :=
  rfl




end CategoryTheory.Limits.FiniteMultifunctor
end
end source_FiniteTupleCurrying

/- Source proof segment: FiniteTupleSlices -/
section source_FiniteTupleSlices
/-!
# Source one-slot preservation for curried finite tuple functors

Last-coordinate and tail-coordinate slices are compared with the
actual one-slot replacement functors. The preservation condition
is inherited from those original source slots, never from a joint
multifunctor colimit outcome.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe vC uC vD uD uS

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- The actual last-coordinate tuple slice. -/
def lastTupleSlice {n : ℕ} (A : Fin n → C) : C ⥤ (Fin (n + 1) → C) where
  obj X := Fin.snoc (α := fun _ => C) A X
  map f := snocMap (𝟙 A) f
  map_id X := snocMap_id A X
  map_comp f g := by
    change snocMap (𝟙 A) (f ≫ g) = (fun i => snocMap (𝟙 A) f i ≫ snocMap (𝟙 A) g i)
    have h := snocMap_comp (𝟙 A) (𝟙 A) f g
    simpa only [Category.id_comp] using h

/-- The actual tail tuple slice, retaining the original last object. -/
def tailTupleSlice (n : ℕ) (X : C) : (Fin n → C) ⥤ (Fin (n + 1) → C) where
  obj A := Fin.snoc (α := fun _ => C) A X
  map f := snocMap f (𝟙 X)
  map_id A := snocMap_id A X
  map_comp f g := by
    change snocMap (f ≫ g) (𝟙 X) = (fun i => snocMap f (𝟙 X) i ≫ snocMap g (𝟙 X) i)
    have h := snocMap_comp f g (𝟙 X) (𝟙 X)
    simpa only [Category.id_comp] using h

/-- Replacing the last entry of a snoc tuple gives the actual
last-coordinate slice as a functor, with its original maps. -/
theorem lastTupleSlice_eq {n : ℕ} (A : Fin n → C) (x : C) :
    Pi.replaceFunctor (Fin.snoc (α := fun _ => C) A x) (Fin.last n) = lastTupleSlice A := by
  apply Functor.hext
  · intro X
    exact @Fin.update_snoc_last n (fun _ => C) x A X
  · intro X Y f
    apply Function.hfunext rfl
    intro i i' hi
    have hidx : i = i' := eq_of_heq hi
    subst i'
    cases i using Fin.lastCases with
    | last =>
      exact (Pi.replaceMap_at _ _ f).trans (snocMap_last (𝟙 A) f).symm
    | cast i =>
      have hne : i.castSucc ≠ Fin.last n := Fin.castSucc_ne_last i
      have hId : HEq (𝟙 (Fin.snoc (α := fun _ => C) A x i.castSucc)) (𝟙 (A i)) := by
        rw [Fin.snoc_castSucc]
      exact (Pi.replaceMap_other _ _ _ hne f).trans
        (hId.trans (snocMap_castSucc (𝟙 A) f i).symm)

/-- Replacement in a tail slot is exactly replacement in its
original castSucc slot of the full tuple. -/
theorem tailTupleSlice_replace_eq {n : ℕ} (A : Fin n → C) (x : C) (i : Fin n) :
    Pi.replaceFunctor A i ⋙ tailTupleSlice n x =
      Pi.replaceFunctor (Fin.snoc (α := fun _ => C) A x) i.castSucc := by
  apply Functor.hext
  · intro X
    exact @Fin.snoc_update n (fun _ => C) x A i X
  · intro X Y f
    apply Function.hfunext rfl
    intro j j' hj
    have hidx : j = j' := eq_of_heq hj
    subst j'
    cases j using Fin.lastCases with
    | last =>
      have hne : Fin.last n ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
      have hId : HEq (𝟙 x) (𝟙 (Fin.snoc (α := fun _ => C) A x (Fin.last n))) := by
        rw [Fin.snoc_last]
      exact (snocMap_last (Pi.replaceMap A i f) (𝟙 x)).trans
        (hId.trans (Pi.replaceMap_other (Fin.snoc (α := fun _ => C) A x) _ _ hne f).symm)
    | cast j =>
      by_cases h : j = i
      · subst j
        exact (snocMap_castSucc (Pi.replaceMap A i f) (𝟙 x) i).trans
          ((Pi.replaceMap_at A i f).trans (Pi.replaceMap_at _ _ f).symm)
      · have hne : j.castSucc ≠ i.castSucc := fun he => h (Fin.castSucc_inj.mp he)
        have hId : HEq (𝟙 (A j)) (𝟙 (Fin.snoc (α := fun _ => C) A x j.castSucc)) := by
          rw [Fin.snoc_castSucc]
        exact (snocMap_castSucc (Pi.replaceMap A i f) (𝟙 x) j).trans
          ((Pi.replaceMap_other A i j h f).trans
            (hId.trans (Pi.replaceMap_other (Fin.snoc (α := fun _ => C) A x) _ _ hne f).symm))

/-- Currying followed by evaluation is the actual tail tuple slice
followed by the original multifunctor. -/
theorem curryLast_eval_eq {n : ℕ} (F : (Fin (n + 1) → C) ⥤ D) (x : C) :
    curryLast F ⋙ (evaluation C D).obj x = tailTupleSlice n x ⋙ F := by
  apply Functor.hext
  · intro A
    rfl
  · intro A B f
    exact HEq.rfl

/-- Each last-coordinate slice of the curried functor is the
original last tuple slice followed by the original multifunctor. -/
theorem curryLast_slice_eq {n : ℕ} (F : (Fin (n + 1) → C) ⥤ D) (A : Fin n → C) :
    (curryLast F).obj A = lastTupleSlice A ⋙ F := by
  apply Functor.hext
  · intro X
    rfl
  · intro X Y f
    exact HEq.rfl

/-- The source slot hypothesis gives small-colimit preservation by
every last-coordinate curried slice. -/
theorem curryLast_preserves_last {n : ℕ} (F : (Fin (n + 1) → C) ⥤ D)
    [Functor.PreservesColimitsInEachSlot.{0, uC, vC, uD, vD, uS} F]
    (A : Fin n → C) : PreservesColimitsOfSize.{uS, uS} ((curryLast F).obj A) := by
  constructor
  intro J hJ
  constructor
  intro K
  constructor
  intro c hc
  have hslot := Functor.PreservesColimitsInEachSlot.preserves
    (F := F) (Fin.snoc (α := fun _ => C) A c.pt) (Fin.last n)
  have hfun : Pi.replaceFunctor (Fin.snoc (α := fun _ => C) A c.pt) (Fin.last n) ⋙ F =
      (curryLast F).obj A := by
    rw [lastTupleSlice_eq, ← curryLast_slice_eq F A]
  let : PreservesColimitsOfSize.{uS, uS} ((curryLast F).obj A) :=
    hfun ▸ hslot
  exact ⟨isColimitOfPreserves ((curryLast F).obj A) hc⟩

/-- The source slot hypothesis is inherited by the tail multifunctor
with functor-category target, proved by evaluation in the last object. -/
instance curryLast_preserves_slots {n : ℕ} (F : (Fin (n + 1) → C) ⥤ D)
    [Functor.PreservesColimitsInEachSlot.{0, uC, vC, uD, vD, uS} F] :
    Functor.PreservesColimitsInEachSlot.{0, uC, vC, _, _, uS} (curryLast F) where
  preserves A i := by
    apply preservesColimits_of_evaluation
    intro x
    have hslot := Functor.PreservesColimitsInEachSlot.preserves
      (F := F) (Fin.snoc (α := fun _ => C) A x) i.castSucc
    have hfun : (Pi.replaceFunctor A i ⋙ curryLast F) ⋙ (evaluation C D).obj x =
        Pi.replaceFunctor (Fin.snoc (α := fun _ => C) A x) i.castSucc ⋙ F := by
      rw [Functor.assoc, curryLast_eval_eq, ← Functor.assoc, tailTupleSlice_replace_eq]
    rw [hfun]
    exact hslot

end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteTupleSlices

/- Source proof segment: FiniteProductTensor -/
section source_FiniteProductTensor
/-!
# Finite product tensor colimit cocones

Finite products of index categories are represented recursively:
the empty product is a singleton category and a successor product
is the previous product times the final index category. The tensor
diagram and tensor cocone use the original binary tensor, with the
original unit for the empty tensor.

Separate preservation of the required small colimits constructs
the universal property by iterated binary tensor colimit descent.
No siftedness is needed for this product-index construction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe vJ uJ vC uC

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory Limits CategoryTheory.Functor
open scoped MonoidalCategory.ExternalProduct

/-- The actual recursively represented product of finitely many
index types, including the singleton empty product. -/
def ProductIndex : {n : ℕ} → (Fin n → Type uJ) → Type uJ
  | 0, _ => PUnit
  | n + 1, J => ProductIndex (fun i : Fin n => J i.castSucc) × J (Fin.last n)

/-- Category structure on the finite product, built from the given
category structure in each slot. The morphism universe is independent
of the object universe, including in degree zero. -/
@[instance_reducible]
def productIndexCategory : {n : ℕ} → (J : Fin n → Type uJ) →
    (∀ i, Category.{vJ} (J i)) → Category.{vJ} (ProductIndex J)
  | 0, _, _ =>
    { Hom := fun _ _ => PUnit.{vJ + 1}
      id := fun _ => PUnit.unit
      comp := fun _ _ => PUnit.unit
      id_comp := by intros; exact Subsingleton.elim _ _
      comp_id := by intros; exact Subsingleton.elim _ _
      assoc := by intros; exact Subsingleton.elim _ _ }
  | n + 1, J, hJ => by
    letI : Category.{vJ} (ProductIndex (fun i : Fin n => J i.castSucc)) :=
      productIndexCategory (fun i : Fin n => J i.castSucc) (fun i => hJ i.castSucc)
    letI : Category.{vJ} (J (Fin.last n)) := hJ (Fin.last n)
    exact inferInstanceAs (Category.{vJ}
      (ProductIndex (fun i : Fin n => J i.castSucc) × J (Fin.last n)))

instance {n : ℕ} (J : Fin n → Type uJ) [∀ i, Category.{vJ} (J i)] :
    Category.{vJ} (ProductIndex J) :=
  productIndexCategory J (fun _ => inferInstance)

/-- The original object in every coordinate of a finite product
index; no colors or profile choices are discarded. -/
def coordinates : {n : ℕ} → {J : Fin n → Type uJ} →
    ProductIndex J → ∀ i, J i
  | 0, _, _, i => Fin.elim0 i
  | n + 1, _, p, i =>
    Fin.lastCases p.2 (fun i : Fin n => coordinates p.1 i) i

/-- Assemble a full tuple of original index objects as a finite
product index. -/
def indexOfCoordinates : {n : ℕ} → {J : Fin n → Type uJ} →
    (∀ i, J i) → ProductIndex J
  | 0, _, _ => PUnit.unit
  | n + 1, _, p =>
    (indexOfCoordinates (fun i : Fin n => p i.castSucc), p (Fin.last n))

theorem coordinates_indexOfCoordinates : ∀ {n : ℕ} {J : Fin n → Type uJ}
    (p : ∀ i, J i), coordinates (indexOfCoordinates p) = p
  | 0, _, _ => by funext i; exact Fin.elim0 i
  | n + 1, J, p => by
    funext i
    cases i using Fin.lastCases with
    | last => simp only [coordinates, indexOfCoordinates, Fin.lastCases_last]
    | cast i =>
      simpa only [coordinates, indexOfCoordinates, Fin.lastCases_castSucc] using
        congrFun (coordinates_indexOfCoordinates (fun i : Fin n => p i.castSucc)) i

theorem indexOfCoordinates_coordinates : ∀ {n : ℕ} {J : Fin n → Type uJ}
    (p : ProductIndex J), indexOfCoordinates (coordinates p) = p
  | 0, _, p => by cases p; rfl
  | n + 1, _, p => by
    rcases p with ⟨p, q⟩
    change
      (indexOfCoordinates (fun i : Fin n =>
        Fin.lastCases q (fun i : Fin n => coordinates p i) i.castSucc),
        Fin.lastCases q (fun i : Fin n => coordinates p i) (Fin.last n)) = (p, q)
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [indexOfCoordinates_coordinates]

/-- The recursively represented finite product retains exactly the
same tuples as the ordinary dependent product of index objects. -/
def productIndexEquiv {n : ℕ} (J : Fin n → Type uJ) :
    ProductIndex J ≃ (∀ i, J i) where
  toFun := coordinates
  invFun := indexOfCoordinates
  left_inv := indexOfCoordinates_coordinates
  right_inv := coordinates_indexOfCoordinates

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]

/-- The actual finite tensor diagram over a finite product of
independently varying index categories. -/
def productDiagram : {n : ℕ} → (J : Fin n → Type uJ) →
    [∀ i, Category.{vJ} (J i)] → (∀ i, J i ⥤ C) → ProductIndex J ⥤ C
  | 0, J, _, _ => (Functor.const (ProductIndex J)).obj (𝟙_ C)
  | n + 1, J, _, K =>
    productDiagram (fun i : Fin n => J i.castSucc) (fun i => K i.castSucc) ⊠ K (Fin.last n)

/-- The finite tensor cocone built by tensoring the original
injections of every independent factor diagram. -/
def productCocone : {n : ℕ} → {J : Fin n → Type uJ} →
    [∀ i, Category.{vJ} (J i)] → {K : ∀ i, J i ⥤ C} →
    (∀ i, Cocone (K i)) → Cocone (productDiagram J K)
  | 0, J, _, _, _ => constCocone (ProductIndex J) (𝟙_ C)
  | n + 1, _, _, _, c =>
    (curriedTensor C).mapCocone₂
      (productCocone (fun i : Fin n => c i.castSucc)) (c (Fin.last n))

variable [∀ c : C, PreservesColimitsOfSize.{vJ, uJ} (tensorRight c)]
  [∀ c : C, PreservesColimitsOfSize.{vJ, uJ} (tensorLeft c)]

/-- The canonical finite tensor cocone is a colimit cocone. The
proof constructs each successor colimit from separate preservation
and the preceding actual tensor colimit. -/
def isColimitProductCocone : {n : ℕ} → {J : Fin n → Type uJ} →
    [∀ i, Category.{vJ} (J i)] → {K : ∀ i, J i ⥤ C} →
    {c : ∀ i, Cocone (K i)} → (∀ i, IsColimit (c i)) →
    IsColimit (productCocone c)
  | 0, J, _, _, _, _ => by
    let : Nonempty (ProductIndex J) := ⟨PUnit.unit⟩
    let : Subsingleton (ProductIndex J) :=
      ⟨fun p q => by cases p; cases q; rfl⟩
    exact isColimitConstCocone (ProductIndex J) (𝟙_ C)
  | n + 1, _, _, _, _, h =>
    isColimitOfPreserves₂ (curriedTensor C)
      (isColimitProductCocone (fun i : Fin n => h i.castSucc)) (h (Fin.last n))

/-- Existence of every individual factor colimit constructs the
colimit of their finite tensor product diagram. -/
instance hasColimitProductDiagram {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] (K : ∀ i, J i ⥤ C) [∀ i, HasColimit (K i)] :
    HasColimit (productDiagram J K) :=
  ⟨⟨{
    cocone := productCocone (fun i => colimit.cocone (K i))
    isColimit := isColimitProductCocone (fun i => colimit.isColimit (K i))
  }⟩⟩

/-- The product-index tensor colimit identifies canonically with
the tensor cocone formed from the original factor colimits. -/
def productColimitIso {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] (K : ∀ i, J i ⥤ C) [∀ i, HasColimit (K i)] :
    colimit (productDiagram J K) ≅
      (productCocone (fun i => colimit.cocone (K i))).pt :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (productDiagram J K))
    (isColimitProductCocone (fun i => colimit.isColimit (K i)))

/-- On every full original tuple, the comparison is the injection
map of the actual tensor cocone. -/
@[reassoc (attr := simp)]
theorem productColimitIso_ι {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] (K : ∀ i, J i ⥤ C) [∀ i, HasColimit (K i)]
    (p : ProductIndex J) :
    colimit.ι (productDiagram J K) p ≫ (productColimitIso K).hom =
      (productCocone (fun i => colimit.cocone (K i))).ι.app p :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ p

/-- All original independent factor injection tuples determine
maps out of the finite tensor of their colimits. -/
theorem product_hom_ext {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] {K : ∀ i, J i ⥤ C} [∀ i, HasColimit (K i)]
    {Z : C} {f g : (productCocone (fun i => colimit.cocone (K i))).pt ⟶ Z}
    (h : ∀ p : ProductIndex J,
      (productCocone (fun i => colimit.cocone (K i))).ι.app p ≫ f =
        (productCocone (fun i => colimit.cocone (K i))).ι.app p ≫ g) : f = g :=
  (isColimitProductCocone (fun i => colimit.isColimit (K i))).hom_ext h






end CategoryTheory.MonoidalCategory.OrderedTensor
end
end
end source_FiniteProductTensor

/- Source proof segment: FiniteProductTensorSmall -/
section source_FiniteProductTensorSmall
/-!
# Tensor product colimits over essentially small finite products

Each index category may have a large presentation, while being
essentially small at the original source size. Its finite product
retains that same smallness bound. Tensor preservation is transported
along the actual small-model equivalence, so the product colimit
construction needs no larger ambient colimit universe.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe vJ uJ vC uC vD uD uS

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory Limits

/-- A finite product of essentially small categories has the same
smallness bound, including its singleton empty product. -/
theorem productIndexEssentiallySmall : {n : ℕ} → (J : Fin n → Type uJ) →
    [∀ i, Category.{vJ} (J i)] → [∀ i, EssentiallySmall.{uS} (J i)] →
    EssentiallySmall.{uS} (ProductIndex J)
  | 0, J, _, _ => by
    let : Subsingleton (ProductIndex J) := ⟨fun p q => by cases p; cases q; rfl⟩
    let : Small.{uS} (ProductIndex J) := inferInstance
    let : LocallySmall.{uS} (ProductIndex J) :=
      { hom_small _ _ := by
          change Small.{uS} PUnit.{vJ + 1}
          infer_instance }
    exact essentiallySmall_of_small_of_locallySmall (ProductIndex J)
  | n + 1, J, _, _ => by
    let : EssentiallySmall.{uS} (ProductIndex (fun i : Fin n => J i.castSucc)) :=
      productIndexEssentiallySmall (fun i : Fin n => J i.castSucc)
    exact EssentiallySmall.mk'
      (Equivalence.prod
        (equivSmallModel.{uS} (ProductIndex (fun i : Fin n => J i.castSucc)))
        (equivSmallModel.{uS} (J (Fin.last n))))

instance {n : ℕ} (J : Fin n → Type uJ) [∀ i, Category.{vJ} (J i)]
    [∀ i, EssentiallySmall.{uS} (J i)] : EssentiallySmall.{uS} (ProductIndex J) :=
  productIndexEssentiallySmall J

/-- Preservation of source-sized small colimits implies preservation
for an essentially small displayed shape, through its actual
small-model equivalence. -/
theorem preservesColimitsOfEssentiallySmall
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) [PreservesColimitsOfSize.{uS, uS} F]
    (J : Type uJ) [Category.{vJ} J] [EssentiallySmall.{uS} J] :
    PreservesColimitsOfShape J F :=
  preservesColimitsOfShape_of_equiv (equivSmallModel.{uS} J).symm F

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
variable [∀ c : C, PreservesColimitsOfSize.{uS, uS} (tensorRight c)]
  [∀ c : C, PreservesColimitsOfSize.{uS, uS} (tensorLeft c)]

/-- The actual finite product tensor cocone is constructed using
source-sized small tensor preservation. Large but essentially small
factor presentations do not enlarge the required source size. -/
def isColimitProductCoconeSmall : {n : ℕ} → {J : Fin n → Type uJ} →
    [∀ i, Category.{vJ} (J i)] → [∀ i, EssentiallySmall.{uS} (J i)] →
    {K : ∀ i, J i ⥤ C} → {c : ∀ i, Cocone (K i)} →
    (∀ i, IsColimit (c i)) → IsColimit (productCocone c)
  | 0, J, _, _, _, _, _ => by
    let : Nonempty (ProductIndex J) := ⟨PUnit.unit⟩
    let : Subsingleton (ProductIndex J) :=
      ⟨fun p q => by cases p; cases q; rfl⟩
    exact isColimitConstCocone (ProductIndex J) (𝟙_ C)
  | n + 1, J, _, _, _, _, h => by
    letI : ∀ d : C, PreservesColimitsOfShape
        (ProductIndex (fun i : Fin n => J i.castSucc)) (tensorRight d) :=
      fun d => preservesColimitsOfEssentiallySmall (tensorRight d)
        (ProductIndex (fun i : Fin n => J i.castSucc))
    letI : ∀ d : C, PreservesColimitsOfShape (J (Fin.last n)) (tensorLeft d) :=
      fun d => preservesColimitsOfEssentiallySmall (tensorLeft d) (J (Fin.last n))
    exact isColimitOfPreserves₂ (curriedTensor C)
      (isColimitProductCoconeSmall (fun i : Fin n => h i.castSucc)) (h (Fin.last n))

/-- The product tensor diagram has a colimit from the original
factor colimits and source-sized tensor preservation. -/
instance hasColimitProductDiagramSmall {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] [∀ i, EssentiallySmall.{uS} (J i)]
    (K : ∀ i, J i ⥤ C) [∀ i, HasColimit (K i)] :
    HasColimit (productDiagram J K) :=
  ⟨⟨{
    cocone := productCocone (fun i => colimit.cocone (K i))
    isColimit := isColimitProductCoconeSmall (fun i => colimit.isColimit (K i))
  }⟩⟩

/-- The source-sized comparison uses the original displayed factor
colimits and the actual finite product tensor cocone. -/
def productColimitIsoSmall {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] [∀ i, EssentiallySmall.{uS} (J i)]
    (K : ∀ i, J i ⥤ C) [∀ i, HasColimit (K i)] :
    colimit (productDiagram J K) ≅
      (productCocone (fun i => colimit.cocone (K i))).pt :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (productDiagram J K))
    (isColimitProductCoconeSmall (fun i => colimit.isColimit (K i)))

@[reassoc (attr := simp)]
theorem productColimitIsoSmall_ι {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] [∀ i, EssentiallySmall.{uS} (J i)]
    (K : ∀ i, J i ⥤ C) [∀ i, HasColimit (K i)] (p : ProductIndex J) :
    colimit.ι (productDiagram J K) p ≫ (productColimitIsoSmall K).hom =
      (productCocone (fun i => colimit.cocone (K i))).ι.app p :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ p

/-- The finite tensor of factor colimit points receives the unique
descent of a cocone on the original product tensor diagram. -/
def productDescSmall {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] [∀ i, EssentiallySmall.{uS} (J i)]
    {K : ∀ i, J i ⥤ C} {c : ∀ i, Cocone (K i)}
    (h : ∀ i, IsColimit (c i)) (s : Cocone (productDiagram J K)) :
    (productCocone c).pt ⟶ s.pt :=
  (isColimitProductCoconeSmall h).desc s

@[reassoc (attr := simp)]
theorem productDescSmall_ι {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] [∀ i, EssentiallySmall.{uS} (J i)]
    {K : ∀ i, J i ⥤ C} {c : ∀ i, Cocone (K i)}
    (h : ∀ i, IsColimit (c i)) (s : Cocone (productDiagram J K)) (p : ProductIndex J) :
    (productCocone c).ι.app p ≫ productDescSmall h s = s.ι.app p :=
  (isColimitProductCoconeSmall h).fac s p

/-- All original tuple injections determine maps from the tensor of
colimit points at the original smallness bound. -/
theorem productSmall_hom_ext {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] [∀ i, EssentiallySmall.{uS} (J i)]
    {K : ∀ i, J i ⥤ C} {c : ∀ i, Cocone (K i)} (hc : ∀ i, IsColimit (c i))
    {Z : C} {f g : (productCocone c).pt ⟶ Z}
    (h : ∀ p : ProductIndex J,
      (productCocone c).ι.app p ≫ f = (productCocone c).ι.app p ≫ g) : f = g :=
  (isColimitProductCoconeSmall hc).hom_ext h






end CategoryTheory.MonoidalCategory.OrderedTensor
end
end
end source_FiniteProductTensorSmall

/- Source proof segment: FiniteProductTensorCoordinateValues -/
section source_FiniteProductTensorCoordinateValues
@[expose] public section

set_option autoImplicit false

universe uJ

namespace CategoryTheory.MonoidalCategory.OrderedTensor

@[simp]
theorem coordinates_last {n : ℕ} {J : Fin (n + 1) → Type uJ} (p : ProductIndex J) :
    coordinates p (Fin.last n) = p.2 := by
  simp only [coordinates, Fin.lastCases_last]

@[simp]
theorem coordinates_castSucc {n : ℕ} {J : Fin (n + 1) → Type uJ}
    (p : ProductIndex J) (i : Fin n) : coordinates p i.castSucc = coordinates p.1 i := by
  simp only [coordinates, Fin.lastCases_castSucc]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteProductTensorCoordinateValues

/- Source proof segment: FiniteProductTensorCoordinates -/
section source_FiniteProductTensorCoordinates
/-!
# Full tuple coordinates for finite tensor product index categories

The recursively represented finite product and the ordinary tuple
category are equivalent through every original coordinate object
and coordinate morphism. The coordinate maps have explicit inverse
maps, identity and composition equations, including the empty product.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe vJ uJ

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

/-- Every original coordinate morphism of a finite product map. -/
def coordinatesMap : {n : ℕ} → {J : Fin n → Type uJ} →
    [∀ i, Category.{vJ} (J i)] → {p q : ProductIndex J} →
    (p ⟶ q) → (∀ i, coordinates p i ⟶ coordinates q i)
  | 0, _, _, _, _, _, i => Fin.elim0 i
  | n + 1, _, _, p, q, f, i => by
    cases i using Fin.lastCases with
    | last =>
      exact eqToHom (coordinates_last p) ≫ f.2 ≫ eqToHom (coordinates_last q).symm
    | cast i =>
      exact eqToHom (coordinates_castSucc p i) ≫ coordinatesMap f.1 i ≫
        eqToHom (coordinates_castSucc q i).symm

/-- Reconstruct a finite product map from all its original
coordinate morphisms. -/
def mapOfCoordinates : {n : ℕ} → {J : Fin n → Type uJ} →
    [∀ i, Category.{vJ} (J i)] → {p q : ProductIndex J} →
    (∀ i, coordinates p i ⟶ coordinates q i) → (p ⟶ q)
  | 0, _, _, _, _, _ => PUnit.unit
  | n + 1, _, _, p, q, f => by
    have h : ∀ i : Fin n, coordinates p.1 i ⟶ coordinates q.1 i :=
      fun i => eqToHom (coordinates_castSucc p i).symm ≫ f i.castSucc ≫
        eqToHom (coordinates_castSucc q i)
    have k : p.2 ⟶ q.2 := by
      exact eqToHom (coordinates_last p).symm ≫ f (Fin.last n) ≫ eqToHom (coordinates_last q)
    exact (mapOfCoordinates h, k)

theorem coordinatesMap_id : ∀ {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] (p : ProductIndex J),
    coordinatesMap (𝟙 p) = (fun i => 𝟙 (coordinates p i))
  | 0, _, _, _ => by funext i; exact Fin.elim0 i
  | n + 1, _, _, p => by
    funext i
    cases i using Fin.lastCases with
    | last =>
      simp only [coordinatesMap, Fin.lastCases_last]
      change eqToHom (coordinates_last p) ≫ 𝟙 p.2 ≫
        eqToHom (coordinates_last p).symm = 𝟙 (coordinates p (Fin.last n))
      simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
    | cast i =>
      simp only [coordinatesMap, Fin.lastCases_castSucc]
      change eqToHom (coordinates_castSucc p i) ≫ coordinatesMap (𝟙 p.1) i ≫
        eqToHom (coordinates_castSucc p i).symm = 𝟙 (coordinates p i.castSucc)
      rw [congrFun (coordinatesMap_id p.1) i]
      simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]

theorem coordinatesMap_comp : ∀ {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] {p q r : ProductIndex J} (f : p ⟶ q) (g : q ⟶ r),
    coordinatesMap (f ≫ g) = (fun i => coordinatesMap f i ≫ coordinatesMap g i)
  | 0, _, _, _, _, _, _, _ => by funext i; exact Fin.elim0 i
  | n + 1, _, _, p, q, r, f, g => by
    funext i
    cases i using Fin.lastCases with
    | last =>
      simp only [coordinatesMap, Fin.lastCases_last]
      change eqToHom (coordinates_last p) ≫ (f.2 ≫ g.2) ≫ eqToHom (coordinates_last r).symm =
        (eqToHom (coordinates_last p) ≫ f.2 ≫ eqToHom (coordinates_last q).symm) ≫
          (eqToHom (coordinates_last q) ≫ g.2 ≫ eqToHom (coordinates_last r).symm)
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    | cast i =>
      simp only [coordinatesMap, Fin.lastCases_castSucc]
      change eqToHom (coordinates_castSucc p i) ≫ coordinatesMap (f.1 ≫ g.1) i ≫
          eqToHom (coordinates_castSucc r i).symm =
        (eqToHom (coordinates_castSucc p i) ≫ coordinatesMap f.1 i ≫
          eqToHom (coordinates_castSucc q i).symm) ≫
            (eqToHom (coordinates_castSucc q i) ≫ coordinatesMap g.1 i ≫
              eqToHom (coordinates_castSucc r i).symm)
      rw [congrFun (coordinatesMap_comp f.1 g.1) i]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

theorem coordinatesMap_mapOfCoordinates : ∀ {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] {p q : ProductIndex J}
    (f : ∀ i, coordinates p i ⟶ coordinates q i),
    coordinatesMap (mapOfCoordinates f) = f
  | 0, _, _, _, _, _ => by funext i; exact Fin.elim0 i
  | n + 1, _, _, p, q, f => by
    funext i
    cases i using Fin.lastCases with
    | last => simp [coordinatesMap, mapOfCoordinates]
    | cast i =>
      let f' : ∀ i : Fin n, coordinates p.1 i ⟶ coordinates q.1 i :=
        fun i => eqToHom (coordinates_castSucc p i).symm ≫ f i.castSucc ≫
          eqToHom (coordinates_castSucc q i)
      simp only [coordinatesMap, mapOfCoordinates, Fin.lastCases_castSucc]
      change eqToHom (coordinates_castSucc p i) ≫ coordinatesMap (mapOfCoordinates f') i ≫
        eqToHom (coordinates_castSucc q i).symm = f i.castSucc
      rw [congrFun (coordinatesMap_mapOfCoordinates f') i]
      dsimp only [f']
      simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, Category.comp_id]

theorem mapOfCoordinates_coordinatesMap : ∀ {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] {p q : ProductIndex J} (f : p ⟶ q),
    mapOfCoordinates (coordinatesMap f) = f
  | 0, _, _, _, _, f => by cases f; rfl
  | n + 1, _, _, _, _, f => by
    apply CategoryTheory.Prod.hom_ext
    · simpa [coordinatesMap, mapOfCoordinates] using
        mapOfCoordinates_coordinatesMap f.1
    · simp [coordinatesMap, mapOfCoordinates]

/-- The coordinate functor retains every original object and map. -/
def coordinatesFunctor {n : ℕ} (J : Fin n → Type uJ) [∀ i, Category.{vJ} (J i)] :
    ProductIndex J ⥤ (∀ i, J i) where
  obj := coordinates
  map := coordinatesMap
  map_id := coordinatesMap_id
  map_comp := coordinatesMap_comp

instance coordinatesFunctorFull {n : ℕ} (J : Fin n → Type uJ) [∀ i, Category.{vJ} (J i)] :
    (coordinatesFunctor J).Full where
  map_surjective f := ⟨mapOfCoordinates f, coordinatesMap_mapOfCoordinates f⟩

instance coordinatesFunctorFaithful {n : ℕ} (J : Fin n → Type uJ)
    [∀ i, Category.{vJ} (J i)] : (coordinatesFunctor J).Faithful where
  map_injective {_ _} f g h :=
    (mapOfCoordinates_coordinatesMap f).symm.trans
      ((congrArg (fun f => mapOfCoordinates f) h).trans (mapOfCoordinates_coordinatesMap g))

instance coordinatesFunctorEssSurj {n : ℕ} (J : Fin n → Type uJ)
    [∀ i, Category.{vJ} (J i)] : (coordinatesFunctor J).EssSurj where
  mem_essImage p :=
    ⟨indexOfCoordinates p, ⟨eqToIso (coordinates_indexOfCoordinates p)⟩⟩

instance coordinatesFunctorIsEquivalence {n : ℕ} (J : Fin n → Type uJ)
    [∀ i, Category.{vJ} (J i)] : (coordinatesFunctor J).IsEquivalence where

/-- The full finite product category is equivalent to the ordinary
tuple category through its actual coordinate object and morphism maps. -/
def productIndexPiEquivalence {n : ℕ} (J : Fin n → Type uJ)
    [∀ i, Category.{vJ} (J i)] : ProductIndex J ≌ (∀ i, J i) :=
  (coordinatesFunctor J).asEquivalence




end CategoryTheory.MonoidalCategory.OrderedTensor
end
end
end source_FiniteProductTensorCoordinates

/- Source proof segment: FiniteMultifunctorDiagram -/
section source_FiniteMultifunctorDiagram
/-!
# The actual finite multifunctor diagram and operation cocone

For an arbitrary functor on finite tuples, the product diagram
retains every original input object and component map. The cocone
maps are obtained by applying the original functor to the tuple of
original input injections. No preservation or colimit outcome is
used to define this data.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe vJ uJ vC uC vD uD

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory
open CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- The actual tuple of independently varying input diagram values. -/
def tupleDiagram {n : ℕ} {J : Fin n → Type uJ} [∀ i, Category.{vJ} (J i)]
    (K : ∀ i, J i ⥤ C) : ProductIndex J ⥤ (Fin n → C) :=
  coordinatesFunctor J ⋙ Functor.pi K

/-- Apply the original finite multifunctor to the actual original
input tuple diagram. -/
def diagram {n : ℕ} {J : Fin n → Type uJ} [∀ i, Category.{vJ} (J i)]
    (F : (Fin n → C) ⥤ D) (K : ∀ i, J i ⥤ C) : ProductIndex J ⥤ D :=
  tupleDiagram K ⋙ F

/-- The original tuple of factor cocone points and injection maps. -/
def tupleCocone {n : ℕ} {J : Fin n → Type uJ} [∀ i, Category.{vJ} (J i)]
    {K : ∀ i, J i ⥤ C} (c : ∀ i, Cocone (K i)) : Cocone (tupleDiagram K) where
  pt i := (c i).pt
  ι :=
    { app p i := (c i).ι.app (coordinates p i)
      naturality p q f := by
        funext i
        change (K i).map (coordinatesMap f i) ≫ (c i).ι.app (coordinates q i) =
          (c i).ι.app (coordinates p i) ≫ 𝟙 ((c i).pt)
        exact ((c i).w (coordinatesMap f i)).trans (Category.comp_id _).symm }

/-- The concrete operation cocone has point `F(c_i)` and maps
`F` applied to the actual tuple of original factor injections. -/
def cocone {n : ℕ} {J : Fin n → Type uJ} [∀ i, Category.{vJ} (J i)]
    (F : (Fin n → C) ⥤ D) {K : ∀ i, J i ⥤ C} (c : ∀ i, Cocone (K i)) :
    Cocone (diagram F K) :=
  F.mapCocone (tupleCocone c)

@[simp]
theorem cocone_pt {n : ℕ} {J : Fin n → Type uJ} [∀ i, Category.{vJ} (J i)]
    (F : (Fin n → C) ⥤ D) {K : ∀ i, J i ⥤ C} (c : ∀ i, Cocone (K i)) :
    (cocone F c).pt = F.obj (fun i => (c i).pt) :=
  rfl

@[simp]
theorem cocone_ι {n : ℕ} {J : Fin n → Type uJ} [∀ i, Category.{vJ} (J i)]
    (F : (Fin n → C) ⥤ D) {K : ∀ i, J i ⥤ C} (c : ∀ i, Cocone (K i))
    (p : ProductIndex J) :
    (cocone F c).ι.app p = F.map (fun i => (c i).ι.app (coordinates p i)) :=
  rfl





end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteMultifunctorDiagram

/- Source proof segment: FiniteMultifunctorSplit -/
section source_FiniteMultifunctorSplit
/-!
# Exact last-coordinate decomposition of the original input tuple diagram
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe vJ uJ vC uC vD uD

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory
open CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

private theorem map_heq {E : Type*} [Category* E] {T : Type*} [Category* T]
    {A B A' B' : E} (F : E ⥤ T)
    (hA : A = A') (hB : B = B') {f : A ⟶ B} {g : A' ⟶ B'}
    (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hA
  cases hB
  cases h
  rfl

theorem coordinatesMap_last_heq {n : ℕ} {J : Fin (n + 1) → Type uJ}
    [∀ i, Category.{vJ} (J i)] {p q : ProductIndex J} (f : p ⟶ q) :
    HEq (coordinatesMap f (Fin.last n)) f.2 := by
  simp only [coordinatesMap, Fin.lastCases_last]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

theorem coordinatesMap_castSucc_heq {n : ℕ} {J : Fin (n + 1) → Type uJ}
    [∀ i, Category.{vJ} (J i)] {p q : ProductIndex J} (f : p ⟶ q) (i : Fin n) :
    HEq (coordinatesMap f i.castSucc) (coordinatesMap f.1 i) := by
  simp only [coordinatesMap, Fin.lastCases_castSucc]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

/-- The split tuple diagram uses the original tail tuple and last
factor through the original snoc functor. -/
def splitTupleDiagram {n : ℕ} {J : Fin (n + 1) → Type uJ}
    [∀ i, Category.{vJ} (J i)] (K : ∀ i, J i ⥤ C) : ProductIndex J ⥤ (Fin (n + 1) → C) :=
  (tupleDiagram (fun i : Fin n => K i.castSucc)).prod (K (Fin.last n)) ⋙ snocFunctor n

theorem splitTupleDiagram_obj {n : ℕ} {J : Fin (n + 1) → Type uJ}
    [∀ i, Category.{vJ} (J i)] (K : ∀ i, J i ⥤ C) (p : ProductIndex J) :
    (splitTupleDiagram K).obj p = (tupleDiagram K).obj p := by
  funext i
  cases i using Fin.lastCases with
  | last =>
    change Fin.snoc (α := fun _ => C)
      (fun i : Fin n => (K i.castSucc).obj (coordinates p.1 i))
      ((K (Fin.last n)).obj p.2) (Fin.last n) =
        (K (Fin.last n)).obj (coordinates p (Fin.last n))
    rw [Fin.snoc_last, coordinates_last]
  | cast i =>
    change Fin.snoc (α := fun _ => C)
      (fun i : Fin n => (K i.castSucc).obj (coordinates p.1 i))
      ((K (Fin.last n)).obj p.2) i.castSucc =
        (K i.castSucc).obj (coordinates p i.castSucc)
    rw [Fin.snoc_castSucc, coordinates_castSucc]

theorem splitTupleDiagram_map_heq {n : ℕ} {J : Fin (n + 1) → Type uJ}
    [∀ i, Category.{vJ} (J i)] (K : ∀ i, J i ⥤ C)
    {p q : ProductIndex J} (f : p ⟶ q) :
    HEq ((splitTupleDiagram K).map f) ((tupleDiagram K).map f) := by
  apply Function.hfunext rfl
  intro i i' hi
  have hidx : i = i' := eq_of_heq hi
  subst i'
  cases i using Fin.lastCases with
  | last =>
    have hsnoc := snocMap_last
      ((tupleDiagram (fun i : Fin n => K i.castSucc)).map f.1)
      ((K (Fin.last n)).map f.2)
    have hcoord := map_heq (K (Fin.last n)) (coordinates_last p) (coordinates_last q)
      (coordinatesMap_last_heq f)
    exact hsnoc.trans hcoord.symm
  | cast i =>
    have hsnoc := snocMap_castSucc
      ((tupleDiagram (fun i : Fin n => K i.castSucc)).map f.1)
      ((K (Fin.last n)).map f.2) i
    have hcoord := map_heq (K i.castSucc) (coordinates_castSucc p i) (coordinates_castSucc q i)
      (coordinatesMap_castSucc_heq f i)
    exact hsnoc.trans hcoord.symm

/-- The split and original tuple diagrams agree on all original
objects and maps; no chosen tuple is removed. -/
def splitTupleDiagramIso {n : ℕ} {J : Fin (n + 1) → Type uJ}
    [∀ i, Category.{vJ} (J i)] (K : ∀ i, J i ⥤ C) :
    splitTupleDiagram K ≅ tupleDiagram K :=
  NatIso.ofComponents (fun p => eqToIso (splitTupleDiagram_obj K p)) (by
    intro p q f
    have h := (conj_eqToHom_iff_heq _ _ (splitTupleDiagram_obj K p)
      (splitTupleDiagram_obj K q)).mpr (splitTupleDiagram_map_heq K f)
    exact (congrArg (· ≫ eqToHom (splitTupleDiagram_obj K q)) h).trans
      (by simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl,
        Category.comp_id]))

/-- After swapping the last and tail product indices, evaluation of
the curried original multifunctor is the original tuple diagram. -/
def curriedProductDiagramIso {n : ℕ} {J : Fin (n + 1) → Type uJ}
    [∀ i, Category.{vJ} (J i)] (F : (Fin (n + 1) → C) ⥤ D)
    (K : ∀ i, J i ⥤ C) :
    Prod.swap _ _ ⋙ Functor.uncurry.obj
        (K (Fin.last n) ⋙ (diagram (curryLast F) (fun i : Fin n => K i.castSucc)).flip) ≅
      diagram F K := by
  let E := Functor.isoWhiskerRight (splitTupleDiagramIso K) F
  exact NatIso.ofComponents
    (F := Prod.swap _ _ ⋙ Functor.uncurry.obj
      (K (Fin.last n) ⋙ (diagram (curryLast F) (fun i : Fin n => K i.castSucc)).flip))
    (G := diagram F K) (fun p => E.app p) (by
      intro p q f
      have h := E.hom.naturality f
      dsimp [diagram, tupleDiagram, curryLast, snocFunctor, Functor.curryObj,
        Functor.uncurry, E] at h ⊢
      let a := ((tupleDiagram (fun i : Fin n => K i.castSucc)).map f.1)
      let b := (K (Fin.last n)).map f.2
      let l : (splitTupleDiagram K).obj p ⟶
          Fin.snoc (α := fun _ => C) ((tupleDiagram (fun i : Fin n => K i.castSucc)).obj p.1)
            ((K (Fin.last n)).obj q.2) :=
        snocMap (𝟙 ((tupleDiagram (fun i : Fin n => K i.castSucc)).obj p.1)) b
      let r : Fin.snoc (α := fun _ => C) ((tupleDiagram (fun i : Fin n => K i.castSucc)).obj p.1)
          ((K (Fin.last n)).obj q.2) ⟶ (splitTupleDiagram K).obj q :=
        snocMap a (𝟙 ((K (Fin.last n)).obj q.2))
      let m : (splitTupleDiagram K).obj p ⟶ (splitTupleDiagram K).obj q := snocMap a b
      have hm : l ≫ r = m := by
        change (fun i => snocMap (𝟙 _) b i ≫ snocMap a (𝟙 _) i) = snocMap a b
        have hc := snocMap_comp (𝟙 _) a b (𝟙 _)
        simpa only [Category.id_comp, Category.comp_id] using hc.symm
      have hFm : F.map l ≫ F.map r = F.map m :=
        (F.map_comp l r).symm.trans (congrArg F.map hm)
      exact (congrArg (· ≫ E.hom.app q) hFm).trans h)

theorem curriedProductDiagramIso_hom {n : ℕ} {J : Fin (n + 1) → Type uJ}
    [∀ i, Category.{vJ} (J i)] (F : (Fin (n + 1) → C) ⥤ D)
    (K : ∀ i, J i ⥤ C) (p : ProductIndex J) :
    (curriedProductDiagramIso F K).hom.app p =
      eqToHom (congrArg F.obj (splitTupleDiagram_obj K p)) := by
  dsimp [curriedProductDiagramIso, splitTupleDiagramIso, NatIso.ofComponents, Iso.app,
    Functor.isoWhiskerRight, Functor.mapIso, Functor.whiskeringRight, Functor.whiskerRight]
  exact eqToHom_map F (splitTupleDiagram_obj K p)

end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteMultifunctorSplit

/- Source proof segment: FiniteTupleInjection -/
section source_FiniteTupleInjection
/-!
# Original injection tuples under last-coordinate decomposition
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe vJ uJ vC uC

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory
open CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type uC} [Category.{vC} C]

theorem snocInjection_heq {n : ℕ} {J : Fin (n + 1) → Type uJ}
    [∀ i, Category.{vJ} (J i)] {K : ∀ i, J i ⥤ C}
    (c : ∀ i, Cocone (K i)) (p : ProductIndex J) :
    HEq (snocMap (fun i : Fin n => (c i.castSucc).ι.app (coordinates p.1 i))
      ((c (Fin.last n)).ι.app p.2))
      (fun i => (c i).ι.app (coordinates p i)) := by
  apply Function.hfunext rfl
  intro i i' hi
  have hidx : i = i' := eq_of_heq hi
  subst i'
  cases i using Fin.lastCases with
  | last =>
    have h := snocMap_last (fun i : Fin n => (c i.castSucc).ι.app (coordinates p.1 i))
      ((c (Fin.last n)).ι.app p.2)
    have he := (coordinates_last p).symm
    have hi : HEq ((c (Fin.last n)).ι.app p.2)
        ((c (Fin.last n)).ι.app (coordinates p (Fin.last n))) :=
      he.rec (HEq.refl ((c (Fin.last n)).ι.app p.2))
    exact h.trans hi
  | cast i =>
    have h := snocMap_castSucc (fun i : Fin n => (c i.castSucc).ι.app (coordinates p.1 i))
      ((c (Fin.last n)).ι.app p.2) i
    have he := (coordinates_castSucc p i).symm
    have hi : HEq ((c i.castSucc).ι.app (coordinates p.1 i))
        ((c i.castSucc).ι.app (coordinates p i.castSucc)) :=
      he.rec (HEq.refl ((c i.castSucc).ι.app (coordinates p.1 i)))
    exact h.trans hi

end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteTupleInjection

/- Source proof segment: EvaluationFubini -/
section source_EvaluationFubini
/-!
# Fubini for actual evaluated cocones

A functor-valued cocone is combined with an input cocone using the
actual evaluation maps. Pointwise colimits and preservation by its
actual cocone-point functor construct the product colimit.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe vJ uJ vK uK vC uC vD uD

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory CategoryTheory.Functor

variable {J : Type uJ} [Category.{vJ} J]
variable {K : Type uK} [Category.{vK} K]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- The actual evaluated product cocone. -/
def evaluatedCocone {T : J ⥤ C ⥤ D} {X : K ⥤ C}
    (t : Cocone T) (c : Cocone X) :
    Cocone (uncurry.obj (X ⋙ T.flip)) where
  pt := t.pt.obj c.pt
  ι :=
    { app p := (T.obj p.2).map (c.ι.app p.1) ≫ (t.ι.app p.2).app c.pt
      naturality := by
        intro p q f
        dsimp
        rw [Category.assoc, NatTrans.naturality_assoc, ← Functor.map_comp_assoc, c.w f.1]
        rw [← NatTrans.naturality_assoc]
        have h := congr_app (t.w f.2) c.pt
        simpa only [Category.comp_id, Category.assoc, NatTrans.comp_app] using
          congrArg ((T.obj p.2).map (c.ι.app p.1) ≫ ·) h }

/-- Pointwise actual colimits and the actual cocone-point functor's
preservation construct the evaluated product colimit. -/
def isColimitEvaluatedCocone {T : J ⥤ C ⥤ D} {X : K ⥤ C}
    {t : Cocone T} (ht : ∀ A : C, IsColimit (((evaluation C D).obj A).mapCocone t))
    {c : Cocone X} (hc : IsColimit c) [PreservesColimit X t.pt] :
    IsColimit (evaluatedCocone t c) := by
  let Q : DiagramOfCocones (X ⋙ T.flip) :=
    { obj k := ((evaluation C D).obj (X.obj k)).mapCocone t
      map f :=
        { hom := t.pt.map (X.map f)
          w j := by
            dsimp
            exact ((t.ι.app j).naturality (X.map f)).symm }
      id k := by
        change t.pt.map (X.map (𝟙 k)) = 𝟙 (t.pt.obj (X.obj k))
        rw [X.map_id, t.pt.map_id]
      comp f g := by
        change t.pt.map (X.map (f ≫ g)) = t.pt.map (X.map f) ≫ t.pt.map (X.map g)
        rw [X.map_comp, t.pt.map_comp] }
  have hQ : ∀ k : K, IsColimit (Q.obj k) := fun k => ht (X.obj k)
  have hlast : IsColimit (t.pt.mapCocone c) := isColimitOfPreserves t.pt hc
  apply IsColimit.ofCoconeUncurry hQ
  let E : Q.coconePoints ≅ X ⋙ t.pt :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro j k f
      change t.pt.map (X.map f) ≫ 𝟙 (t.pt.obj (X.obj k)) =
        𝟙 (t.pt.obj (X.obj j)) ≫ t.pt.map (X.map f)
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  apply IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv E (t.pt.mapCocone c)).symm hlast)
  refine Cocone.ext (Iso.refl _) fun k => ?_
  dsimp [evaluatedCocone, Q, E, NatIso.ofComponents]
  apply (hQ k).hom_ext
  intro j
  dsimp [coconeOfCoconeUncurry]
  rw [(hQ k).fac]
  dsimp only [Q, DiagramOfCocones.coconePoints]
  simp only [Functor.mapCocone_ι_app, Functor.mapCocone_pt,
    evaluation_obj_map, evaluation_obj_obj]
  change (t.ι.app j).app (X.obj k) ≫
      ((𝟙 (t.pt.obj (X.obj k)) ≫ t.pt.map (c.ι.app k)) ≫ 𝟙 (t.pt.obj c.pt)) =
    (T.obj j).map (c.ι.app k) ≫ (t.ι.app j).app c.pt
  exact (congrArg ((t.ι.app j).app (X.obj k) ≫ ·)
    ((Category.comp_id _).trans (Category.id_comp _))).trans
      ((t.ι.app j).naturality (c.ι.app k)).symm



end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_EvaluationFubini

/- Source proof segment: FiniteMultifunctorCoconeSplit -/
section source_FiniteMultifunctorCoconeSplit
/-!
# Exact source cocone comparison for curry/Fubini descent
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe vJ uJ vC uC vD uD

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory
open CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

theorem cancelConjugation {A B T U : D} (e : A ⟶ B) (s : B ⟶ A)
    (f : A ⟶ T) (t : T ⟶ U) (q : U ⟶ T)
    (he : e ≫ s = 𝟙 A) (hq : t ≫ q = 𝟙 T) :
    (e ≫ (s ≫ f ≫ t)) ≫ q = f := by
  calc
    (e ≫ (s ≫ f ≫ t)) ≫ q = (e ≫ s) ≫ f ≫ (t ≫ q) := by simp only [Category.assoc]
    _ = 𝟙 A ≫ f ≫ (t ≫ q) := congrArg (fun a => a ≫ f ≫ (t ≫ q)) he
    _ = 𝟙 A ≫ f ≫ 𝟙 T := congrArg (fun a => 𝟙 A ≫ f ≫ a) hq
    _ = f := (Category.id_comp _).trans (Category.comp_id _)

/-- Transport the iterated last-slot cocone to the original finite product diagram. -/
def transportedSplitCocone {n : ℕ} {J : Fin (n + 1) → Type uJ}
    [∀ i, Category.{vJ} (J i)] (F : (Fin (n + 1) → C) ⥤ D)
    {K : ∀ i, J i ⥤ C} (c : ∀ i, Cocone (K i)) : Cocone (diagram F K) := by
  let E := curriedProductDiagramIso F K
  let b := (evaluatedCocone (cocone (curryLast F) (fun i : Fin n => c i.castSucc))
    (c (Fin.last n))).whisker (Prod.swap _ _)
  exact
    { pt := b.pt
      ι := E.inv ≫ b.ι }

/-- Identify the transported last-slot cocone with the original simultaneous finite-input cocone. -/
def splitCoconeIso {n : ℕ} {J : Fin (n + 1) → Type uJ}
    [∀ i, Category.{vJ} (J i)] (F : (Fin (n + 1) → C) ⥤ D)
    {K : ∀ i, J i ⥤ C} (c : ∀ i, Cocone (K i)) :
    transportedSplitCocone F c ≅ cocone F c := by
  have hpts : Fin.snoc (α := fun _ => C) (fun i : Fin n => (c i.castSucc).pt)
      ((c (Fin.last n)).pt) = (fun i => (c i).pt) :=
    Fin.snoc_init_self (q := fun i => (c i).pt)
  refine Cocone.ext (eqToIso (congrArg F.obj hpts)) fun p => ?_
  let E := curriedProductDiagramIso F K
  let d := evaluatedCocone (cocone (curryLast F) (fun i : Fin n => c i.castSucc))
    (c (Fin.last n))
  with_unfolding_all
    change (E.inv.app p ≫ d.ι.app (p.2, p.1)) ≫ eqToHom (congrArg F.obj hpts) =
      F.map (fun i => (c i).ι.app (coordinates p i))
  dsimp [d, evaluatedCocone, cocone, tupleCocone, curryLast, Functor.curryObj]
  let a : (tupleDiagram (fun i : Fin n => K i.castSucc)).obj p.1 ⟶
      (tupleCocone (fun i : Fin n => c i.castSucc)).pt :=
    fun i => (c i.castSucc).ι.app (coordinates p.1 i)
  let b := (c (Fin.last n)).ι.app p.2
  let sObj : Fin (n + 1) → C :=
    Fin.snoc (α := fun _ => C) ((tupleDiagram (fun i : Fin n => K i.castSucc)).obj p.1)
      ((K (Fin.last n)).obj p.2)
  let mid : Fin (n + 1) → C :=
    Fin.snoc (α := fun _ => C) ((tupleDiagram (fun i : Fin n => K i.castSucc)).obj p.1)
      ((c (Fin.last n)).pt)
  let tObj : Fin (n + 1) → C :=
    Fin.snoc (α := fun _ => C) ((tupleCocone (fun i : Fin n => c i.castSucc)).pt)
      ((c (Fin.last n)).pt)
  let l : sObj ⟶ mid := snocMap (𝟙 _) b
  let r : mid ⟶ tObj := snocMap a (𝟙 _)
  let m : sObj ⟶ tObj := snocMap a b
  let g : (tupleDiagram K).obj p ⟶ (tupleCocone c).pt :=
    fun i => (c i).ι.app (coordinates p i)
  have hm : l ≫ r = m := by
    change (fun i => snocMap (𝟙 _) b i ≫ snocMap a (𝟙 _) i) = snocMap a b
    have hc := snocMap_comp (𝟙 _) a b (𝟙 _)
    simpa only [Category.id_comp, Category.comp_id] using hc.symm
  have hinj : m = eqToHom (splitTupleDiagram_obj K p) ≫ g ≫ eqToHom hpts.symm :=
    (conj_eqToHom_iff_heq m g (splitTupleDiagram_obj K p) hpts).mpr (snocInjection_heq c p)
  have hF : F.map m =
      eqToHom (congrArg F.obj (splitTupleDiagram_obj K p)) ≫ F.map g ≫
        eqToHom (congrArg F.obj hpts.symm) := by
    have hh := congrArg (fun f : sObj ⟶ tObj => F.map f) hinj
    have hcomp := F.map_comp (eqToHom (splitTupleDiagram_obj K p))
      (g ≫ eqToHom hpts.symm)
    have hcomp' := F.map_comp g (eqToHom hpts.symm)
    exact hh.trans (hcomp.trans
      ((congrArg (F.map (eqToHom (splitTupleDiagram_obj K p)) ≫ ·) hcomp').trans
        (congrArg₂ (fun a b => a ≫ F.map g ≫ b)
          (eqToHom_map F (splitTupleDiagram_obj K p)) (eqToHom_map F hpts.symm))))
  have hmF : F.map l ≫ F.map r = F.map m :=
    (F.map_comp l r).symm.trans (congrArg F.map hm)
  let e : F.obj ((tupleDiagram K).obj p) ⟶ F.obj sObj := E.inv.app p
  let q : F.obj tObj ⟶ F.obj ((tupleCocone c).pt) := eqToHom (congrArg F.obj hpts)
  with_unfolding_all
    change (e ≫ (F.map l ≫ F.map r)) ≫ q = F.map g
  have h1 : (e ≫ (F.map l ≫ F.map r)) ≫ q = (e ≫ F.map m) ≫ q :=
    congrArg (fun f : F.obj sObj ⟶ F.obj tObj => (e ≫ f) ≫ q) hmF
  have h2 : (e ≫ F.map m) ≫ q =
      (e ≫ (eqToHom (congrArg F.obj (splitTupleDiagram_obj K p)) ≫ F.map g ≫
        eqToHom (congrArg F.obj hpts.symm))) ≫ q :=
    congrArg (fun f : F.obj sObj ⟶ F.obj tObj => (e ≫ f) ≫ q) hF
  have he : e ≫ eqToHom (congrArg F.obj (splitTupleDiagram_obj K p)) =
      𝟙 (F.obj ((tupleDiagram K).obj p)) := by
    have h := Iso.inv_hom_id_app E p
    rw [curriedProductDiagramIso_hom] at h
    exact h
  have hq : eqToHom (congrArg F.obj hpts.symm) ≫ q =
      𝟙 (F.obj ((tupleCocone c).pt)) := by
    dsimp only [q]
    exact eqToHom_trans _ _ |>.trans (eqToHom_refl _ _)
  let s : F.obj sObj ⟶ F.obj ((tupleDiagram K).obj p) :=
    eqToHom (congrArg F.obj (splitTupleDiagram_obj K p))
  let t : F.obj ((tupleCocone c).pt) ⟶ F.obj tObj :=
    eqToHom (congrArg F.obj hpts.symm)
  let f : F.obj ((tupleDiagram K).obj p) ⟶ F.obj ((tupleCocone c).pt) := F.map g
  have he' : e ≫ s = 𝟙 _ := he
  have hq' : t ≫ q = 𝟙 _ := hq
  have hc : (e ≫ (s ≫ f ≫ t)) ≫ q = f := cancelConjugation e s f t q he' hq'
  exact h1.trans (h2.trans hc)

end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteMultifunctorCoconeSplit

/- Source proof segment: FiniteMultifunctorColimit -/
section source_FiniteMultifunctorColimit
/-!
# Colimits of finite multifunctors from source slot preservation

The original finite multifunctor cocone is colimiting from preservation
in each original slot. Its proof uses a curry/Fubini induction and
actual factor colimit cocones. No joint tuple-diagram colimit in the
source category, or joint multifunctor preservation result, is an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe vJ uJ vC uC vD uD uS

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory
open CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type uC} [Category.{vC} C]

/-- The actual finite multifunctor cocone is colimiting from source
one-slot preservation, with independent original category universes. -/
def isColimitCocone : ∀ (n : ℕ)
    (D : Type uD) [Category.{vD} D]
    (J : Fin n → Type uJ) [∀ i, Category.{vJ} (J i)]
    [∀ i, EssentiallySmall.{uS} (J i)]
    (F : (Fin n → C) ⥤ D)
    [Functor.PreservesColimitsInEachSlot.{0, uC, vC, _, _, uS} F]
    (K : ∀ i, J i ⥤ C) (c : ∀ i, Cocone (K i)),
    (∀ i, IsColimit (c i)) → IsColimit (cocone F c) := by
  intro n
  induction n with
  | zero =>
    intro D hD J hJ hSmall F hF K c hc
    let : Nonempty (ProductIndex J) := ⟨PUnit.unit⟩
    let : Subsingleton (ProductIndex J) := ⟨fun p q => by cases p; cases q; rfl⟩
    let p : ProductIndex J := PUnit.unit
    have htuple : (tupleDiagram K).obj p = (tupleCocone c).pt :=
      funext (fun i => Fin.elim0 i)
    let iso : (diagram F K).obj p ≅ (cocone F c).pt := eqToIso (congrArg F.obj htuple)
    have hι : (cocone F c).ι.app p = iso.hom := by
      change F.map (fun i => (c i).ι.app (coordinates p i)) = eqToHom (congrArg F.obj htuple)
      have hm : (fun i => (c i).ι.app (coordinates p i)) = eqToHom htuple :=
        funext (fun i => Fin.elim0 i)
      exact (congrArg (fun f : (tupleDiagram K).obj p ⟶ (tupleCocone c).pt => F.map f) hm).trans
        (eqToHom_map F htuple)
    refine
      { desc := fun s => iso.inv ≫ s.ι.app p
        fac := ?_
        uniq := ?_ }
    · intro s q
      have hq : q = p := Subsingleton.elim _ _
      subst q
      rw [hι, Iso.hom_inv_id_assoc]
    · intro s m hm
      have h := hm p
      rw [hι] at h
      exact (Iso.eq_inv_comp iso).mpr h
  | succ n ih =>
    intro D hD J hJ hSmall F hF K c hc
    let KT := fun i : Fin n => K i.castSucc
    let cT := fun i : Fin n => c i.castSucc
    let G := curryLast F
    let t := cocone G cT
    let KL := K (Fin.last n)
    let cL := c (Fin.last n)
    have hEval : ∀ x : C, IsColimit (((evaluation C D).obj x).mapCocone t) := by
      intro x
      have hslots : Functor.PreservesColimitsInEachSlot.{0, uC, vC, _, _, uS}
          (G ⋙ (evaluation C D).obj x) := by
        constructor
        intro A i
        have hslot := Functor.PreservesColimitsInEachSlot.preserves
          (F := F) (Fin.snoc (α := fun _ => C) A x) i.castSucc
        have hfun : Pi.replaceFunctor A i ⋙ (G ⋙ (evaluation C D).obj x) =
            Pi.replaceFunctor (Fin.snoc (α := fun _ => C) A x) i.castSucc ⋙ F := by
          change Pi.replaceFunctor A i ⋙ (curryLast F ⋙ (evaluation C D).obj x) = _
          rw [curryLast_eval_eq, ← Functor.assoc, tailTupleSlice_replace_eq]
        exact hfun ▸ hslot
      letI := hslots
      exact ih D (fun i : Fin n => J i.castSucc) (G ⋙ (evaluation C D).obj x) KT cT
        (fun i => hc i.castSucc)
    letI : PreservesColimit KL t.pt := by
      change PreservesColimit KL ((curryLast F).obj (fun i : Fin n => (cT i).pt))
      let := curryLast_preserves_last (F := F) (fun i : Fin n => (cT i).pt)
      let : PreservesColimitsOfShape (J (Fin.last n))
          ((curryLast F).obj (fun i : Fin n => (cT i).pt)) :=
        preservesColimitsOfEssentiallySmall _ _
      exact inferInstance
    let b := evaluatedCocone t cL
    have hb := isColimitEvaluatedCocone hEval (hc (Fin.last n))
    let b' := b.whisker (Prod.swap _ _)
    have hb' : IsColimit b' := hb.whiskerEquivalence (Prod.braiding _ _)
    let E := curriedProductDiagramIso F K
    have hp := (IsColimit.precomposeInvEquiv E b').symm hb'
    exact IsColimit.ofIsoColimit hp (splitCoconeIso F c)



end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteMultifunctorColimit

/- Source proof segment: FiniteMultifunctorTupleColimit -/
section source_FiniteMultifunctorTupleColimit
@[expose] public section

set_option autoImplicit false

noncomputable section

universe vJ uJ vC uC vD uD uS

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory
open CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- The original ordinary tuple-category cocone for a finite input
word, retaining each original factor injection. -/
def wordTupleCocone {n : ℕ} {J : Fin n → Type uJ} [∀ i, Category.{vJ} (J i)]
    (F : (Fin n → C) ⥤ D) {K : ∀ i, J i ⥤ C} (c : ∀ i, Cocone (K i)) :
    Cocone (Functor.pi K ⋙ F) :=
  F.mapCocone
    { pt := fun i => (c i).pt
      ι :=
        { app p i := (c i).ι.app (p i)
          naturality p q f := by
            funext i
            exact ((c i).w (f i)).trans (Category.comp_id _).symm } }

/-- Separate slotwise colimit preservation makes the original finite-input tuple cocone
colimiting. -/
def isColimitWordTupleCocone {n : ℕ} {J : Fin n → Type uJ}
    [∀ i, Category.{vJ} (J i)] [∀ i, EssentiallySmall.{uS} (J i)]
    (F : (Fin n → C) ⥤ D)
    [Functor.PreservesColimitsInEachSlot.{0, uC, vC, uD, vD, uS} F]
    {K : ∀ i, J i ⥤ C} {c : ∀ i, Cocone (K i)} (hc : ∀ i, IsColimit (c i)) :
    IsColimit (wordTupleCocone F c) := by
  apply (Functor.Final.isColimitWhiskerEquiv (coordinatesFunctor J) (wordTupleCocone F c)).toFun
  have h := isColimitCocone n D J F K c hc
  exact h



end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteMultifunctorTupleColimit

/- Source proof segment: FiniteSlotReindex -/
section source_FiniteSlotReindex
/-!
# Original one-slot preservation under finite-index reindexing

Reindexing changes only the presentation of the finite input set.
The actual replacement object and component maps are transported
along the chosen input equivalence, with every source slot retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe ui uj uc uh ud uhD us

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory

variable {I : Type ui} {I' : Type uj}
variable {C : Type uc} [Category.{uh} C]
variable {D : Type ud} [Category.{uhD} D]

/-- Reindex an input tuple along an actual equivalence of its index
types, retaining every original component map. -/
def reindexFunctor (e : I' ≃ I) : (I' → C) ⥤ (I → C) :=
  Pi.comap (fun _ : I' => C) e.symm

theorem replace_reindex_eq [DecidableEq I] [DecidableEq I']
    (e : I' ≃ I) (A : I' → C) (i : I') :
    Pi.replaceFunctor A i ⋙ reindexFunctor e =
      Pi.replaceFunctor (A ∘ e.symm) (e i) := by
  apply Functor.hext
  · intro X
    change Function.update A i X ∘ e.symm = Function.update (A ∘ e.symm) (e i) X
    simpa using Function.update_comp_equiv A e.symm i X
  · intro X Y f
    apply Function.hfunext rfl
    intro j j' hj
    have hidx : j = j' := eq_of_heq hj
    subst j'
    by_cases h : e.symm j = i
    · have he : j = e i := by simpa using congrArg e h
      subst j
      have hmap := Pi.replaceMap_at A i f
      have hmap' := Pi.replaceMap_at (A ∘ e.symm) (e i) f
      change HEq (Pi.replaceMap A i f (e.symm (e i)))
        (Pi.replaceMap (A ∘ e.symm) (e i) f (e i))
      rw [e.symm_apply_apply]
      exact hmap.trans hmap'.symm
    · have he : j ≠ e i := fun hji => h (by simp [hji])
      exact (Pi.replaceMap_other A i (e.symm j) h f).trans
        (Pi.replaceMap_other (A ∘ e.symm) (e i) j he f).symm

/-- The original source slot-preservation condition is preserved
under an actual reindexing of the input type. -/
instance preservesSlots_reindex [DecidableEq I] [DecidableEq I']
    (e : I' ≃ I) (F : (I → C) ⥤ D)
    [Functor.PreservesColimitsInEachSlot.{ui, uc, uh, ud, uhD, us} F] :
    Functor.PreservesColimitsInEachSlot.{uj, uc, uh, ud, uhD, us} (reindexFunctor e ⋙ F) where
  preserves A i := by
    have h := Functor.PreservesColimitsInEachSlot.preserves (F := F) (A ∘ e.symm) (e i)
    have hf : Pi.replaceFunctor A i ⋙ (reindexFunctor e ⋙ F) =
        Pi.replaceFunctor (A ∘ e.symm) (e i) ⋙ F := by
      rw [← Functor.assoc, replace_reindex_eq]
    exact hf ▸ h




end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteSlotReindex

/- Source proof segment: FiniteIndexTransport -/
section source_FiniteIndexTransport
@[expose] public section

set_option autoImplicit false

universe ui uJ vJ uC vC

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory

variable {I : Type ui} {J : I → Type uJ} [∀ i, Category.{vJ} (J i)]
variable {C : Type uC} [Category.{vC} C]

theorem transportedFunctor_obj (K : ∀ i, J i ⥤ C) {i j : I} (h : i = j) (x : J j) :
    (K i).obj ((Pi.eqToEquivalence J h).inverse.obj x) = (K j).obj x := by
  cases h
  rfl

theorem transportedFunctor_map_heq (K : ∀ i, J i ⥤ C) {i j : I} (h : i = j)
    {x y : J j} (f : x ⟶ y) :
    HEq ((K i).map ((Pi.eqToEquivalence J h).inverse.map f)) ((K j).map f) := by
  cases h
  exact HEq.rfl

theorem transportedFunctor_obj_forward (K : ∀ i, J i ⥤ C) {i j : I} (h : i = j) (x : J i) :
    (K j).obj ((Pi.eqToEquivalence J h).functor.obj x) = (K i).obj x := by
  cases h
  rfl

theorem transportedFunctor_map_forward_heq (K : ∀ i, J i ⥤ C) {i j : I} (h : i = j)
    {x y : J i} (f : x ⟶ y) :
    HEq ((K j).map ((Pi.eqToEquivalence J h).functor.map f)) ((K i).map f) := by
  cases h
  exact HEq.rfl

theorem transportedInjection_heq (K : ∀ i, J i ⥤ C) (c : ∀ i, Cocone (K i))
    {i j : I} (h : i = j) (x : J j) :
    HEq ((c i).ι.app ((Pi.eqToEquivalence J h).inverse.obj x)) ((c j).ι.app x) := by
  cases h
  exact HEq.rfl

theorem transportedInjection_forward_heq (K : ∀ i, J i ⥤ C) (c : ∀ i, Cocone (K i))
    {i j : I} (h : i = j) (x : J i) :
    HEq ((c j).ι.app ((Pi.eqToEquivalence J h).functor.obj x)) ((c i).ι.app x) := by
  cases h
  exact HEq.rfl

end CategoryTheory.Limits.FiniteMultifunctor
end
end source_FiniteIndexTransport

/- Source proof segment: FiniteMultifunctorFiniteIndex -/
section source_FiniteMultifunctorFiniteIndex
/-!
# Original finite-index multifunctor colimit cocones

The original finite input type is retained. Its finite product of
factor index categories has the ordinary tuple category structure.
Source one-slot preservation constructs the F-applied original
factor cocone, with full injection and unique-descent maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe ui vJ uJ vC uC vD uD uS

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory
open CategoryTheory.MonoidalCategory.OrderedTensor

variable {I : Type ui}
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- The original factor tuple diagram on the unchanged finite input
type, with all original component maps. -/
def finiteIndexDiagram {J : I → Type uJ} [∀ i, Category.{vJ} (J i)]
    (F : (I → C) ⥤ D) (K : ∀ i, J i ⥤ C) : (∀ i, J i) ⥤ D :=
  Functor.pi K ⋙ F

/-- The actual F-applied original tuple cocone at every finite input
index, including the empty input type. -/
def finiteIndexCocone {J : I → Type uJ} [∀ i, Category.{vJ} (J i)]
    (F : (I → C) ⥤ D) {K : ∀ i, J i ⥤ C} (c : ∀ i, Cocone (K i)) :
    Cocone (finiteIndexDiagram F K) :=
  F.mapCocone
    { pt := fun i => (c i).pt
      ι :=
        { app p i := (c i).ι.app (p i)
          naturality p q f := by
            funext i
            exact ((c i).w (f i)).trans (Category.comp_id _).symm } }

@[simp]
theorem finiteIndexCocone_pt {J : I → Type uJ} [∀ i, Category.{vJ} (J i)]
    (F : (I → C) ⥤ D) {K : ∀ i, J i ⥤ C} (c : ∀ i, Cocone (K i)) :
    (finiteIndexCocone F c).pt = F.obj (fun i => (c i).pt) := rfl

@[simp]
theorem finiteIndexCocone_ι {J : I → Type uJ} [∀ i, Category.{vJ} (J i)]
    (F : (I → C) ⥤ D) {K : ∀ i, J i ⥤ C} (c : ∀ i, Cocone (K i)) (p : ∀ i, J i) :
    (finiteIndexCocone F c).ι.app p = F.map (fun i => (c i).ι.app (p i)) := rfl

/-- Source one-slot preservation makes the original finite-index
operation cocone colimiting. No joint-colimit outcome is supplied. -/
def isColimitFiniteIndexCocone [Finite I] [DecidableEq I] {J : I → Type uJ} [∀ i,
  Category.{vJ} (J i)]
    [∀ i, EssentiallySmall.{uS} (J i)] (F : (I → C) ⥤ D)
    [Functor.PreservesColimitsInEachSlot.{ui, uC, vC, uD, vD, uS} F]
    {K : ∀ i, J i ⥤ C} {c : ∀ i, Cocone (K i)} (hc : ∀ i, IsColimit (c i)) :
    IsColimit (finiteIndexCocone F c) := by
  let : Fintype I := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let F' := reindexFunctor e ⋙ F
  let K' := fun i => K (e i)
  let c' := fun i => c (e i)
  have h := isColimitWordTupleCocone F' (fun i => hc (e i))
  let E := Pi.equivalenceOfEquiv J e
  let A : (∀ i, J (e i)) ⥤ (I → C) := E.functor ⋙ Functor.pi K
  let B : (∀ i, J (e i)) ⥤ (I → C) := Functor.pi K' ⋙ reindexFunctor e
  have hobj : ∀ p, A.obj p = B.obj p := by
    intro p
    funext i
    change (K i).obj ((Pi.eqToEquivalence J (e.apply_symm_apply i)).functor.obj (p (e.symm i))) =
      (K (e (e.symm i))).obj (p (e.symm i))
    exact transportedFunctor_obj_forward K (e.apply_symm_apply i) _
  have hmap : ∀ p q (f : p ⟶ q), HEq (A.map f) (B.map f) := by
    intro p q f
    apply Function.hfunext rfl
    intro i i' hi
    have heq : i = i' := eq_of_heq hi
    subst i'
    change HEq ((K i).map ((Pi.eqToEquivalence J (e.apply_symm_apply i)).functor.map (f
      (e.symm i))))
      ((K (e (e.symm i))).map (f (e.symm i)))
    exact transportedFunctor_map_forward_heq K (e.apply_symm_apply i) _
  let U : A ≅ B := NatIso.ofComponents (fun p => eqToIso (hobj p)) (by
    intro p q f
    have he := (conj_eqToHom_iff_heq _ _ (hobj p) (hobj q)).mpr (hmap p q f)
    exact (congrArg (· ≫ eqToHom (hobj q)) he).trans
      (by simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]))
  let T : E.functor ⋙ finiteIndexDiagram F K ≅ Functor.pi K' ⋙ F' :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight U F ≪≫ Functor.associator _ _ _
  have hp := (IsColimit.precomposeHomEquiv T (wordTupleCocone F' c')).symm h
  have hpt : (wordTupleCocone F' c').pt = (finiteIndexCocone F c).pt := by
    apply congrArg F.obj
    funext i
    dsimp [F', c', reindexFunctor, Pi.comap, wordTupleCocone, finiteIndexCocone]
    exact congrArg (fun j => (c j).pt) (e.apply_symm_apply i)
  have hw : IsColimit ((finiteIndexCocone F c).whisker E.functor) := by
    apply IsColimit.ofIsoColimit hp
    refine Cocone.ext (eqToIso hpt) fun p => ?_
    let x : A.obj p ⟶ (fun i => (c i).pt) :=
      fun i => (c i).ι.app (E.functor.obj p i)
    let y : B.obj p ⟶ ((reindexFunctor e).obj (fun i => (c' i).pt)) :=
      (reindexFunctor e).map (fun i => (c' i).ι.app (p i))
    have hy : HEq x y := by
      apply Function.hfunext rfl
      intro i i' hi
      have heq : i = i' := eq_of_heq hi
      subst i'
      change HEq ((c i).ι.app ((Pi.eqToEquivalence J (e.apply_symm_apply i)).functor.obj (p
        (e.symm i))))
        ((c (e (e.symm i))).ι.app (p (e.symm i)))
      exact transportedInjection_forward_heq K c (e.apply_symm_apply i) _
    have hpoints : (fun i => (c i).pt) = (reindexFunctor e).obj (fun i => (c' i).pt) := by
      funext i
      change (c i).pt = (c (e (e.symm i))).pt
      exact congrArg (fun j => (c j).pt) (e.apply_symm_apply i).symm
    have hxy : x = eqToHom (hobj p) ≫ y ≫ eqToHom hpoints.symm :=
      (conj_eqToHom_iff_heq x y (hobj p) hpoints).mpr hy
    have hF := congrArg (fun f : A.obj p ⟶ (fun i => (c i).pt) => F.map f) hxy
    have hmap1 := F.map_comp (eqToHom (hobj p)) (y ≫ eqToHom hpoints.symm)
    have hmap2 := F.map_comp y (eqToHom hpoints.symm)
    have hFxy : F.map x = eqToHom (congrArg F.obj (hobj p)) ≫ F.map y ≫
        eqToHom (congrArg F.obj hpoints.symm) :=
      hF.trans (hmap1.trans ((congrArg (F.map (eqToHom (hobj p)) ≫ ·) hmap2).trans
        (congrArg₂ (fun a b => a ≫ F.map y ≫ b)
          (eqToHom_map F (hobj p)) (eqToHom_map F hpoints.symm))))
    have hT : T.hom.app p = eqToHom (congrArg F.obj (hobj p)) := by
      with_unfolding_all
        change 𝟙 (F.obj (A.obj p)) ≫ (F.map (eqToHom (hobj p)) ≫
          𝟙 (F.obj (B.obj p))) = eqToHom (congrArg F.obj (hobj p))
      exact (Category.id_comp _).trans
        ((Category.comp_id _).trans (eqToHom_map F (hobj p)))
    have htarget : eqToHom (congrArg F.obj hpoints.symm) = (eqToIso hpt).hom := by
      rfl
    with_unfolding_all
      change (T.hom.app p ≫ F.map y) ≫ (eqToIso hpt).hom = F.map x
    exact ((congrArg (fun a => (a ≫ F.map y) ≫ (eqToIso hpt).hom) hT).trans
      ((Category.assoc _ _ _).trans ((congrArg (eqToHom (congrArg F.obj (hobj p)) ≫ F.map y ≫ ·)
        htarget.symm).trans hFxy.symm)))
  exact (Functor.Final.isColimitWhiskerEquiv E.functor (finiteIndexCocone F c)).toFun hw



end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteMultifunctorFiniteIndex

/- Source proof segment: PiEssentiallySmall -/
section source_PiEssentiallySmall
/-!
# Original small-index products of essentially small categories
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe ui u v us

namespace CategoryTheory

/-- A small original index family of essentially small categories
has an essentially small product category, via the product of the
actual equivalences to their small models. -/
theorem piEssentiallySmall {I : Type ui} [Small.{us} I]
    (C : I → Type u) [∀ i, Category.{v} (C i)] [∀ i, EssentiallySmall.{us} (C i)] :
    EssentiallySmall.{us} (∀ i, C i) := by
  let D := fun i => SmallModel.{us} (C i)
  let : ∀ i, SmallCategory (D i) := fun i => inferInstanceAs (SmallCategory (SmallModel.{us} (C i)))
  let : LocallySmall.{us} (∀ i, D i) :=
    { hom_small := fun X Y => by
        change Small.{us} (∀ i, X i ⟶ Y i)
        infer_instance }
  let : EssentiallySmall.{us} (∀ i, D i) := essentiallySmall_of_small_of_locallySmall _
  exact (essentiallySmall_congr (Equivalence.pi (fun i => equivSmallModel.{us} (C i)))).mpr
    inferInstance



end CategoryTheory
end
end
end source_PiEssentiallySmall

/- Source proof segment: PiEvaluationColimits -/
section source_PiEvaluationColimits
/-!
# Original independently sized carrier-family colimits and evaluation maps
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe ui uJ vJ uC vC

namespace CategoryTheory.Limits

open CategoryTheory

variable {I : Type ui} {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C] [HasColimitsOfShape J C]

/-- Color evaluation preserves the original colimits, with color,
diagram, object and hom universes independent. It is transported
through the actual discrete-functor equivalence and evaluation iso. -/
instance piEvalPreservesColimitsOfShape (i : I) :
    PreservesColimitsOfShape J (Pi.eval (fun _ : I => C) i) := by
  let E := piEquivalenceFunctorDiscrete I C
  let : PreservesColimitsOfShape J (E.functor ⋙ (evaluation (Discrete I) C).obj ⟨i⟩)
    := inferInstance
  exact preservesColimitsOfShape_of_natIso (piEquivalenceFunctorDiscreteCompEvaluationIso C i)

/-- The source colimits construct colimits in the original carrier
family category through its actual equivalence with discrete functors. -/
instance piHasColimitsOfShape : HasColimitsOfShape J (I → C) :=
  Adjunction.hasColimitsOfShape_of_equivalence (piEquivalenceFunctorDiscrete I C).functor




end CategoryTheory.Limits
end
end
end source_PiEvaluationColimits

/- Source proof segment: ConstantConnectedColimits -/
section source_ConstantConnectedColimits
/-!
# Actual constant functors preserve connected colimits
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uJ vJ uB vB uC vC

namespace CategoryTheory.Limits

open CategoryTheory

variable {J : Type uJ} [Category.{vJ} J] [IsConnected J]
variable {B : Type uB} [Category.{vB} B] {C : Type uC} [Category.{vC} C]

/-- The constant coefficient functor preserves every original
connected colimit. Its mapped cocone is constructed from original
identity coefficient maps; no terminality of the coefficient is used. -/
instance constantPreservesConnectedColimits (X : C) :
    PreservesColimitsOfShape J ((Functor.const B).obj X) where
  preservesColimit {D} :=
    { preserves := fun {c} _ => ⟨by
        let F := (Functor.const B).obj X
        let E : D ⋙ F ≅ (Functor.const J).obj X :=
          NatIso.ofComponents (fun _ => Iso.refl X) (by
            intro j k f
            exact (Category.comp_id _).trans (Category.id_comp _).symm)
        let t := constCocone J X
        have ht := (IsColimit.precomposeHomEquiv E t).symm (isColimitConstCocone J X)
        apply IsColimit.ofIsoColimit ht
        refine Cocone.ext (Iso.refl X) fun j => ?_
        change (𝟙 X ≫ 𝟙 X) ≫ 𝟙 X = 𝟙 X
        simp only [Category.id_comp]⟩ }



end CategoryTheory.Limits
end
end
end source_ConstantConnectedColimits

/- Source proof segment: ConnectedFinalUniqueHoms -/
section source_ConnectedFinalUniqueHoms
/-!
# Final functors from connected categories to categories with unique arrows
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uJ vJ uD vD

namespace CategoryTheory.Functor

open CategoryTheory Limits

variable {J : Type uJ} [Category.{vJ} J] {D : Type uD} [Category.{vD} D]

/-- The structured-arrow projection is an actual equivalence
when every arrow in the target category is unique. -/
def structuredArrowProjectionEquivalenceUnique (F : J ⥤ D)
    [∀ X Y : D, Unique (X ⟶ Y)] (d : D) : StructuredArrow d F ≌ J := by
  let P := StructuredArrow.proj d F
  let : P.Full :=
    { map_surjective := fun f => ⟨StructuredArrow.homMk f (Subsingleton.elim _ _), rfl⟩ }
  let : P.Faithful :=
    { map_injective := fun h => StructuredArrow.hom_ext _ _ h }
  let : P.EssSurj :=
    { mem_essImage := fun j => ⟨StructuredArrow.mk (default : d ⟶ F.obj j), ⟨Iso.refl j⟩⟩ }
  let : P.IsEquivalence := {}
  exact P.asEquivalence

/-- Every actual functor from a connected category to a category
with unique arrows is final. Its comma categories are connected
through the constructed projection equivalences. -/
theorem finalOfIsConnectedUniqueHoms [IsConnected J] (F : J ⥤ D)
    [∀ X Y : D, Unique (X ⟶ Y)] : F.Final where
  out d := by
    let E := structuredArrowProjectionEquivalenceUnique F d
    exact (isConnected_iff_of_final E.functor).mpr inferInstance



end CategoryTheory.Functor
end
end
end source_ConnectedFinalUniqueHoms

/- Source proof segment: FiniteSiftedDiagonal -/
section source_FiniteSiftedDiagonal
/-!
# Actual finite diagonals of sifted indexing categories
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uJ vJ

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory CategoryTheory.MonoidalCategory.OrderedTensor

variable (J : Type uJ) [Category.{vJ} J]

/-- The actual diagonal into the recursive finite product index,
including the singleton category in degree zero. -/
def diagonalProductFunctor : (n : ℕ) → J ⥤ ProductIndex (fun _ : Fin n => J)
  | 0 => (Functor.const J).obj PUnit.unit
  | n + 1 => (diagonalProductFunctor n).prod' (𝟭 J)

/-- Every actual finite diagonal of a sifted category is final.
Degree zero uses connectedness; successors use the original
sifted binary diagonal and actual product of final functors. -/
theorem diagonalProductFinal [IsSifted J] : (n : ℕ) → (diagonalProductFunctor J n).Final
  | 0 => by
    let : ∀ X Y : ProductIndex (fun _ : Fin 0 => J), Unique (X ⟶ Y) := fun _ _ => by
      change Unique PUnit.{vJ + 1}
      infer_instance
    exact Functor.finalOfIsConnectedUniqueHoms _
  | n + 1 => by
    let : (diagonalProductFunctor J n).Final := diagonalProductFinal n
    exact inferInstanceAs ((diagonalProductFunctor J n).prod' (𝟭 J)).Final

/-- The actual finite diagonal followed by the original tuple
coordinate equivalence is final, retaining every finite coordinate. -/
def diagonalWordFunctor (n : ℕ) : J ⥤ (Fin n → J) :=
  diagonalProductFunctor J n ⋙ coordinatesFunctor (fun _ : Fin n => J)

instance diagonalWordFinal [IsSifted J] (n : ℕ) : (diagonalWordFunctor J n).Final := by
  let : (diagonalProductFunctor J n).Final := diagonalProductFinal J n
  exact Functor.final_comp _ _




end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteSiftedDiagonal

/- Source proof segment: FiniteDiagonalCoordinates -/
section source_FiniteDiagonalCoordinates
/-!
# Original coordinate maps of the finite sifted diagonal
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uJ vJ

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory CategoryTheory.MonoidalCategory.OrderedTensor

variable {J : Type uJ} [Category.{vJ} J]

/-- Every original coordinate of the finite diagonal is the
original object, including all finite arities. -/
theorem diagonalProductCoordinates : ∀ (n : ℕ) (j : J) (i : Fin n),
    coordinates ((diagonalProductFunctor J n).obj j) i = j
  | 0, _, i => Fin.elim0 i
  | n + 1, j, i => by
    cases i using Fin.lastCases with
    | last => exact (coordinates_last _).trans rfl
    | cast i => exact (coordinates_castSucc _ i).trans (diagonalProductCoordinates n j i)

/-- Every actual coordinate morphism of the finite diagonal is
the original morphism, with its original source and target retained. -/
theorem diagonalProductCoordinatesMap : ∀ (n : ℕ) {j k : J} (f : j ⟶ k) (i : Fin n),
    HEq (coordinatesMap ((diagonalProductFunctor J n).map f) i) f
  | 0, _, _, _, i => Fin.elim0 i
  | n + 1, j, k, f, i => by
    cases i using Fin.lastCases with
    | last =>
      simp only [diagonalProductFunctor, coordinatesMap, Fin.lastCases_last]
      change HEq (eqToHom _ ≫ f ≫ eqToHom _) f
      exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
    | cast i =>
      simp only [diagonalProductFunctor, coordinatesMap, Fin.lastCases_castSucc]
      change HEq (eqToHom _ ≫ coordinatesMap ((diagonalProductFunctor J n).map f) i ≫ eqToHom _) f
      exact ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).trans
        (diagonalProductCoordinatesMap n f i)

/-- The original finite tuple diagonal, with all components the
same original object/morphism. -/
def diagonalTupleFunctor (n : ℕ) : J ⥤ (Fin n → J) where
  obj j _ := j
  map f _ := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The recursive finite diagonal and its actual tuple coordinates
have precisely the original tuple diagonal object function. -/
theorem diagonalWord_obj (n : ℕ) (j : J) :
    (diagonalWordFunctor J n).obj j = (diagonalTupleFunctor (J := J) n).obj j := by
  funext i
  exact diagonalProductCoordinates n j i

/-- The original coordinate readbacks give full naturality of the
finite tuple diagonal comparison, at every original morphism. -/
def diagonalWordIsoTuple (n : ℕ) :
    diagonalWordFunctor J n ≅ diagonalTupleFunctor (J := J) n :=
  NatIso.ofComponents (fun j => eqToIso (diagonalWord_obj n j)) (by
    intro j k f
    have hmap : HEq ((diagonalWordFunctor J n).map f) ((diagonalTupleFunctor (J :=
      J) n).map f) := by
      apply Function.hfunext rfl
      intro i i' hi
      have h : i = i' := eq_of_heq hi
      subst i'
      exact diagonalProductCoordinatesMap n f i
    have h := (conj_eqToHom_iff_heq _ _ (diagonalWord_obj n j) (diagonalWord_obj n k)).mpr hmap
    exact (congrArg (· ≫ eqToHom (diagonalWord_obj n k)) h).trans
      (by simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, eqToIso.hom]))

instance diagonalTupleFinal [IsSifted J] (n : ℕ) : (diagonalTupleFunctor (J := J) n).Final :=
  Functor.final_of_natIso (diagonalWordIsoTuple n)



end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteDiagonalCoordinates

/- Source proof segment: FiniteIndexSiftedDiagonal -/
section source_FiniteIndexSiftedDiagonal
/-!
# Original arbitrary finite-index sifted diagonals
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe ui uJ vJ

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory

variable {J : Type uJ} [Category.{vJ} J]

/-- The original diagonal repeats the original object and morphism
in every position of the unchanged finite input index type. -/
def diagonalFiniteIndexFunctor (I : Type ui) : J ⥤ (I → J) where
  obj j _ := j
  map f _ := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every original finite-index diagonal of a sifted category is
final. The coordinate equivalence is used only in the proof, while
the displayed diagonal retains the original finite input type. -/
instance diagonalFiniteIndexFinal (I : Type ui) [Finite I] [IsSifted J] :
    (diagonalFiniteIndexFunctor (J := J) I).Final := by
  let : Fintype I := Fintype.ofFinite I
  let n := Fintype.card I
  let e := Fintype.equivFin I
  let E := Pi.equivalenceOfEquiv (fun _ : Fin n => J) e
  have h : diagonalTupleFunctor (J := J) n ⋙ E.inverse = diagonalFiniteIndexFunctor (J := J) I := by
    apply Functor.ext (fun _ => rfl)
  let : (diagonalTupleFunctor (J := J) n ⋙ E.inverse).Final := Functor.final_comp _ _
  exact Functor.final_of_natIso (eqToIso h)



end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteIndexSiftedDiagonal

/- Source proof segment: FiniteSiftedColimits -/
section source_FiniteSiftedColimits
/-!
# Actual finite multifunctor commutation with sifted colimits
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe ui uJ vJ uC vC uD vD us

namespace CategoryTheory.Limits.FiniteMultifunctor

open CategoryTheory

variable {I : Type ui} [Finite I] [DecidableEq I]
variable {J : Type uJ} [Category.{vJ} J] [EssentiallySmall.{us} J] [IsSifted J]
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- Apply an original finite multifunctor to a family of original
diagrams at the same sifted index object. -/
def finiteSiftedDiagram (F : (I → C) ⥤ D) (K : ∀ _ : I, J ⥤ C) : J ⥤ D :=
  diagonalFiniteIndexFunctor I ⋙ finiteIndexDiagram F K

/-- The actual original finite multifunctor of factor colimit
points with simultaneous original factor injection maps. -/
def finiteSiftedCocone (F : (I → C) ⥤ D) {K : ∀ _ : I, J ⥤ C} (c : ∀ i, Cocone (K i)) :
    Cocone (finiteSiftedDiagram F K) :=
  (finiteIndexCocone F c).whisker (diagonalFiniteIndexFunctor I)

/-- Source preservation in each slot and the proved original
finite diagonal finality construct the actual sifted tensor colimit. -/
def isColimitFiniteSiftedCocone (F : (I → C) ⥤ D)
    [Functor.PreservesColimitsInEachSlot.{ui, uC, vC, uD, vD, us} F]
    {K : ∀ _ : I, J ⥤ C} {c : ∀ i, Cocone (K i)} (hc : ∀ i, IsColimit (c i)) :
    IsColimit (finiteSiftedCocone F c) :=
  (Functor.Final.isColimitWhiskerEquiv (diagonalFiniteIndexFunctor I) (finiteIndexCocone F c)).symm
    (isColimitFiniteIndexCocone F hc)

omit [Finite I] [DecidableEq I] [EssentiallySmall.{us} J] [IsSifted J] in
/-- Every original sifted node has precisely the simultaneous
original factor tensor injection, including the empty index family. -/
theorem finiteSiftedCocone_ι (F : (I → C) ⥤ D) {K : ∀ _ : I, J ⥤ C}
    (c : ∀ i, Cocone (K i)) (j : J) :
    (finiteSiftedCocone F c).ι.app j = F.map (fun i => (c i).ι.app j) := rfl

/-- Original simultaneous factor injections determine every map
from the actual finite multifunctor of sifted colimit points. -/
theorem finiteSifted_hom_ext (F : (I → C) ⥤ D)
    [Functor.PreservesColimitsInEachSlot.{ui, uC, vC, uD, vD, us} F]
    {K : ∀ _ : I, J ⥤ C} {c : ∀ i, Cocone (K i)} (hc : ∀ i, IsColimit (c i))
    {Y : D} {f g : F.obj (fun i => (c i).pt) ⟶ Y}
    (h : ∀ j, F.map (fun i => (c i).ι.app j) ≫ f = F.map (fun i => (c i).ι.app j) ≫ g) : f = g :=
  (isColimitFiniteSiftedCocone F hc).hom_ext h




end CategoryTheory.Limits.FiniteMultifunctor
end
end
end source_FiniteSiftedColimits

/- Source proof segment: PiPointwisePreservation -/
section source_PiPointwisePreservation
/-!
# Actual pointwise preservation in independently sized carrier-family categories
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe ui uJ vJ uB vB uC vC

namespace CategoryTheory.Limits

open CategoryTheory

variable {I : Type ui} {J : Type uJ} [Category.{vJ} J]
variable {B : Type uB} [Category.{vB} B] {C : Type uC} [Category.{vC} C]

/-- Original color evaluations detect preservation of the full
carrier-family colimit. The proof uses the actual discrete-functor
equivalence and reflection of colimits, with independent universes. -/
theorem preservesColimitsOfShape_of_piEvaluation (F : B ⥤ (I → C))
    (h : ∀ i : I, PreservesColimitsOfShape J (F ⋙ Pi.eval (fun _ : I => C) i)) :
    PreservesColimitsOfShape J F := by
  let E := piEquivalenceFunctorDiscrete I C
  let H := F ⋙ E.functor
  let : PreservesColimitsOfShape J H :=
    preservesColimitsOfShape_of_evaluation H J (fun i => by
      let : PreservesColimitsOfShape J (F ⋙ Pi.eval (fun _ : I => C) i.as) := h i.as
      let e : H ⋙ (evaluation (Discrete I) C).obj i ≅ F ⋙ Pi.eval (fun _ : I => C) i.as :=
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft F (piEquivalenceFunctorDiscreteCompEvaluationIso C i.as)
      exact preservesColimitsOfShape_of_natIso e.symm)
  exact preservesColimitsOfShape_of_reflects_of_preserves F E.functor



end CategoryTheory.Limits
end
end
end source_PiPointwisePreservation

/- Source proof segment: ReflexivePairSifted -/
section source_ReflexivePairSifted
/-!
# The walking reflexive pair is sifted

The diagonal is final by explicit spans in its structured-arrow
categories. Thus the colimit of an actual reflexive pair is a sifted
colimit. This is the indexing fact used in finite tensor commutation
and operadic algebra colimit creation.

Reference: Pavlov--Scholbach, *Admissibility and rectification of
colored symmetric operads*, arXiv:1410.5675v4, Section 3.
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Limits.WalkingReflexivePair

open CategoryTheory

/-- The chosen map to the coequalizer-side object. -/
def toZero : (x : WalkingReflexivePair) → (x ⟶ zero)
  | zero => Hom.id zero
  | one => Hom.left

/-- A distinguished cocone under a pair of objects of the walking
reflexive pair. -/
def pairCenter (p : WalkingReflexivePair × WalkingReflexivePair) :
    StructuredArrow p (Functor.diag WalkingReflexivePair) :=
  StructuredArrow.mk (toZero p.1, toZero p.2)

/-- Each cocone with apex `zero` is connected to the distinguished
cocone by the original reflexion and the original two parallel maps. -/
theorem zeroNodeZigzag (x y : WalkingReflexivePair) (f : x ⟶ zero) (g : y ⟶ zero) :
    Zigzag (StructuredArrow.mk (T := Functor.diag WalkingReflexivePair) (f, g))
      (pairCenter (x, y)) := by
  cases x with
  | zero =>
    cases f
    cases y with
    | zero =>
      cases g
      exact Zigzag.refl _
    | one =>
      cases g with
      | left => exact Zigzag.refl _
      | right =>
        let m : StructuredArrow (zero, one) (Functor.diag WalkingReflexivePair) :=
          StructuredArrow.mk (Hom.reflexion, Hom.id one)
        let hr : m ⟶ StructuredArrow.mk (T := Functor.diag WalkingReflexivePair)
            (Hom.id zero, Hom.right) :=
          StructuredArrow.homMk Hom.right rfl
        let hl : m ⟶ pairCenter (zero, one) :=
          StructuredArrow.homMk Hom.left rfl
        exact Zigzag.of_inv_hom hr hl
  | one =>
    cases y with
    | zero =>
      cases g
      cases f with
      | left => exact Zigzag.refl _
      | right =>
        let m : StructuredArrow (one, zero) (Functor.diag WalkingReflexivePair) :=
          StructuredArrow.mk (Hom.id one, Hom.reflexion)
        let hr : m ⟶ StructuredArrow.mk (T := Functor.diag WalkingReflexivePair)
            (Hom.right, Hom.id zero) :=
          StructuredArrow.homMk Hom.right rfl
        let hl : m ⟶ pairCenter (one, zero) :=
          StructuredArrow.homMk Hom.left rfl
        exact Zigzag.of_inv_hom hr hl
    | one =>
      cases f with
      | left =>
        cases g with
        | left => exact Zigzag.refl _
        | right =>
          let m : StructuredArrow (one, one) (Functor.diag WalkingReflexivePair) :=
            StructuredArrow.mk (Hom.leftCompReflexion, Hom.id one)
          let hr : m ⟶ StructuredArrow.mk (T := Functor.diag WalkingReflexivePair)
              (Hom.left, Hom.right) :=
            StructuredArrow.homMk Hom.right rfl
          let hl : m ⟶ pairCenter (one, one) :=
            StructuredArrow.homMk Hom.left rfl
          exact Zigzag.of_inv_hom hr hl
      | right =>
        cases g with
        | left =>
          let m : StructuredArrow (one, one) (Functor.diag WalkingReflexivePair) :=
            StructuredArrow.mk (Hom.id one, Hom.leftCompReflexion)
          let hr : m ⟶ StructuredArrow.mk (T := Functor.diag WalkingReflexivePair)
              (Hom.right, Hom.left) :=
            StructuredArrow.homMk Hom.right rfl
          let hl : m ⟶ pairCenter (one, one) :=
            StructuredArrow.homMk Hom.left rfl
          exact Zigzag.of_inv_hom hr hl
        | right =>
          let m : StructuredArrow (one, one) (Functor.diag WalkingReflexivePair) :=
            StructuredArrow.mk (Hom.id one, Hom.id one)
          let hr : m ⟶ StructuredArrow.mk (T := Functor.diag WalkingReflexivePair)
              (Hom.right, Hom.right) :=
            StructuredArrow.homMk Hom.right rfl
          let hl : m ⟶ pairCenter (one, one) :=
            StructuredArrow.homMk Hom.left rfl
          exact Zigzag.of_inv_hom hr hl

/-- Any structured arrow for the diagonal connects to the distinguished
cocone, first by the original map to `zero`, then by the explicit spans. -/
theorem zigzagToPairCenter (p : WalkingReflexivePair × WalkingReflexivePair)
    (a : StructuredArrow p (Functor.diag WalkingReflexivePair)) :
    Zigzag a (pairCenter p) := by
  obtain ⟨z, h, rfl⟩ := a.mk_surjective
  obtain ⟨f, g⟩ := h
  cases z with
  | zero => exact zeroNodeZigzag p.1 p.2 f g
  | one =>
    exact (Zigzag.of_hom (StructuredArrow.homMk'
      (StructuredArrow.mk (T := Functor.diag WalkingReflexivePair) (f, g)) Hom.left)).trans
        (zeroNodeZigzag p.1 p.2 (f ≫ Hom.left) (g ≫ Hom.left))

/-- The actual diagonal of the walking reflexive pair is final. -/
instance diagonalFinal : (Functor.diag WalkingReflexivePair).Final where
  out p := by
    let : Nonempty (StructuredArrow p (Functor.diag WalkingReflexivePair)) :=
      ⟨pairCenter p⟩
    apply zigzag_isConnected
    intro a b
    exact (zigzagToPairCenter p a).trans (zigzagToPairCenter p b).symm

/-- Reflexive coequalizers are sifted colimits. -/
instance isSifted : IsSifted WalkingReflexivePair where




end CategoryTheory.Limits.WalkingReflexivePair
end
end source_ReflexivePairSifted
