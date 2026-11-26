/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.CategoryTheory.Category.RelCat
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Relations with disjoint-union tensor

The disjoint union of sets is both a categorical product and a coproduct in the
category of relations. The empty set is both terminal and initial. A separate
object wrapper carries this Cartesian symmetric monoidal structure, independently
of the product-of-types tensor on `RelCat`.

This is the relational monoidal model described by Joyal, Street and Verity,
Traced monoidal categories (1996), Section 6, preceding Proposition 6.3,
https://doi.org/10.1017/S0305004100074338. The finite-path trace is a separate construction.
-/

@[expose] public section
universe u
namespace CategoryTheory

/-- The relation category equipped with disjoint union rather than product of types as tensor. -/
structure SumRelCat where
  /-- The underlying set of the relation object. -/
  carrier : Type u

namespace SumRelCat

instance : CoeSort SumRelCat.{u} (Type u) := ⟨SumRelCat.carrier⟩

/-- Regard a type as an object of the disjoint-union relation category. -/
abbrev of (X : Type u) : SumRelCat.{u} := ⟨X⟩

/-- Relational morphisms retain their source and target object tags. -/
structure Hom (X Y : SumRelCat.{u}) : Type u where
  /-- Construct a morphism from a relation. -/
  ofRel ::
  /-- The underlying relation. -/
  rel : SetRel X Y

/-- Morphisms compose by existential relational composition. -/
instance : LargeCategory SumRelCat.{u} where
  Hom := Hom
  id _ := .ofRel SetRel.id
  comp f g := .ofRel (f.rel.comp g.rel)

namespace Hom
/-- Relations determine relational morphisms. -/
@[ext] theorem ext {X Y : SumRelCat.{u}} (f g : X ⟶ Y) (h : f.rel = g.rel) : f = g := by
  cases f
  cases g
  congr
end Hom

open Limits MonoidalCategory
open scoped MonoidalCategory

theorem rel_comp {X Y Z : SumRelCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).rel = f.rel.comp g.rel := rfl

@[simp] theorem rel_id (X : SumRelCat.{u}) : (𝟙 X : X ⟶ X).rel = SetRel.id := rfl

/-- Disjoint union of the underlying sets. -/
abbrev sum (X Y : SumRelCat.{u}) : SumRelCat.{u} := of (Sum X Y)

/-- The empty relation object. -/
abbrev zero : SumRelCat.{u} := of PEmpty

/-- The first relational projection is defined exactly on the left summand. -/
def fst (X Y : SumRelCat.{u}) : sum X Y ⟶ X := .ofRel {p | p.1 = Sum.inl p.2}

/-- The second relational projection is defined exactly on the right summand. -/
def snd (X Y : SumRelCat.{u}) : sum X Y ⟶ Y := .ofRel {p | p.1 = Sum.inr p.2}

/-- Pair two relations by selecting the relation indexed by the output summand. -/
def pair {X Y Z : SumRelCat.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ sum X Y :=
  .ofRel {p | match p.2 with | .inl x => (p.1, x) ∈ f.rel | .inr y => (p.1, y) ∈ g.rel}

@[simp] theorem fst_rel_eq (X Y : SumRelCat.{u}) :
    (fst X Y).rel = {p | p.1 = Sum.inl p.2} := rfl

@[simp] theorem snd_rel_eq (X Y : SumRelCat.{u}) :
    (snd X Y).rel = {p | p.1 = Sum.inr p.2} := rfl

@[simp] theorem pair_rel_eq {X Y Z : SumRelCat.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    (pair f g).rel = {p | match p.2 with
      | .inl x => (p.1, x) ∈ f.rel | .inr y => (p.1, y) ∈ g.rel} := rfl

theorem comp_rel {X Y Z : SumRelCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z) :
    (x, z) ∈ (f ≫ g).rel ↔ ∃ y, (x, y) ∈ f.rel ∧ (y, z) ∈ g.rel := Iff.rfl

theorem fst_rel (X Y : SumRelCat.{u}) (s : Sum X Y) (x : X) :
    (s, x) ∈ (fst X Y).rel ↔ s = Sum.inl x := Iff.rfl

theorem snd_rel (X Y : SumRelCat.{u}) (s : Sum X Y) (y : Y) :
    (s, y) ∈ (snd X Y).rel ↔ s = Sum.inr y := Iff.rfl

theorem pair_rel {X Y Z : SumRelCat.{u}} (f : Z ⟶ X) (g : Z ⟶ Y)
    (z : Z) (s : Sum X Y) : (z, s) ∈ (pair f g).rel ↔
      match s with | .inl x => (z, x) ∈ f.rel | .inr y => (z, y) ∈ g.rel := Iff.rfl

@[simp] theorem comp_fst_rel {X Y Z : SumRelCat.{u}} (f : Z ⟶ sum X Y) (z : Z) (x : X) :
    (z, x) ∈ (f ≫ fst X Y).rel ↔ (z, Sum.inl x) ∈ f.rel := by
  simp [fst, rel_comp, SetRel.comp, Set.mem_ofPred_eq]

@[simp] theorem comp_snd_rel {X Y Z : SumRelCat.{u}} (f : Z ⟶ sum X Y) (z : Z) (y : Y) :
    (z, y) ∈ (f ≫ snd X Y).rel ↔ (z, Sum.inr y) ∈ f.rel := by
  simp [snd, rel_comp, SetRel.comp, Set.mem_ofPred_eq]

@[simp] theorem pair_fst {X Y Z : SumRelCat.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    pair f g ≫ fst X Y = f := by
  apply Hom.ext
  ext ⟨z, x⟩
  rw [comp_fst_rel]
  rfl

@[simp] theorem pair_snd {X Y Z : SumRelCat.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    pair f g ≫ snd X Y = g := by
  apply Hom.ext
  ext ⟨z, y⟩
  rw [comp_snd_rel]
  rfl

/-- A relation into a sum is determined by its two projections. -/
theorem hom_ext {X Y Z : SumRelCat.{u}} {f g : Z ⟶ sum X Y}
    (hf : f ≫ fst X Y = g ≫ fst X Y) (hg : f ≫ snd X Y = g ≫ snd X Y) : f = g := by
  apply Hom.ext
  ext ⟨z, s⟩
  cases s with
  | inl x => simpa using congrArg (fun h : Z ⟶ X => (z, x) ∈ h.rel) hf
  | inr y => simpa using congrArg (fun h : Z ⟶ Y => (z, y) ∈ h.rel) hg

/-- The chosen disjoint union has the binary product universal property. -/
abbrev binaryProduct (X Y : SumRelCat.{u}) : LimitCone (Limits.pair X Y) where
  cone := BinaryFan.mk (fst X Y) (snd X Y)
  isLimit := BinaryFan.IsLimit.mk _ (fun f g => pair f g)
    (fun f g => pair_fst f g) (fun f g => pair_snd f g)
    (fun f g _m hf hg => hom_ext (hf.trans (pair_fst f g).symm) (hg.trans (pair_snd f g).symm))

/-- The empty set is terminal among relations. -/
def zeroIsTerminal : IsTerminal (zero : SumRelCat.{u}) :=
  IsTerminal.ofUniqueHom (fun _ => .ofRel ∅) (fun _ f => by
    apply Hom.ext
    ext ⟨_, e⟩
    exact PEmpty.elim e)

/-- The empty set is initial among relations. -/
def zeroIsInitial : IsInitial (zero : SumRelCat.{u}) :=
  IsInitial.ofUniqueHom (fun _ => .ofRel ∅) (fun _ f => by
    apply Hom.ext
    ext ⟨e, _⟩
    exact PEmpty.elim e)

/-- The left injection is the graph of the sum constructor. -/
def inl (X Y : SumRelCat.{u}) : X ⟶ sum X Y := .ofRel {p | Sum.inl p.1 = p.2}

/-- The right injection is the graph of the sum constructor. -/
def inr (X Y : SumRelCat.{u}) : Y ⟶ sum X Y := .ofRel {p | Sum.inr p.1 = p.2}

/-- Copair two relations by selecting the relation indexed by the input summand. -/
def desc {X Y Z : SumRelCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) : sum X Y ⟶ Z :=
  .ofRel {p | match p.1 with | .inl x => (x, p.2) ∈ f.rel | .inr y => (y, p.2) ∈ g.rel}

@[simp] theorem inl_rel_eq (X Y : SumRelCat.{u}) :
    (inl X Y).rel = {p | Sum.inl p.1 = p.2} := rfl

@[simp] theorem inr_rel_eq (X Y : SumRelCat.{u}) :
    (inr X Y).rel = {p | Sum.inr p.1 = p.2} := rfl

@[simp] theorem desc_rel_eq {X Y Z : SumRelCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (desc f g).rel = {p | match p.1 with
      | .inl x => (x, p.2) ∈ f.rel | .inr y => (y, p.2) ∈ g.rel} := rfl

@[simp] theorem inl_comp_rel {X Y Z : SumRelCat.{u}} (f : sum X Y ⟶ Z) (x : X) (z : Z) :
    (x, z) ∈ (inl X Y ≫ f).rel ↔ (Sum.inl x, z) ∈ f.rel := by
  simp [inl, rel_comp, SetRel.comp, Set.mem_ofPred_eq]

@[simp] theorem inr_comp_rel {X Y Z : SumRelCat.{u}} (f : sum X Y ⟶ Z) (y : Y) (z : Z) :
    (y, z) ∈ (inr X Y ≫ f).rel ↔ (Sum.inr y, z) ∈ f.rel := by
  simp [inr, rel_comp, SetRel.comp, Set.mem_ofPred_eq]

@[simp] theorem inl_desc {X Y Z : SumRelCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    inl X Y ≫ desc f g = f := by
  apply Hom.ext
  ext ⟨x, z⟩
  rw [inl_comp_rel]
  rfl

@[simp] theorem inr_desc {X Y Z : SumRelCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    inr X Y ≫ desc f g = g := by
  apply Hom.ext
  ext ⟨y, z⟩
  rw [inr_comp_rel]
  rfl

/-- A relation out of a sum is determined by its two injections. -/
theorem hom_ext_out {X Y Z : SumRelCat.{u}} {f g : sum X Y ⟶ Z}
    (hf : inl X Y ≫ f = inl X Y ≫ g) (hg : inr X Y ≫ f = inr X Y ≫ g) : f = g := by
  apply Hom.ext
  ext ⟨s, z⟩
  cases s with
  | inl x => simpa using congrArg (fun h : X ⟶ Z => (x, z) ∈ h.rel) hf
  | inr y => simpa using congrArg (fun h : Y ⟶ Z => (y, z) ∈ h.rel) hg

@[simp] theorem inl_fst (X Y : SumRelCat.{u}) : inl X Y ≫ fst X Y = 𝟙 X := by
  apply Hom.ext
  ext ⟨x, y⟩
  simp [rel_comp, SetRel.comp, SetRel.id, Set.mem_ofPred_eq]

@[simp] theorem inr_snd (X Y : SumRelCat.{u}) : inr X Y ≫ snd X Y = 𝟙 Y := by
  apply Hom.ext
  ext ⟨x, y⟩
  simp [rel_comp, SetRel.comp, SetRel.id, Set.mem_ofPred_eq]

/-- The same disjoint union has the binary coproduct universal property. -/
def binaryCoproduct (X Y : SumRelCat.{u}) : ColimitCocone (Limits.pair X Y) where
  cocone := BinaryCofan.mk (inl X Y) (inr X Y)
  isColimit := BinaryCofan.IsColimit.mk _ (fun f g => desc f g)
    (fun f g => inl_desc f g) (fun f g => inr_desc f g)
    (fun f g _m hf hg => hom_ext_out (hf.trans (inl_desc f g).symm) (hg.trans (inr_desc f g).symm))

/-- Relations admit binary coproducts with the displayed sum cocones. -/
instance hasBinaryCoproducts : HasBinaryCoproducts SumRelCat.{u} := by
  let : ∀ {X Y : SumRelCat.{u}}, HasColimit (Limits.pair X Y) :=
    fun {X Y} => HasColimit.mk (binaryCoproduct X Y)
  exact hasBinaryCoproducts_of_hasColimit_pair _

/-- The empty relation object supplies an initial object. -/
instance hasInitial : HasInitial SumRelCat.{u} := zeroIsInitial.hasInitial

/-- Relations admit all finite coproducts. -/
instance hasFiniteCoproducts : HasFiniteCoproducts SumRelCat.{u} :=
  hasFiniteCoproducts_of_has_binary_and_initial

/-- Disjoint union gives the relation category its Cartesian monoidal structure.
Reducibility keeps the concrete tensor carriers available to downstream simplification. -/
@[reducible]
instance cartesianMonoidalCategory : CartesianMonoidalCategory SumRelCat.{u} :=
  .ofChosenFiniteProducts ⟨asEmptyCone zero, zeroIsTerminal⟩ binaryProduct

@[simp] theorem tensorObj_def (X Y : SumRelCat.{u}) : X ⊗ Y = sum X Y := rfl
@[simp] theorem tensorUnit_def : 𝟙_ SumRelCat.{u} = zero := rfl

/-- The canonical Cartesian symmetry exchanges the summands. -/
instance braidedCategory : BraidedCategory SumRelCat.{u} :=
  .ofCartesianMonoidalCategory

/-- Tensor acts separately on the two summands. -/
theorem tensor_eq_pair {X Y U V : SumRelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V) :
    f ⊗ₘ g = pair (fst X U ≫ f) (snd X U ≫ g) := rfl

theorem tensor_rel {X Y U V : SumRelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V)
    (x : (X ⊗ U : SumRelCat)) (y : (Y ⊗ V : SumRelCat)) :
    (x, y) ∈ (f ⊗ₘ g).rel ↔ match x, y with
      | .inl a, .inl b => (a, b) ∈ f.rel
      | .inr a, .inr b => (a, b) ∈ g.rel
      | _, _ => False := by
  rw [tensor_eq_pair]
  cases x <;> cases y <;> simp [rel_comp, SetRel.comp, Set.mem_ofPred_eq]

theorem whiskerLeft_rel (X : SumRelCat.{u}) {Y Z : SumRelCat.{u}} (f : Y ⟶ Z)
    (x : (X ⊗ Y : SumRelCat)) (y : (X ⊗ Z : SumRelCat)) :
    (x, y) ∈ (X ◁ f).rel ↔ match x, y with
      | .inl a, .inl b => a = b
      | .inr a, .inr b => (a, b) ∈ f.rel
      | _, _ => False := by
  change (x, y) ∈ ((𝟙 X) ⊗ₘ f).rel ↔ _
  rw [tensor_rel]
  cases x <;> cases y <;> rfl

theorem whiskerRight_rel {X Y : SumRelCat.{u}} (f : X ⟶ Y) (Z : SumRelCat.{u})
    (x : (X ⊗ Z : SumRelCat)) (y : (Y ⊗ Z : SumRelCat)) :
    (x, y) ∈ (f ▷ Z).rel ↔ match x, y with
      | .inl a, .inl b => (a, b) ∈ f.rel
      | .inr a, .inr b => a = b
      | _, _ => False := by
  change (x, y) ∈ (f ⊗ₘ (𝟙 Z)).rel ↔ _
  rw [tensor_rel]
  cases x <;> cases y <;> rfl

/-- The associator is the pairing `⟨π₁ ≫ π₁, ⟨π₁ ≫ π₂, π₂⟩⟩` of the projections
`(X ⊕ Y) ⊕ Z ⟶ X ⊕ (Y ⊕ Z)`. -/
theorem associator_hom_eq_pair (X Y Z : SumRelCat.{u}) :
    (α_ X Y Z).hom = pair (fst (sum X Y) Z ≫ fst X Y)
      (pair (fst (sum X Y) Z ≫ snd X Y) (snd (sum X Y) Z)) := rfl

/-- The inverse associator is the pairing `⟨⟨π₁, π₂ ≫ π₁⟩, π₂ ≫ π₂⟩` of the projections
`X ⊕ (Y ⊕ Z) ⟶ (X ⊕ Y) ⊕ Z`. -/
theorem associator_inv_eq_pair (X Y Z : SumRelCat.{u}) :
    (α_ X Y Z).inv = pair (pair (fst X (sum Y Z)) (snd X (sum Y Z) ≫ fst Y Z))
      (snd X (sum Y Z) ≫ snd Y Z) := rfl

theorem associator_hom_rel (X Y Z : SumRelCat.{u})
    (x : ((X ⊗ Y) ⊗ Z : SumRelCat)) (y : (X ⊗ (Y ⊗ Z) : SumRelCat)) :
    (x, y) ∈ (α_ X Y Z).hom.rel ↔ Equiv.sumAssoc X Y Z x = y := by
  rw [associator_hom_eq_pair]
  rcases x with (xL | xM) | xR <;> rcases y with yL | (yM | yR) <;>
    simp [rel_comp, SetRel.comp, Set.mem_ofPred_eq]

theorem associator_inv_rel (X Y Z : SumRelCat.{u})
    (x : (X ⊗ (Y ⊗ Z) : SumRelCat)) (y : ((X ⊗ Y) ⊗ Z : SumRelCat)) :
    (x, y) ∈ (α_ X Y Z).inv.rel ↔ (Equiv.sumAssoc X Y Z).symm x = y := by
  rw [associator_inv_eq_pair]
  rcases x with xL | (xM | xR) <;> rcases y with (yL | yM) | yR <;>
    simp [rel_comp, SetRel.comp, Set.mem_ofPred_eq]

/-- Symmetry is the relation that swaps the two summands. -/
theorem braiding_hom_eq_pair (X Y : SumRelCat.{u}) : (β_ X Y).hom = pair (snd X Y) (fst X Y) := rfl

theorem braiding_hom_rel (X Y : SumRelCat.{u})
    (x : (X ⊗ Y : SumRelCat)) (y : (Y ⊗ X : SumRelCat)) :
    (x, y) ∈ (β_ X Y).hom.rel ↔ x.swap = y := by
  rw [braiding_hom_eq_pair]
  cases x <;> cases y <;> simp [Set.mem_ofPred_eq]

theorem leftUnitor_hom_rel (X : SumRelCat.{u})
    (x : (𝟙_ SumRelCat ⊗ X : SumRelCat)) (y : X) :
    (x, y) ∈ (λ_ X).hom.rel ↔ x = Sum.inr y := by
  rw [CartesianMonoidalCategory.leftUnitor_hom]
  rfl

theorem rightUnitor_hom_rel (X : SumRelCat.{u})
    (x : (X ⊗ 𝟙_ SumRelCat : SumRelCat)) (y : X) :
    (x, y) ∈ (ρ_ X).hom.rel ↔ x = Sum.inl y := by
  rw [CartesianMonoidalCategory.rightUnitor_hom]
  rfl

/-- The left unitor inverse is the right injection past the empty summand. -/
theorem leftUnitor_inv_eq_inr (X : SumRelCat.{u}) : (λ_ X).inv = inr zero X := by
  apply hom_ext
  · exact zeroIsTerminal.hom_ext _ _
  · erw [inr_snd]
    exact CartesianMonoidalCategory.leftUnitor_inv_snd X

/-- The right unitor inverse is the left injection before the empty summand. -/
theorem rightUnitor_inv_eq_inl (X : SumRelCat.{u}) : (ρ_ X).inv = inl X zero := by
  apply hom_ext
  · erw [inl_fst]
    exact CartesianMonoidalCategory.rightUnitor_inv_fst X
  · exact zeroIsTerminal.hom_ext _ _

theorem leftUnitor_inv_rel (X : SumRelCat.{u})
    (x : X) (y : (𝟙_ SumRelCat ⊗ X : SumRelCat)) :
    (x, y) ∈ (λ_ X).inv.rel ↔ Sum.inr x = y := by rw [leftUnitor_inv_eq_inr]; rfl

theorem rightUnitor_inv_rel (X : SumRelCat.{u})
    (x : X) (y : (X ⊗ 𝟙_ SumRelCat : SumRelCat)) :
    (x, y) ∈ (ρ_ X).inv.rel ↔ Sum.inl x = y := by rw [rightUnitor_inv_eq_inl]; rfl

@[simp] theorem tensor_rel_eq {X Y U V : SumRelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V) :
    (f ⊗ₘ g).rel = {p | match p.1, p.2 with
      | .inl a, .inl b => (a, b) ∈ f.rel
      | .inr a, .inr b => (a, b) ∈ g.rel
      | _, _ => False} := by ext ⟨x, y⟩; exact tensor_rel f g x y

@[simp] theorem whiskerLeft_rel_eq (X : SumRelCat.{u}) {Y Z : SumRelCat.{u}} (f : Y ⟶ Z) :
    (X ◁ f).rel = {p | match p.1, p.2 with
      | .inl a, .inl b => a = b
      | .inr a, .inr b => (a, b) ∈ f.rel
      | _, _ => False} := by ext ⟨x, y⟩; exact whiskerLeft_rel X f x y

@[simp] theorem whiskerRight_rel_eq {X Y : SumRelCat.{u}} (f : X ⟶ Y) (Z : SumRelCat.{u}) :
    (f ▷ Z).rel = {p | match p.1, p.2 with
      | .inl a, .inl b => (a, b) ∈ f.rel
      | .inr a, .inr b => a = b
      | _, _ => False} := by ext ⟨x, y⟩; exact whiskerRight_rel f Z x y

@[simp] theorem associator_hom_rel_eq (X Y Z : SumRelCat.{u}) :
    (α_ X Y Z).hom.rel = {p | Equiv.sumAssoc X Y Z p.1 = p.2} := by
  ext ⟨x, y⟩; exact associator_hom_rel X Y Z x y

@[simp] theorem associator_inv_rel_eq (X Y Z : SumRelCat.{u}) :
    (α_ X Y Z).inv.rel = {p | (Equiv.sumAssoc X Y Z).symm p.1 = p.2} := by
  ext ⟨x, y⟩; exact associator_inv_rel X Y Z x y

@[simp] theorem braiding_hom_rel_eq (X Y : SumRelCat.{u}) :
    (β_ X Y).hom.rel = {p | p.1.swap = p.2} := by
  ext ⟨x, y⟩; exact braiding_hom_rel X Y x y

@[simp] theorem leftUnitor_hom_rel_eq (X : SumRelCat.{u}) :
    (λ_ X).hom.rel = {p | p.1 = Sum.inr p.2} := by
  ext ⟨x, y⟩; exact leftUnitor_hom_rel X x y

@[simp] theorem rightUnitor_hom_rel_eq (X : SumRelCat.{u}) :
    (ρ_ X).hom.rel = {p | p.1 = Sum.inl p.2} := by
  ext ⟨x, y⟩; exact rightUnitor_hom_rel X x y

@[simp] theorem leftUnitor_inv_rel_eq (X : SumRelCat.{u}) :
    (λ_ X).inv.rel = {p | Sum.inr p.1 = p.2} := by
  ext ⟨x, y⟩; exact leftUnitor_inv_rel X x y

@[simp] theorem rightUnitor_inv_rel_eq (X : SumRelCat.{u}) :
    (ρ_ X).inv.rel = {p | Sum.inl p.1 = p.2} := by
  ext ⟨x, y⟩; exact rightUnitor_inv_rel X x y

end SumRelCat
end CategoryTheory
