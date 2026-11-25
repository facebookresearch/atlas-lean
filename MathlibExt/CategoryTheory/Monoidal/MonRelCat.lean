/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.Traced
public import Mathlib.Order.Category.Preord
public import Mathlib.Basic.Rel
/-!
# Preorders and monotone relations

A morphism is a relation downward closed in its input and upward closed in its
output. Composition is existential relational composition; the identity is the
preorder relation, not equality. Product of preorders supplies a symmetric
monoidal structure, with structural maps given by upward-closed order-isomorphism
graphs. Existential feedback supplies all six symmetric trace axioms.

This is the Hoare category of Arthan, Martin, Mathiesen and Oliva,
A General Framework for Sound and Complete Floyd-Hoare Logics, Definition 3.1
and Section 5, https://arxiv.org/pdf/0807.1016. No antisymmetry, finiteness or
nonemptiness assumption is imposed. These are abstract relational constructions;
no particular assertion language is fixed.
-/

@[expose] public section
namespace CategoryTheory
universe u
/-- Preordered objects with monotone relations as morphisms. -/
structure MonRelCat where
  /-- The underlying type. -/
  carrier : Type u
  /-- The preorder; antisymmetry is not required. -/
  [str : Preorder carrier]
attribute [instance] MonRelCat.str
namespace MonRelCat
instance : CoeSort MonRelCat.{u} (Type u) := ⟨MonRelCat.carrier⟩
/-- Regard a preordered type as a monotone-relation object. -/
abbrev of (X : Type u) [Preorder X] : MonRelCat.{u} := ⟨X⟩
/-- Relations closed downwards in the input and upwards in the output. -/
structure Hom (X Y : MonRelCat.{u}) where
  /-- The underlying relation. -/
  rel : SetRel X Y
  /-- Strengthen inputs and weaken outputs. -/
  closed : ∀ {x x' : X} {y y' : Y}, x' ≤ x → y ≤ y' → (x, y) ∈ rel → (x', y') ∈ rel
/-- The underlying relation determines a morphism. -/
@[ext]
theorem Hom.ext {X Y : MonRelCat.{u}} (f g : Hom X Y) (h : f.rel = g.rel) : f = g := by
  cases f
  cases g
  congr
/-- The preorder relation is the identity morphism. -/
def ident (X : MonRelCat.{u}) : Hom X X where
  rel := {p | p.1 ≤ p.2}
  closed hx hy h := hx.trans (h.trans hy)
/-- Existential composition of monotone relations. -/
def compose {X Y Z : MonRelCat.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  rel := f.rel.comp g.rel
  closed hx hz h := by
    obtain ⟨y, hxy, hyz⟩ := h
    exact ⟨y, f.closed hx le_rfl hxy, g.closed le_rfl hz hyz⟩
instance : LargeCategory MonRelCat.{u} where
  Hom := Hom
  id := ident
  comp := compose
  id_comp f := by
    apply Hom.ext
    ext ⟨x, y⟩
    change (∃ z, x ≤ z ∧ (z, y) ∈ f.rel) ↔ (x, y) ∈ f.rel
    constructor
    · rintro ⟨z, hxz, hzy⟩
      exact f.closed hxz le_rfl hzy
    · intro h
      exact ⟨x, le_rfl, h⟩
  comp_id f := by
    apply Hom.ext
    ext ⟨x, y⟩
    change (∃ z, (x, z) ∈ f.rel ∧ z ≤ y) ↔ (x, y) ∈ f.rel
    constructor
    · rintro ⟨z, hxz, hzy⟩
      exact f.closed le_rfl hzy hxz
    · intro h
      exact ⟨y, h, le_rfl⟩
  assoc f g h := by
    apply Hom.ext
    exact SetRel.comp_assoc f.rel g.rel h.rel
@[simp] theorem rel_id (X : MonRelCat.{u}) : (𝟙 X : X ⟶ X).rel = {p | p.1 ≤ p.2} := rfl
@[simp] theorem rel_comp {X Y Z : MonRelCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).rel = f.rel.comp g.rel := rfl

/-- The upward-closed graph of a monotone map. -/
def graph {X Y : MonRelCat.{u}} (f : X →o Y) : X ⟶ Y where
  rel := {p | f p.1 ≤ p.2}
  closed hx hy h := (f.monotone hx).trans (h.trans hy)
@[simp] theorem graph_rel {X Y : MonRelCat.{u}} (f : X →o Y) :
    (graph f).rel = {p | f p.1 ≤ p.2} := rfl
@[simp] theorem graph_id (X : MonRelCat.{u}) : graph (OrderHom.id : X →o X) = 𝟙 X := rfl
@[simp] theorem graph_comp {X Y Z : MonRelCat.{u}} (f : X →o Y) (g : Y →o Z) :
    graph f ≫ graph g = graph (g.comp f) := by
  apply Hom.ext
  ext ⟨x, z⟩
  change (∃ y, f x ≤ y ∧ g y ≤ z) ↔ g (f x) ≤ z
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact (g.monotone hxy).trans hyz
  · intro h
    exact ⟨f x, le_rfl, h⟩

/-- An order isomorphism induces an isomorphism of monotone relations. -/
def isoOfOrderIso {X Y : MonRelCat.{u}} (e : X ≃o Y) : X ≅ Y where
  hom := graph (e : X →o Y)
  inv := graph (e.symm : Y →o X)
  hom_inv_id := by
    have h : (e.symm : Y →o X).comp (e : X →o Y) = OrderHom.id := by
      ext x
      exact e.symm_apply_apply x
    exact (graph_comp (e : X →o Y) (e.symm : Y →o X)).trans (congrArg graph h)
  inv_hom_id := by
    have h : (e : X →o Y).comp (e.symm : Y →o X) = OrderHom.id := by
      ext x
      exact e.apply_symm_apply x
    exact (graph_comp (e.symm : Y →o X) (e : X →o Y)).trans (congrArg graph h)

@[simp] theorem isoOfOrderIso_hom_comp_rel {X Y Z : MonRelCat.{u}} (e : X ≃o Y)
    (f : Y ⟶ Z) (x : X) (z : Z) :
    (x, z) ∈ ((isoOfOrderIso e).hom ≫ f).rel ↔ (e x, z) ∈ f.rel := by
  change (∃ y, e x ≤ y ∧ (y, z) ∈ f.rel) ↔ (e x, z) ∈ f.rel
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact f.closed hxy le_rfl hyz
  · intro h
    exact ⟨e x, le_rfl, h⟩

@[simp] theorem comp_isoOfOrderIso_hom_rel {X Y Z : MonRelCat.{u}} (f : X ⟶ Y)
    (e : Y ≃o Z) (x : X) (z : Z) :
    (x, z) ∈ (f ≫ (isoOfOrderIso e).hom).rel ↔ (x, e.symm z) ∈ f.rel := by
  change (∃ y, (x, y) ∈ f.rel ∧ e y ≤ z) ↔ (x, e.symm z) ∈ f.rel
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact f.closed le_rfl (e.le_symm_apply.mpr hyz) hxy
  · intro h
    exact ⟨e.symm z, h, by simp⟩
open MonoidalCategory
/-- The coordinatewise product preorder. -/
abbrev prod (X Y : MonRelCat.{u}) : MonRelCat.{u} := of (X × Y)
/-- The singleton tensor unit. -/
abbrev unit : MonRelCat.{u} := of PUnit

/-- Tensor two relations componentwise. -/
def tensor {X Y U V : MonRelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V) : prod X U ⟶ prod Y V where
  rel := {p | (p.1.1, p.2.1) ∈ f.rel ∧ (p.1.2, p.2.2) ∈ g.rel}
  closed hx hy h := ⟨f.closed hx.1 hy.1 h.1, g.closed hx.2 hy.2 h.2⟩
@[simp] theorem tensor_graph {X Y U V : MonRelCat.{u}} (f : X →o Y) (g : U →o V) :
    tensor (graph f) (graph g) = graph (f.prodMap g) := rfl
@[simp] theorem tensor_graph_id {X Y U : MonRelCat.{u}} (f : X →o Y) :
    tensor (graph f) (𝟙 U) = graph (f.prodMap OrderHom.id) := rfl
@[simp] theorem tensor_id_graph {X U V : MonRelCat.{u}} (g : U →o V) :
    tensor (𝟙 X) (graph g) = graph (OrderHom.id.prodMap g) := rfl

/-- Remove the singleton on the left. -/
def leftUnitOrderIso (X : MonRelCat.{u}) : PUnit × X ≃o X where
  toEquiv := Equiv.punitProd X
  map_rel_iff' := by simp
/-- Remove the singleton on the right. -/
def rightUnitOrderIso (X : MonRelCat.{u}) : X × PUnit ≃o X where
  toEquiv := Equiv.prodPUnit X
  map_rel_iff' := by simp

/-- Product tensor with the standard order-isomorphism structural maps. -/
@[reducible]
instance monoidalStruct : MonoidalCategoryStruct MonRelCat.{u} where
  tensorObj := prod
  tensorUnit := unit
  tensorHom := tensor
  whiskerLeft X {_ _} f := tensor (𝟙 X) f
  whiskerRight {_ _} f Y := tensor f (𝟙 Y)
  associator X Y Z := isoOfOrderIso (OrderIso.prodAssoc X Y Z)
  leftUnitor X := isoOfOrderIso (leftUnitOrderIso X)
  rightUnitor X := isoOfOrderIso (rightUnitOrderIso X)

@[simp] theorem tensor_rel {X Y U V : MonRelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V)
    (x : X × U) (y : Y × V) :
    (x, y) ∈ (f ⊗ₘ g).rel ↔ (x.1, y.1) ∈ f.rel ∧ (x.2, y.2) ∈ g.rel := Iff.rfl

theorem tensor_rel_eq {X Y U V : MonRelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V) :
    (f ⊗ₘ g).rel = {p | (p.1.1, p.2.1) ∈ f.rel ∧ (p.1.2, p.2.2) ∈ g.rel} := rfl

/-- Product tensor satisfies monoidal coherence. -/
@[reducible]
instance monoidalCategory : MonoidalCategory MonRelCat.{u} where
  toMonoidalCategoryStruct := monoidalStruct
  tensorHom_def {X Y U V} f g := by
    apply Hom.ext
    ext ⟨x, y⟩
    change ((x.1, y.1) ∈ f.rel ∧ (x.2, y.2) ∈ g.rel) ↔
      ∃ z : Y × U, ((x.1, z.1) ∈ f.rel ∧ x.2 ≤ z.2) ∧
        (z.1 ≤ y.1 ∧ (z.2, y.2) ∈ g.rel)
    constructor
    · rintro ⟨hf, hg⟩
      exact ⟨(y.1, x.2), ⟨hf, le_rfl⟩, le_rfl, hg⟩
    · rintro ⟨z, ⟨hf, hz⟩, hy, hg⟩
      exact ⟨f.closed le_rfl hy hf, g.closed hz le_rfl hg⟩
  id_tensorHom_id _ _ := rfl
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [rel_comp, SetRel.comp, tensor_rel_eq, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨z, ⟨hf₁, hf₂⟩, hg₁, hg₂⟩
      exact ⟨⟨z.1, hf₁, hg₁⟩, ⟨z.2, hf₂, hg₂⟩⟩
    · rintro ⟨⟨a, hf₁, hg₁⟩, ⟨b, hf₂, hg₂⟩⟩
      exact ⟨(a, b), ⟨hf₁, hf₂⟩, hg₁, hg₂⟩
  whiskerLeft_id _ _ := rfl
  id_whiskerRight _ _ := rfl
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by
    apply Hom.ext
    ext ⟨x, y⟩
    erw [comp_isoOfOrderIso_hom_rel, isoOfOrderIso_hom_comp_rel]
    exact and_assoc
  leftUnitor_naturality {X Y} f := by
    apply Hom.ext
    ext ⟨x, y⟩
    erw [comp_isoOfOrderIso_hom_rel, isoOfOrderIso_hom_comp_rel]
    change (True ∧ (x.2, y) ∈ f.rel) ↔ (x.2, y) ∈ f.rel
    simp
  rightUnitor_naturality {X Y} f := by
    apply Hom.ext
    ext ⟨x, y⟩
    erw [comp_isoOfOrderIso_hom_rel, isoOfOrderIso_hom_comp_rel]
    change ((x.1, y) ∈ f.rel ∧ True) ↔ (x.1, y) ∈ f.rel
    simp
  pentagon W X Y Z := by
    change tensor (graph _) (𝟙 Z) ≫ graph _ ≫ tensor (𝟙 W) (graph _) = graph _ ≫ graph _
    simp only [tensor_graph_id, tensor_id_graph, graph_comp]
    congr 1
  triangle X Y := by
    change graph _ ≫ tensor (𝟙 X) (graph _) = tensor (graph _) (𝟙 Y)
    simp only [tensor_graph_id, tensor_id_graph, graph_comp]
    congr 1
/-- The symmetry exchanges the two coordinates. -/
instance braidedCategory : BraidedCategory MonRelCat.{u} where
  braiding X Y := isoOfOrderIso (OrderIso.prodComm : X × Y ≃o Y × X)
  braiding_naturality_right X {_ _} f := by
    apply Hom.ext
    ext ⟨x, y⟩
    erw [comp_isoOfOrderIso_hom_rel, isoOfOrderIso_hom_comp_rel]
    exact and_comm
  braiding_naturality_left {_ _} f Z := by
    apply Hom.ext
    ext ⟨x, y⟩
    erw [comp_isoOfOrderIso_hom_rel, isoOfOrderIso_hom_comp_rel]
    exact and_comm
  hexagon_forward X Y Z := by
    change graph _ ≫ graph _ ≫ graph _ = tensor (graph _) (𝟙 Z) ≫ graph _ ≫ tensor (𝟙 Y) (graph _)
    simp only [tensor_graph_id, tensor_id_graph, graph_comp]
    congr 1
  hexagon_reverse X Y Z := by
    change graph _ ≫ graph _ ≫ graph _ = tensor (𝟙 X) (graph _) ≫ graph _ ≫ tensor (graph _) (𝟙 Y)
    simp only [tensor_graph_id, tensor_id_graph, graph_comp]
    congr 1
/-- Swapping twice is the preorder identity. -/
instance symmetricCategory : SymmetricCategory MonRelCat.{u} where
  toBraidedCategory := braidedCategory
  symmetry X Y := by
    change graph _ ≫ graph _ = graph (OrderHom.id : prod X Y →o prod X Y)
    rw [graph_comp]
    congr 1

variable {X X' Y Y' U V W Z : MonRelCat.{u}}
/-- Existential feedback over a shared hidden coordinate. -/
def feedback (f : X ⊗ U ⟶ Y ⊗ U) : X ⟶ Y where
  rel := {p | ∃ a : U, ((p.1, a), (p.2, a)) ∈ f.rel}
  closed {x x' y y'} hx hy h := by
    obtain ⟨a, ha⟩ := h
    exact ⟨a, f.closed (x := (x, a)) (x' := (x', a))
      (y := (y, a)) (y' := (y', a)) ⟨hx, le_rfl⟩ ⟨hy, le_rfl⟩ ha⟩
@[simp] theorem feedback_rel (f : X ⊗ U ⟶ Y ⊗ U) (x : X) (y : Y) :
    (x, y) ∈ (feedback f).rel ↔ ∃ a : U, ((x, a), (y, a)) ∈ f.rel := Iff.rfl

/-- Visible composition commutes with existential feedback. -/
theorem feedback_naturality (f : X ⊗ U ⟶ Y ⊗ U) (g : X' ⟶ X) (h : Y ⟶ Y') :
    feedback ((g ⊗ₘ 𝟙 U) ≫ f ≫ (h ⊗ₘ 𝟙 U)) = g ≫ feedback f ≫ h := by
  apply Hom.ext
  ext ⟨x, y⟩
  change (∃ u : U, ∃ a : X × U, ((x, a.1) ∈ g.rel ∧ u ≤ a.2) ∧
      ∃ b : Y × U, (a, b) ∈ f.rel ∧ (b.1, y) ∈ h.rel ∧ b.2 ≤ u) ↔
    ∃ a : X, (x, a) ∈ g.rel ∧ ∃ b : Y,
      (∃ u : U, ((a, u), (b, u)) ∈ f.rel) ∧ (b, y) ∈ h.rel
  constructor
  · rintro ⟨u, a, ⟨hg, hua⟩, b, hf, hh, hbu⟩
    exact ⟨a.1, hg, b.1, ⟨u, f.closed (x := a) (x' := (a.1, u)) (y := b) (y' := (b.1, u))
      ⟨le_rfl, hua⟩ ⟨le_rfl, hbu⟩ hf⟩, hh⟩
  · rintro ⟨a, hg, b, ⟨u, hf⟩, hh⟩
    exact ⟨u, (a, u), ⟨hg, le_rfl⟩, (b, u), hf, hh, le_rfl⟩

/-- An arbitrary monotone relation can slide around feedback. -/
theorem feedback_dinaturality (f : X ⊗ U ⟶ Y ⊗ V) (g : V ⟶ U) :
    feedback (f ≫ (𝟙 Y ⊗ₘ g)) = feedback ((𝟙 X ⊗ₘ g) ≫ f) := by
  apply Hom.ext
  ext ⟨x, y⟩
  change (∃ u : U, ∃ z : Y × V, ((x, u), z) ∈ f.rel ∧ z.1 ≤ y ∧ (z.2, u) ∈ g.rel) ↔
    ∃ v : V, ∃ z : X × U, (x ≤ z.1 ∧ (v, z.2) ∈ g.rel) ∧ (z, (y, v)) ∈ f.rel
  constructor
  · rintro ⟨u, z, hf, hy, hg⟩
    exact ⟨z.2, (x, u), ⟨le_rfl, hg⟩, f.closed le_rfl ⟨hy, le_rfl⟩ hf⟩
  · rintro ⟨v, z, ⟨hx, hg⟩, hf⟩
    exact ⟨z.2, (y, v), f.closed ⟨hx, le_rfl⟩ le_rfl hf, le_rfl, hg⟩

/-- Feedback through symmetry recovers the preorder relation. -/
theorem feedback_yanking (X : MonRelCat.{u}) : feedback (β_ X X).hom = 𝟙 X := by
  apply Hom.ext
  ext ⟨x, y⟩
  change (∃ u : X, u ≤ y ∧ x ≤ u) ↔ x ≤ y
  constructor
  · rintro ⟨u, huy, hxu⟩
    exact hxu.trans huy
  · intro h
    exact ⟨x, h, le_rfl⟩

/-- Feedback over the singleton unit removes the unitors. -/
theorem feedback_vanishing_unit (f : X ⊗ 𝟙_ MonRelCat ⟶ Y ⊗ 𝟙_ MonRelCat) :
    feedback f = (ρ_ X).inv ≫ f ≫ (ρ_ Y).hom := by
  apply Hom.ext
  ext ⟨x, y⟩
  change (∃ u : PUnit, ((x, u), (y, u)) ∈ f.rel) ↔
    (x, y) ∈ ((isoOfOrderIso (X := X) (Y := prod X unit) (rightUnitOrderIso X).symm).hom ≫ f ≫
      (isoOfOrderIso (X := prod Y unit) (Y := Y) (rightUnitOrderIso Y)).hom).rel
  erw [isoOfOrderIso_hom_comp_rel, comp_isoOfOrderIso_hom_rel]
  change (∃ u : PUnit, ((x, u), (y, u)) ∈ f.rel) ↔
    ((x, PUnit.unit), (y, PUnit.unit)) ∈ f.rel
  exact ⟨fun ⟨⟨⟩, h⟩ => h, fun h => ⟨PUnit.unit, h⟩⟩

private theorem reassoc_rel {A B C D : MonRelCat.{u}}
    (f : X ⊗ (A ⊗ B) ⟶ Y ⊗ (C ⊗ D)) (s : (X × A) × B) (t : (Y × C) × D) :
    (s, t) ∈ ((α_ X A B).hom ≫ f ≫ (α_ Y C D).inv).rel ↔
      ((s.1.1, (s.1.2, s.2)), (t.1.1, (t.1.2, t.2))) ∈ f.rel := by
  change (s, t) ∈ ((isoOfOrderIso (X := prod (prod X A) B) (Y := prod X (prod A B))
      (OrderIso.prodAssoc X A B)).hom ≫ f ≫
      (isoOfOrderIso (X := prod Y (prod C D)) (Y := prod (prod Y C) D)
        (OrderIso.prodAssoc Y C D).symm).hom).rel ↔ _
  erw [isoOfOrderIso_hom_comp_rel, comp_isoOfOrderIso_hom_rel]
  rfl

/-- Closing a product is successive existential feedback. -/
theorem feedback_vanishing_tensor (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V)) :
    feedback f = feedback (feedback ((α_ X U V).hom ≫ f ≫ (α_ Y U V).inv)) := by
  apply Hom.ext
  ext ⟨x, y⟩
  change (∃ w : U × V, ((x, w), (y, w)) ∈ f.rel) ↔
    ∃ u : U, ∃ v : V, (((x, u), v), ((y, u), v)) ∈
      ((α_ X U V).hom ≫ f ≫ (α_ Y U V).inv).rel
  constructor
  · rintro ⟨⟨u, v⟩, h⟩
    exact ⟨u, v, (reassoc_rel f _ _).mpr h⟩
  · rintro ⟨u, v, h⟩
    exact ⟨(u, v), (reassoc_rel f _ _).mp h⟩

/-- An unrelated visible relation commutes with feedback. -/
theorem feedback_superposing (f : X ⊗ U ⟶ Y ⊗ U) (g : W ⟶ Z) :
    feedback ((α_ W X U).hom ≫ (g ⊗ₘ f) ≫ (α_ Z Y U).inv) = g ⊗ₘ feedback f := by
  apply Hom.ext
  ext ⟨x, y⟩
  change (∃ u : U, ((x, u), (y, u)) ∈
      ((α_ W X U).hom ≫ (g ⊗ₘ f) ≫ (α_ Z Y U).inv).rel) ↔
    (x.1, y.1) ∈ g.rel ∧ ∃ u : U, ((x.2, u), (y.2, u)) ∈ f.rel
  constructor
  · rintro ⟨u, h⟩
    have h' := (reassoc_rel (g ⊗ₘ f) _ _).mp h
    exact ⟨h'.1, u, h'.2⟩
  · rintro ⟨hg, u, hf⟩
    exact ⟨u, (reassoc_rel (g ⊗ₘ f) _ _).mpr ⟨hg, hf⟩⟩

/-- The existential symmetric trace on preorders and monotone relations. -/
def symmetricTrace : SymmetricTrace MonRelCat.{u} where
  trace := feedback
  naturality := feedback_naturality
  dinaturality := feedback_dinaturality
  vanishing_unit := feedback_vanishing_unit
  vanishing_tensor := feedback_vanishing_tensor
  superposing := feedback_superposing
  yanking := feedback_yanking
@[simp] theorem trace_rel (f : X ⊗ U ⟶ Y ⊗ U) (x : X) (y : Y) :
    (x, y) ∈ (symmetricTrace.trace f).rel ↔ ∃ a : U, ((x, a), (y, a)) ∈ f.rel := Iff.rfl

/-- Send a monotone map to its upward-closed graph. -/
def graphFunctor : Preord.{u} ⥤ MonRelCat.{u} where
  obj X := of X
  map f := graph f.hom
  map_id X := rfl
  map_comp {X Y Z} f g := by
    simpa only [Preord.hom_comp] using
      (graph_comp (X := of X) (Y := of Y) (Z := of Z) f.hom g.hom).symm

/-- The associator rebrackets an input and allows an upward output. -/
theorem associator_hom_rel_eq (X Y Z : MonRelCat.{u}) :
    (α_ X Y Z).hom.rel = {p | (p.1.1.1, (p.1.1.2, p.1.2)) ≤ p.2} := rfl

theorem associator_inv_rel_eq (X Y Z : MonRelCat.{u}) :
    (α_ X Y Z).inv.rel = {p | ((p.1.1, p.1.2.1), p.1.2.2) ≤ p.2} := rfl

/-- The braiding is the upward-closed graph of the swap. -/
theorem braiding_hom_rel_eq (X Y : MonRelCat.{u}) :
    (β_ X Y).hom.rel = {p | p.1.swap ≤ p.2} := rfl

theorem leftUnitor_hom_rel_eq (X : MonRelCat.{u}) :
    (λ_ X).hom.rel = {p | p.1.2 ≤ p.2} := rfl

theorem leftUnitor_inv_rel_eq (X : MonRelCat.{u}) :
    (λ_ X).inv.rel = {p | (PUnit.unit, p.1) ≤ p.2} := rfl

theorem rightUnitor_hom_rel_eq (X : MonRelCat.{u}) :
    (ρ_ X).hom.rel = {p | p.1.1 ≤ p.2} := rfl

theorem rightUnitor_inv_rel_eq (X : MonRelCat.{u}) :
    (ρ_ X).inv.rel = {p | (p.1, PUnit.unit) ≤ p.2} := rfl

theorem whiskerLeft_rel_eq (X : MonRelCat.{u}) (f : Y ⟶ Z) :
    (X ◁ f).rel = {p | p.1.1 ≤ p.2.1 ∧ (p.1.2, p.2.2) ∈ f.rel} := rfl

theorem whiskerRight_rel_eq (f : X ⟶ Y) (Z : MonRelCat.{u}) :
    (f ▷ Z).rel = {p | (p.1.1, p.2.1) ∈ f.rel ∧ p.1.2 ≤ p.2.2} := rfl

/-- Membership in the associator is coordinatewise order after rebracketing. -/
@[simp] theorem associator_hom_rel (X Y Z : MonRelCat.{u})
    (s : (X × Y) × Z) (t : X × (Y × Z)) :
    (s, t) ∈ (α_ X Y Z).hom.rel ↔ s.1.1 ≤ t.1 ∧ s.1.2 ≤ t.2.1 ∧ s.2 ≤ t.2.2 := Iff.rfl

@[simp] theorem braiding_hom_rel (X Y : MonRelCat.{u}) (s : X × Y) (t : Y × X) :
    (s, t) ∈ (β_ X Y).hom.rel ↔ s.2 ≤ t.1 ∧ s.1 ≤ t.2 := Iff.rfl

@[simp] theorem leftUnitor_hom_rel (X : MonRelCat.{u}) (s : PUnit × X) (t : X) :
    (s, t) ∈ (λ_ X).hom.rel ↔ s.2 ≤ t := Iff.rfl

@[simp] theorem rightUnitor_inv_rel (X : MonRelCat.{u}) (s : X) (t : X × PUnit) :
    (s, t) ∈ (ρ_ X).inv.rel ↔ s ≤ t.1 := by
  change (s ≤ t.1 ∧ True) ↔ s ≤ t.1
  simp

end MonRelCat
end CategoryTheory
