/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Category.RelCat
public import MathlibExt.CategoryTheory.Monoidal.Traced

/-!
# The relational model of symmetric trace

Relations have a symmetric monoidal structure with product of types as tensor.
Each object is self-dual, with equality as evaluation and coevaluation. The
canonical trace is existential feedback: the same value closes both ends of
the feedback wire. No finiteness or nonemptiness assumption is required.

The tensor is the product of underlying types, not a categorical product in
`RelCat`. This concrete self-dual model instantiates the canonical trace of
Joyal, Street and Verity, Traced monoidal categories (1996), Proposition 3.1,
https://doi.org/10.1017/S0305004100074338.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u
namespace CategoryTheory.RelCat
open MonoidalCategory
open scoped MonoidalCategory SetRel

/-- An equivalence of types gives an isomorphism of relations via its graph. -/
def isoOfEquiv {X Y : RelCat.{u}} (e : X ≃ Y) : X ≅ Y where
  hom := .ofRel {p | e p.1 = p.2}
  inv := .ofRel {p | e.symm p.1 = p.2}
  hom_inv_id := by
    apply Hom.ext
    ext ⟨x, y⟩
    simp [SetRel.comp, SetRel.id, Set.mem_ofPred_eq]
  inv_hom_id := by
    apply Hom.ext
    ext ⟨x, y⟩
    simp [SetRel.comp, SetRel.id, Set.mem_ofPred_eq]

@[simp] theorem isoOfEquiv_hom_rel {X Y : RelCat.{u}} (e : X ≃ Y) (x : X) (y : Y) :
    (x, y) ∈ (isoOfEquiv e).hom.rel ↔ e x = y := Iff.rfl

/-- Product tensor on relations, with the usual rebracketing isomorphisms. -/
instance monoidalStruct : MonoidalCategoryStruct RelCat.{u} where
  tensorObj X Y := X × Y
  tensorUnit := PUnit
  tensorHom {_ _ _ _} f g := .ofRel {p | (p.1.1, p.2.1) ∈ f.rel ∧ (p.1.2, p.2.2) ∈ g.rel}
  whiskerLeft _ {_ _} f := .ofRel {p | p.1.1 = p.2.1 ∧ (p.1.2, p.2.2) ∈ f.rel}
  whiskerRight {_ _} f _ := .ofRel {p | (p.1.1, p.2.1) ∈ f.rel ∧ p.1.2 = p.2.2}
  associator X Y Z := isoOfEquiv (Equiv.prodAssoc X Y Z)
  leftUnitor X := isoOfEquiv (Equiv.punitProd X)
  rightUnitor X := isoOfEquiv (Equiv.prodPUnit X)

@[simp] theorem tensor_rel {X Y U V : RelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V)
    (x : (X ⊗ U : RelCat)) (y : (Y ⊗ V : RelCat)) :
    (x, y) ∈ (f ⊗ₘ g).rel ↔ (x.1, y.1) ∈ f.rel ∧ (x.2, y.2) ∈ g.rel := Iff.rfl

@[simp] theorem whiskerLeft_rel (X : RelCat.{u}) {Y Z : RelCat.{u}} (f : Y ⟶ Z)
    (x : (X ⊗ Y : RelCat)) (y : (X ⊗ Z : RelCat)) :
    (x, y) ∈ (X ◁ f).rel ↔ x.1 = y.1 ∧ (x.2, y.2) ∈ f.rel := Iff.rfl

@[simp] theorem whiskerRight_rel {X Y : RelCat.{u}} (f : X ⟶ Y) (Z : RelCat.{u})
    (x : (X ⊗ Z : RelCat)) (y : (Y ⊗ Z : RelCat)) :
    (x, y) ∈ (f ▷ Z).rel ↔ (x.1, y.1) ∈ f.rel ∧ x.2 = y.2 := Iff.rfl

@[simp] theorem associator_hom_rel (X Y Z : RelCat.{u}) (x : ((X ⊗ Y) ⊗ Z : RelCat))
    (y : (X ⊗ (Y ⊗ Z) : RelCat)) :
    (x, y) ∈ (α_ X Y Z).hom.rel ↔ (x.1.1, x.1.2, x.2) = y := Iff.rfl

@[simp] theorem associator_inv_rel (X Y Z : RelCat.{u}) (x : (X ⊗ (Y ⊗ Z) : RelCat))
    (y : ((X ⊗ Y) ⊗ Z : RelCat)) :
    (x, y) ∈ (α_ X Y Z).inv.rel ↔ ((x.1, x.2.1), x.2.2) = y := Iff.rfl

@[simp] theorem leftUnitor_hom_rel (X : RelCat.{u}) (x : (𝟙_ RelCat ⊗ X : RelCat)) (y : X) :
    (x, y) ∈ (λ_ X).hom.rel ↔ x.2 = y := Iff.rfl

@[simp] theorem leftUnitor_inv_rel (X : RelCat.{u}) (x : X) (y : (𝟙_ RelCat ⊗ X : RelCat)) :
    (x, y) ∈ (λ_ X).inv.rel ↔ (PUnit.unit, x) = y := Iff.rfl

@[simp] theorem rightUnitor_hom_rel (X : RelCat.{u}) (x : (X ⊗ 𝟙_ RelCat : RelCat)) (y : X) :
    (x, y) ∈ (ρ_ X).hom.rel ↔ x.1 = y := Iff.rfl

@[simp] theorem rightUnitor_inv_rel (X : RelCat.{u}) (x : X) (y : (X ⊗ 𝟙_ RelCat : RelCat)) :
    (x, y) ∈ (ρ_ X).inv.rel ↔ (x, PUnit.unit) = y := Iff.rfl

/-- Relations compose componentwise under product tensor. -/
@[implicit_reducible]
instance monoidalCategory : MonoidalCategory RelCat.{u} where
  toMonoidalCategoryStruct := monoidalStruct
  tensorHom_def := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, tensor_rel, whiskerLeft_rel,
      whiskerRight_rel]
    simp_all [tensorObj, Prod.exists]
  id_tensorHom_id := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_id_apply₂, tensor_rel]
    simp_all [tensorObj, Prod.ext_iff]
  tensorHom_comp_tensorHom := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, tensor_rel]
    simp_all [tensorObj, Prod.exists]
    aesop
  whiskerLeft_id := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_id_apply₂, whiskerLeft_rel]
    simp_all [tensorObj, Prod.ext_iff]
  id_whiskerRight := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_id_apply₂,
      whiskerRight_rel]
    simp_all [tensorObj, Prod.ext_iff]
  associator_naturality := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, tensor_rel,
       associator_hom_rel]
    simp_all [tensorObj, Prod.exists, Prod.ext_iff]
    aesop
  leftUnitor_naturality := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, whiskerLeft_rel,
        leftUnitor_hom_rel]
    simp_all [tensorObj, Prod.exists]
  rightUnitor_naturality := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂,
      whiskerRight_rel, rightUnitor_hom_rel]
    simp_all [tensorObj, Prod.exists]
  pentagon := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, whiskerLeft_rel,
      whiskerRight_rel, associator_hom_rel]
    simp_all [tensorObj, Prod.exists, Prod.ext_iff]
  triangle := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, whiskerLeft_rel,
      whiskerRight_rel, associator_hom_rel, leftUnitor_hom_rel, rightUnitor_hom_rel]
    simp_all [tensorObj]


@[simp] theorem tensorObj_def (X Y : RelCat.{u}) : X ⊗ Y = (X × Y : RelCat) := rfl

@[simp] theorem tensorUnit_def : 𝟙_ RelCat.{u} = (PUnit : RelCat) := rfl

@[simp] theorem swapIso_rel (X Y : RelCat.{u})
    (x : (X ⊗ Y : RelCat)) (y : (Y ⊗ X : RelCat)) :
    (x, y) ∈ (isoOfEquiv (Equiv.prodComm X Y)).hom.rel ↔ x.swap = y := Iff.rfl

/-- The symmetry exchanges the two components. -/
instance braidedCategory : BraidedCategory RelCat.{u} where
  braiding X Y := isoOfEquiv (Equiv.prodComm X Y)
  braiding_naturality_right := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, whiskerLeft_rel, whiskerRight_rel]
    simp [Prod.exists, Prod.ext_iff]
  braiding_naturality_left := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, whiskerLeft_rel, whiskerRight_rel]
    simp [Prod.exists, Prod.ext_iff]
    tauto
  hexagon_forward := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, whiskerLeft_rel, whiskerRight_rel,
      associator_hom_rel]
    simp [Prod.exists, Prod.ext_iff]
  hexagon_reverse := by
    intros
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, whiskerLeft_rel, whiskerRight_rel,
       associator_inv_rel]
    simp [Prod.exists, Prod.ext_iff]
    tauto

@[simp] theorem braiding_hom_rel (X Y : RelCat.{u})
    (x : (X ⊗ Y : RelCat)) (y : (Y ⊗ X : RelCat)) :
    (x, y) ∈ (β_ X Y).hom.rel ↔ x.swap = y := Iff.rfl

/-- Swapping twice is the identity relation. -/
instance symmetricCategory : SymmetricCategory RelCat.{u} where
  toBraidedCategory := braidedCategory
  symmetry X Y := by
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, Hom.rel_id_apply₂, braiding_hom_rel]
    simp [Prod.ext_iff]

/-- Equality is the cup and cap giving every relation object as its own dual. -/
@[implicit_reducible]
def exactPairing (X : RelCat.{u}) : ExactPairing X X where
  coevaluation' := .ofRel {p | p.2.1 = p.2.2}
  evaluation' := .ofRel {p | p.1.1 = p.1.2}
  coevaluation_evaluation' := by
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, whiskerLeft_rel, whiskerRight_rel,
      associator_inv_rel, leftUnitor_inv_rel, rightUnitor_hom_rel]
    simp only [tensorObj_def, tensorUnit_def, Set.mem_ofPred_eq, ↓existsAndEq, true_and,
      Prod.exists, exists_eq_right_right, exists_eq_right', exists_eq_right]
    have hy : PUnit.unit = y.1 := Subsingleton.elim (α := PUnit) _ _
    simp only [Prod.ext_iff, hy, true_and]
  evaluation_coevaluation' := by
    apply Hom.ext
    ext ⟨x, y⟩
    simp only [Hom.rel_comp_apply₂, whiskerLeft_rel, whiskerRight_rel,
      associator_hom_rel, leftUnitor_hom_rel, rightUnitor_inv_rel]
    simp only [tensorObj_def, tensorUnit_def, Set.mem_ofPred_eq, ↓existsAndEq, true_and,
      Prod.exists, exists_eq_right_right', exists_and_right, exists_eq_right]
    have hy : PUnit.unit = y.2 := Subsingleton.elim (α := PUnit) _ _
    simp only [Prod.ext_iff, hy, and_true]

@[simp] theorem coevaluation_rel (X : RelCat.{u}) (p : (𝟙_ RelCat : RelCat))
    (x : (X ⊗ X : RelCat)) :
    (p, x) ∈ (@ExactPairing.coevaluation RelCat _ _ X X (exactPairing X)).rel ↔
      x.1 = x.2 := Iff.rfl

@[simp] theorem evaluation_rel (X : RelCat.{u}) (x : (X ⊗ X : RelCat))
    (p : (𝟙_ RelCat : RelCat)) :
    (x, p) ∈ (@ExactPairing.evaluation RelCat _ _ X X (exactPairing X)).rel ↔
      x.1 = x.2 := Iff.rfl

/-- Choose each object itself as its right dual. -/
@[implicit_reducible]
instance rightRigidCategory : RightRigidCategory RelCat.{u} where
  rightDual X := { rightDual := X, exact := exactPairing X }

/-- The canonical relational trace, derived from the equality pairing. -/
def symmetricTrace : SymmetricTrace RelCat.{u} := symmetricTraceOfRigid RelCat

/-- The categorical trace closes the loop with one existentially chosen value. -/
@[simp] theorem trace_rel {X Y U : RelCat.{u}} (r : X ⊗ U ⟶ Y ⊗ U) (x : X) (y : Y) :
    (x, y) ∈ (symmetricTrace.trace r).rel ↔ ∃ z : U, ((x, z), (y, z)) ∈ r.rel := by
  let := exactPairing U
  change (x, y) ∈ (SymmetricTrace.traceOfPairing U r).rel ↔ _
  simp only [SymmetricTrace.traceOfPairing, Hom.rel_comp_apply₂, whiskerLeft_rel,
    whiskerRight_rel, associator_inv_rel, associator_hom_rel,
    rightUnitor_inv_rel, rightUnitor_hom_rel, braiding_hom_rel, coevaluation_rel, evaluation_rel]
  simp [Prod.exists, Prod.ext_iff]

/-- Tracing identity tests equality and whether a loop value exists. -/
theorem trace_id_rel (X U : RelCat.{u}) (x y : X) :
    (x, y) ∈ (symmetricTrace.trace (𝟙 (X ⊗ U))).rel ↔ x = y ∧ Nonempty U := by
  rw [trace_rel]
  simp [and_comm]

/-- Enlarging a relation enlarges its trace. -/
theorem trace_mono {X Y U : RelCat.{u}} {r s : X ⊗ U ⟶ Y ⊗ U}
    (h : r.rel ⊆ s.rel) : (symmetricTrace.trace r).rel ⊆ (symmetricTrace.trace s).rel := by
  rintro ⟨x, y⟩ hxy
  obtain ⟨z, hz⟩ := (trace_rel r x y).mp hxy
  exact (trace_rel s x y).mpr ⟨z, h hz⟩

/-- Existential feedback distributes over nondeterministic choice. -/
theorem trace_union {X Y U : RelCat.{u}} (r s : X ⊗ U ⟶ Y ⊗ U) :
    (symmetricTrace.trace (X := X) (Y := Y) (U := U) (.ofRel (r.rel ∪ s.rel))).rel =
      (symmetricTrace.trace r).rel ∪ (symmetricTrace.trace s).rel := by
  ext ⟨x, y⟩
  simp only [trace_rel, Set.mem_union]
  change (∃ z, ((x, z), (y, z)) ∈ r.rel ∨ ((x, z), (y, z)) ∈ s.rel) ↔ _
  exact exists_or

/-- For the graph of a function `f`, feedback relates `x` to `y` exactly when
`f (x, z) = (y, z)` for some hidden value `z`. -/
theorem trace_graph_rel {X Y U : RelCat.{u}} (f : X × U → Y × U) (x : X) (y : Y) :
    (x, y) ∈ (symmetricTrace.trace (X := X) (Y := Y) (U := U)
      (.ofRel f.graph)).rel ↔ ∃ z : U, f (x, z) = (y, z) := by
  rw [trace_rel]
  rfl

/-- An empty feedback object yields the empty relation. -/
theorem trace_of_isEmpty {X Y U : RelCat.{u}} [IsEmpty U] (r : X ⊗ U ⟶ Y ⊗ U) :
    (symmetricTrace.trace r).rel = ∅ := by
  ext ⟨x, y⟩
  simp

end CategoryTheory.RelCat
