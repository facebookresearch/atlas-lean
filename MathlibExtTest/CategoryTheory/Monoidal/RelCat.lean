/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import MathlibExt.CategoryTheory.Monoidal.RelCat

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory SetRel

set_option backward.isDefEq.respectTransparency false

universe u

-- Feedback uses the same value on the input and output wire.
example {X Y U : RelCat.{u}} (r : X ⊗ U ⟶ Y ⊗ U) (x : X) (y : Y) :
    x ~[(RelCat.symmetricTrace.trace r).rel] y ↔ ∃ z : U, (x, z) ~[r.rel] (y, z) :=
  RelCat.trace_rel r x y

-- Empty feedback cannot produce an output, even for identity.
example (x y : Bool) :
    ¬ x ~[(RelCat.symmetricTrace.trace (RelCat.instLargeCategory.id (Bool × PEmpty))).rel] y := by
  simp [RelCat.trace_rel]

-- Symmetry feeds back to equality, not the total relation.
example (x y : Bool) :
    x ~[(RelCat.symmetricTrace.trace (RelCat.braidedCategory.braiding Bool Bool).hom).rel] y ↔
      x = y := by
  rw [RelCat.symmetricTrace.yanking]
  rfl

-- An infinite feedback type needs no finite enumeration.
example (x y : Bool) :
    x ~[(RelCat.symmetricTrace.trace (RelCat.instLargeCategory.id (Bool × ℕ))).rel] y ↔
      x = y := by
  simp [RelCat.trace_rel]

-- A loop can choose different outputs for the same input: trace is relational.
private def chooseLoop : RelCat.Hom (Bool × Bool) (Bool × Bool) :=
  .ofRel {p | p.2.1 = p.1.2 ∧ p.2.2 = p.1.2}

example : false ~[(RelCat.symmetricTrace.trace chooseLoop).rel] false := by
  rw [RelCat.trace_rel]
  exact ⟨false, rfl, rfl⟩

example : false ~[(RelCat.symmetricTrace.trace chooseLoop).rel] true := by
  rw [RelCat.trace_rel]
  exact ⟨true, rfl, rfl⟩

-- Nonempty off-diagonal feedback edges do not count as a closed loop.
private def offDiagonal : RelCat.Hom (Bool × Bool) (Bool × Bool) :=
  .ofRel {p | p.1.2 ≠ p.2.2}

example : ((false, false), (true, true)) ∈ offDiagonal.rel := by
  change false ≠ true
  decide

example : (RelCat.symmetricTrace.trace offDiagonal).rel = ∅ := by
  ext ⟨x, y⟩
  simp [offDiagonal]

-- A deterministic update that toggles the loop has no fixed point.
example (x y : Bool) :
    ¬ (x, y) ∈ (RelCat.symmetricTrace.trace (X := Bool) (Y := Bool) (U := Bool)
      (.ofRel (Function.graph (fun p : Bool × Bool => (p.1, !p.2))))).rel := by
  rw [RelCat.trace_graph_rel]
  simp only [not_exists, Prod.mk.injEq, not_and]
  intro z _
  cases z <;> decide

-- Unit feedback simply removes its single wire.
example {X Y : RelCat.{u}} (r : X ⟶ Y) (x : X) (y : Y) :
    (x, y) ∈ (RelCat.symmetricTrace.trace (U := PUnit)
      (.ofRel {p | (p.1.1, p.2.1) ∈ r.rel})).rel ↔ (x, y) ∈ r.rel := by
  simp

-- Empty input relation remains empty, even with inhabited feedback.
example {X Y U : RelCat.{u}} :
    (RelCat.symmetricTrace.trace (X := X) (Y := Y) (U := U) (.ofRel ∅)).rel = ∅ := by
  ext ⟨x, y⟩
  simp

-- Generic monotonicity and union laws work at arbitrary universe levels.
example {X Y U : RelCat.{u}} (r s : X ⊗ U ⟶ Y ⊗ U) (h : r.rel ⊆ s.rel) :
    (RelCat.symmetricTrace.trace r).rel ⊆ (RelCat.symmetricTrace.trace s).rel :=
  RelCat.trace_mono h

example {X Y U : RelCat.{u}} (r s : X ⊗ U ⟶ Y ⊗ U) :
    (RelCat.symmetricTrace.trace (X := X) (Y := Y) (U := U) (.ofRel (r.rel ∪ s.rel))).rel =
      (RelCat.symmetricTrace.trace r).rel ∪ (RelCat.symmetricTrace.trace s).rel :=
  RelCat.trace_union r s

-- The model is an instance of the canonical rigid-category construction.
example : RelCat.symmetricTrace = symmetricTraceOfRigid RelCat := rfl

#print axioms CategoryTheory.RelCat.monoidalCategory
#print axioms CategoryTheory.RelCat.exactPairing
#print axioms CategoryTheory.RelCat.trace_rel

-- Equality self-duality must not override the reversed tensor pairing.
example (X : RelCat) [ExactPairing (C := RelCat) X X] :
    ε_ (X ⊗ X) (X ⊗ X) =
      @ExactPairing.evaluation RelCat _ _ (X ⊗ X) (X ⊗ X)
        (ExactPairing.tensor (X₁ := X) (X₂ := X) (Y₁ := X) (Y₂ := X)) := rfl

-- The chosen equality cup on a repeated product contains its diagonal.
example : (PUnit.unit, ((false, true), (false, true))) ∈
    (@ExactPairing.coevaluation RelCat _ _ (Bool × Bool) (Bool × Bool)
      (RelCat.exactPairing (Bool × Bool))).rel := by
  rfl

@[instance_reducible] private def boolTensorPairing : ExactPairing (C := RelCat) (Bool × Bool) (Bool × Bool) :=
  letI : ExactPairing (C := RelCat) Bool Bool := RelCat.exactPairing Bool
  ExactPairing.tensor (C := RelCat) (X₁ := Bool) (X₂ := Bool) (Y₁ := Bool) (Y₂ := Bool)

private theorem boolTensorPairing_coevaluation_rel (x y : Bool × Bool) :
    (PUnit.unit, (x, y)) ∈
      (@ExactPairing.coevaluation RelCat _ _ (Bool × Bool) (Bool × Bool)
        boolTensorPairing).rel ↔ x.swap = y := by
  dsimp +instances [boolTensorPairing, ExactPairing.coevaluation, ExactPairing.tensor,
    monoidalComp, RelCat.exactPairing, RelCat.monoidalCategory, RelCat.monoidalStruct,
    whiskerRightIso, whiskerLeftIso, Iso.trans, Iso.refl, Iso.symm, RelCat.isoOfEquiv,
    RelCat.Hom.ofRel, SetRel.comp, SetRel.id]
  simp [Prod.exists, Prod.ext_iff, and_comm]
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

-- The tensor cup reverses the factors, so it contains the reversed point only.
example : (PUnit.unit, ((false, true), (true, false))) ∈
    (@ExactPairing.coevaluation RelCat _ _ (Bool × Bool) (Bool × Bool)
      boolTensorPairing).rel := by
  rw [boolTensorPairing_coevaluation_rel]
  rfl

example : (PUnit.unit, ((false, true), (false, true))) ∉
    (@ExactPairing.coevaluation RelCat _ _ (Bool × Bool) (Bool × Bool)
      boolTensorPairing).rel := by
  rw [boolTensorPairing_coevaluation_rel]
  decide

-- Ordinary downstream use also works with default options and the Type tensor imported.
set_option backward.isDefEq.respectTransparency true

example : MonoidalCategory RelCat.{u} := inferInstance
example : RightRigidCategory RelCat.{u} := inferInstance
example : SymmetricCategory RelCat.{u} := inferInstance
example : MonoidalCategory (Type u) := inferInstance
example {X Y U V : RelCat.{u}} (f : X ⟶ Y) (g : U ⟶ V)
    (x : (X ⊗ U : RelCat)) (y : (Y ⊗ V : RelCat)) :
    (x, y) ∈ (f ⊗ₘ g).rel ↔ (x.1, y.1) ∈ f.rel ∧ (x.2, y.2) ∈ g.rel :=
  RelCat.tensor_rel f g x y
example {X Y U : RelCat.{u}} (r : X ⊗ U ⟶ Y ⊗ U) (x : X) (y : Y) :
    (x, y) ∈ (RelCat.symmetricTrace.trace r).rel ↔ ∃ z : U, ((x, z), (y, z)) ∈ r.rel :=
  RelCat.trace_rel r x y
