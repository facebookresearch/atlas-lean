/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntRigid
import MathlibExt.CategoryTheory.Monoidal.RelCat
import Mathlib.Algebra.Category.FGModuleCat.Basic

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [RightRigidCategory C] (T : SymmetricTrace C)

example : (IntConstruction.embedding T).IsEquivalence := inferInstance
example : Subsingleton (SymmetricTrace C) := inferInstance
example : C ≌ IntConstruction T := IntConstruction.rigidEquivalence T


open IntConstruction
open Functor.LaxMonoidal Functor.OplaxMonoidal

-- Only right duals are assumed, with an arbitrary supplied trace.
example : (embedding T).EssSurj := inferInstance
example : (rigidEquivalence T).functor.Braided := inferInstance
example : (rigidEquivalence T).inverse.Monoidal := inferInstance
example : (rigidEquivalence T).inverse.Braided := inferInstance
example : (rigidEquivalence T).IsMonoidal := inferInstance
example : NatTrans.IsMonoidal (rigidEquivalence T).unit := inferInstance
example : NatTrans.IsMonoidal (rigidEquivalence T).counit := inferInstance

example (A B : C) :
    (⟨A, B⟩ : IntConstruction T) ≅ (embedding T).obj (A ⊗ Bᘁ) :=
  representativeIso T ⟨A, B⟩
example (X : IntConstruction T) :
    (rigidEquivalence T).inverse.obj X ≅ X.positive ⊗ X.negativeᘁ :=
  rigidInverseObjIso T X

-- Both directions of the equivalence can be consumed through the standard API.
example (A : C) :
    A ≅ (rigidEquivalence T).inverse.obj ((embedding T).obj A) :=
  (rigidEquivalence T).unitIso.app A
example (X : IntConstruction T) :
    (embedding T).obj ((rigidEquivalence T).inverse.obj X) ≅ X :=
  (rigidEquivalence T).counitIso.app X
example (X Y : IntConstruction T) :
    μ (rigidEquivalence T).inverse X Y ≫ (rigidEquivalence T).inverse.map (β_ X Y).hom =
      (β_ _ _).hom ≫ μ (rigidEquivalence T).inverse Y X :=
  Functor.LaxBraided.braided X Y

example (S : SymmetricTrace C) : T = S := Subsingleton.elim _ _
example {A B U : C} (f : A ⊗ U ⟶ B ⊗ U) :
    T.trace f = (symmetricTraceOfRigid C).trace f := T.trace_eq_of_rigid f
example {X Y U : IntConstruction T} (f : X ⊗ U ⟶ Y ⊗ U) :
    (rigidEquivalence T).inverse.map ((symmetricTraceOfRigid (IntConstruction T)).trace f) =
      (symmetricTraceOfRigid C).trace
        (μ (rigidEquivalence T).inverse X U ≫ (rigidEquivalence T).inverse.map f ≫
          δ (rigidEquivalence T).inverse Y U) := rigidInverse_preserves_trace T f

-- Relational feedback includes the empty object; no nonemptiness is needed.
example (S : SymmetricTrace RelCat) {X Y U : RelCat} (r : X ⊗ U ⟶ Y ⊗ U)
    (x : X) (y : Y) : (x, y) ∈ (S.trace r).rel ↔ ∃ u : U, ((x, u), (y, u)) ∈ r.rel := by
  have h : S = RelCat.symmetricTrace := Subsingleton.elim _ _
  rw [h]
  exact RelCat.trace_rel r x y
example (S : SymmetricTrace RelCat) {X Y U : RelCat} [IsEmpty U]
    (r : X ⊗ U ⟶ Y ⊗ U) : (S.trace r).rel = ∅ := by
  have h : S = RelCat.symmetricTrace := Subsingleton.elim _ _
  rw [h]
  exact RelCat.trace_of_isEmpty r

-- A concrete linear category also recovers arbitrary, possibly zero, pairs.
example (A B : FGModuleCat ℚ) :
    (⟨A, B⟩ : IntConstruction (symmetricTraceOfRigid (FGModuleCat ℚ))) ≅
      (embedding (symmetricTraceOfRigid (FGModuleCat ℚ))).obj (A ⊗ Bᘁ) :=
  representativeIso _ _
example (S : SymmetricTrace (FGModuleCat ℚ)) (X Y U : FGModuleCat ℚ) :
    S.trace (0 : X ⊗ U ⟶ Y ⊗ U) = 0 := by
  rw [S.trace_eq_of_rigid]
  simp [symmetricTraceOfRigid, SymmetricTrace.traceOfPairing]
