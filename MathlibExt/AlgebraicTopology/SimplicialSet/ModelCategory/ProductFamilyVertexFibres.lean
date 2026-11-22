/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanFibrationVertexWeakRecognition

/-!
# Full original product families and their actual vertex fibres

The graph of a complete map `X ⊗ A ⟶ Y` retains its entire parameter
coordinate. Its literal strict fibre map is identified with restriction
to the same parameter vertex, through explicit isomorphisms retaining
both product projections and both inverse equations.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.ProductFamilyVertexFibres

variable {X Y A : SSet.{u}}

/-- The SAME whole parameter family with its original parameter coordinate retained. -/
def graph (h : X ⊗ A ⟶ Y) : X ⊗ A ⟶ Y ⊗ A := lift h (snd X A)

/-- Its first projection is the entire supplied original family. -/
@[reassoc]
lemma graph_fst (h : X ⊗ A ⟶ Y) : graph h ≫ fst Y A = h := lift_fst _ _

/-- Its second projection is the SAME entire parameter projection. -/
@[reassoc]
lemma graph_snd (h : X ⊗ A ⟶ Y) : graph h ≫ snd Y A = snd X A := lift_snd _ _

/-- Insert the original parameter vertex as its full constant simplex in every degree. -/
def sectionAt (X : SSet.{u}) (a : A _⦋0⦌) : X ⟶ X ⊗ A := lift (𝟙 X) (SSet.const a)

@[reassoc]
lemma sectionAt_fst (a : A _⦋0⦌) : sectionAt X a ≫ fst X A = 𝟙 X := lift_fst _ _

@[reassoc]
lemma sectionAt_snd (a : A _⦋0⦌) : sectionAt X a ≫ snd X A = SSet.const a := lift_snd _ _

/-- Restrict the SAME complete family to the original parameter vertex. -/
def vertexAction (h : X ⊗ A ⟶ Y) (a : A _⦋0⦌) : X ⟶ Y := sectionAt X a ≫ h

/-- Full product-fibre presentation with its original inclusion and both inverses. -/
def fibreIso (X : SSet.{u}) (a : A _⦋0⦌) :
    X ≅ (Subcomplex.fiber (snd X A) a : SSet.{u}) where
  hom := Subcomplex.lift (sectionAt X a) (by
    rw [Subcomplex.range_le_fiber_iff]
    exact sectionAt_snd a)
  inv := (Subcomplex.fiber (snd X A) a).ι ≫ fst X A
  hom_inv_id := by
    rw [← Category.assoc, Subcomplex.lift_ι, sectionAt_fst]
  inv_hom_id := by
    apply (cancel_mono (Subcomplex.fiber (snd X A) a).ι).mp
    simp only [Category.assoc, Subcomplex.lift_ι, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, sectionAt_fst, Category.comp_id]
    · simp only [Category.assoc, sectionAt_snd, SSet.comp_const, Subcomplex.fiber_ι_comp]

/-- The forward isomorphism retains the entire original constant-parameter section. -/
@[reassoc]
lemma fibreIso_hom_ι (a : A _⦋0⦌) :
    (fibreIso X a).hom ≫ (Subcomplex.fiber (snd X A) a).ι = sectionAt X a :=
  rfl

/-- The inverse retains the entire original first projection. -/
lemma fibreIso_inv (a : A _⦋0⦌) :
    (fibreIso X a).inv = (Subcomplex.fiber (snd X A) a).ι ≫ fst X A := rfl

/-- The SAME original full strict fibre map of the graph family. -/
def fibreMap (h : X ⊗ A ⟶ Y) (a : A _⦋0⦌) :
    (Subcomplex.fiber (snd X A) a : SSet.{u}) ⟶ (Subcomplex.fiber (snd Y A) a : SSet.{u}) :=
  Subcomplex.mapFiber (graph h) (𝟙 A) (by rw [graph_snd, Category.comp_id])
    (y := a) (y' := a) rfl

/-- The full actual fibre comparison is the SAME original restricted action. -/
lemma fibreMap_comparison (h : X ⊗ A ⟶ Y) (a : A _⦋0⦌) :
    (fibreIso X a).hom ≫ fibreMap h a = vertexAction h a ≫ (fibreIso Y a).hom := by
  apply (cancel_mono (Subcomplex.fiber (snd Y A) a).ι).mp
  simp only [fibreMap, Category.assoc, Subcomplex.mapFiber_ι, fibreIso_hom_ι_assoc,
    fibreIso_hom_ι]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, graph_fst, sectionAt_fst, Category.comp_id, vertexAction]
  · rw [Category.assoc, graph_snd, sectionAt_snd, Category.assoc, sectionAt_snd, SSet.comp_const]

/-- The actual original full fibre map is weak exactly when its SAME
complete original vertex action is weak. -/
theorem fibreMap_weak_iff (h : X ⊗ A ⟶ Y) (a : A _⦋0⦌) :
    realizationWeakEquivalences (fibreMap h a) ↔ realizationWeakEquivalences (vertexAction h a) :=
  (realizationWeakEquivalences.arrow_mk_iso_iff
    (Arrow.isoMk' (vertexAction h a) (fibreMap h a) (fibreIso X a) (fibreIso Y a)
      (fibreMap_comparison h a))).symm

/-- The SAME original tensor projection is an actual Kan fibration when
its original coefficient is Kan. -/
theorem fibration_snd (X A : SSet.{u}) [IsFibrant X] : Fibration (snd X A) := by
  let _ : (fibrations SSet.{u}).IsStableUnderBaseChange := by
    rw [SSet.modelCategoryQuillen.fibrations_eq]
    infer_instance
  rw [fibration_iff]
  exact (fibrations SSet.{u}).of_isPullback
    (IsPullback.of_is_product' (tensorProductIsBinaryProduct X A) terminalIsTerminal)
    ((fibration_iff _).mp (inferInstance : Fibration (terminal.from X)))

/-- Weakness of EVERY original vertex action detects the SAME entire
original graph map over its complete Kan parameter. -/
theorem graph_weak_of_vertexActions (h : X ⊗ A ⟶ Y)
    [IsFibrant X] [IsFibrant Y] [IsFibrant A]
    (hV : ∀ a : A _⦋0⦌, realizationWeakEquivalences (vertexAction h a)) :
    realizationWeakEquivalences (graph h) := by
  let _ : Fibration (snd X A) := fibration_snd X A
  let _ : Fibration (snd Y A) := fibration_snd Y A
  apply KanFibrationVertexWeakRecognition.realizationWeakEquivalences_of_vertexFibers
    (snd X A) (snd Y A) (graph h) (graph_snd h)
  intro a
  exact (fibreMap_weak_iff h a).mpr (hV a)

end SSet.ProductFamilyVertexFibres
