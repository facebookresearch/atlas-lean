/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.Transport
public import MathlibExt.CategoryTheory.Enriched.ModuleMappingRSourceContext

/-!
# Source mapping-end closed transport

The original source right adjoints and chosen adjunction families transport
through an arbitrary equivalence, retaining both Hom functions and triangles.
-/

@[expose] public section

section OriginalSourceClosed

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D]
  (E : C ≌ D) (R : C → C ⥤ C)

/-- The whole original source right adjoint, restricted and reconstructed by the same E. -/
def mappingFunctor (X : D) : D ⥤ D :=
  E.inverse ⋙ R (E.inverse.obj X) ⋙ E.functor

omit [MonoidalCategory C] in
/-- Every entire target map is the actual source map followed by original reconstruction. -/
theorem mappingFunctor_map (X : D) {Y Z : D} (g : Y ⟶ Z) :
    (mappingFunctor E R X).map g =
      E.functor.map ((R (E.inverse.obj X)).map (E.inverse.map g)) := rfl

/-- Compose the two actual E adjunctions with the original source tensor adjunction. -/
def adjunction (h : ∀ M : C, tensorLeft M ⊣ R M) (X : D) :
    letI := Monoidal.transport E
    tensorLeft X ⊣ mappingFunctor E R X := by
  letI := Monoidal.transport E
  exact ((E.symm.toAdjunction.comp (h (E.inverse.obj X))).comp E.toAdjunction)

/-- Closedness chooses the original entire source right adjoint in the transported tensor. -/
@[instance_reducible]
def monoidalClosed (h : ∀ M : C, tensorLeft M ⊣ R M) :
    letI := Monoidal.transport E
    MonoidalClosed D := by
  letI : MonoidalClosed C := { closed M := { rightAdj := R M, adj := h M } }
  exact inferInstanceAs (MonoidalClosed (Monoidal.Transported E))

/-- The complete chosen right-adjoint functor is the original restricted source functor. -/
theorem monoidalClosed_ihom (h : ∀ M : C, tensorLeft M ⊣ R M) (X : D) :
    letI := Monoidal.transport E
    letI := monoidalClosed E R h
    ihom X = E.inverse ⋙ R (E.inverse.obj X) ⋙ E.functor := rfl

/-- The canonical closed transport retains the entire original source/E adjunction record. -/
theorem monoidalClosed_adjunction (h : ∀ M : C, tensorLeft M ⊣ R M) (X : D) :
    letI := Monoidal.transport E
    letI := monoidalClosed E R h
    ihom.adjunction X = adjunction E R h X := by
  let : MonoidalClosed C := { closed M := { rightAdj := R M, adj := h M } }
  let := Monoidal.transport E
  let := monoidalClosed E R h
  let : E.inverse.Monoidal :=
    inferInstanceAs (Monoidal.equivalenceTransported E).inverse.Monoidal
  change ((E.symm.toAdjunction.comp ((h (E.inverse.obj X)).comp
    E.symm.toAdjunction.toEquivalence.symm.toAdjunction)).ofNatIsoLeft
      (Iso.compInverseIso (H := E.symm.toAdjunction.toEquivalence)
        (Functor.Monoidal.commTensorLeft E.inverse X))) = _
  have tensorator_eq (Y : D) :
      Functor.LaxMonoidal.μ E.inverse X Y =
        E.unit.app (E.inverse.obj X ⊗ E.inverse.obj Y) := rfl
  have comparison_eq :
      Iso.compInverseIso (H := E.symm.toAdjunction.toEquivalence)
        (Functor.Monoidal.commTensorLeft E.inverse X) =
      Iso.refl (E.inverse ⋙ tensorLeft (E.inverse.obj X) ⋙ E.functor) := by
    ext Y
    simp only [Iso.compInverseIso_hom_app, Functor.Monoidal.commTensorLeft_hom_app,
      Iso.refl_hom, NatTrans.id_app]
    change E.functor.map (Functor.LaxMonoidal.μ E.inverse X Y) ≫
      inv (E.counitInv.app (E.functor.obj (E.inverse.obj X ⊗ E.inverse.obj Y))) =
        𝟙 (E.functor.obj (E.inverse.obj X ⊗ E.inverse.obj Y))
    rw [tensorator_eq]
    simp
  have reflAdj (F G : D ⥤ D) (adj : F ⊣ G) : adj.ofNatIsoLeft (Iso.refl F) = adj := by
    apply Adjunction.ext
    simp only [Adjunction.ofNatIsoLeft, Iso.refl_hom, Functor.whiskerRight_id', Category.comp_id]
  have reconstructedAdjunction_eq :
      E.symm.toAdjunction.toEquivalence.symm.toAdjunction = E.toAdjunction := by
    apply Adjunction.ext
    ext Y
    simp [Equivalence.toAdjunction, Adjunction.toEquivalence]
  rw [reconstructedAdjunction_eq, comparison_eq]
  refine (reflAdj _ _
    (E.symm.toAdjunction.comp ((h (E.inverse.obj X)).comp E.toAdjunction))).trans ?_
  apply Adjunction.ext
  ext Y
  simp only [adjunction, Adjunction.comp_unit_app, Functor.comp_obj,
    Functor.map_comp, Category.assoc]
  rfl

/-- The entire Hom correspondence is the composite of the three original Hom correspondences. -/
theorem homEquiv_apply (h : ∀ M : C, tensorLeft M ⊣ R M)
    (X Y Z : D) :
    letI := Monoidal.transport E
    ∀ f : X ⊗ Y ⟶ Z,
      (adjunction E R h X).homEquiv Y Z f =
        (E.symm.toAdjunction.homEquiv Y ((R (E.inverse.obj X)).obj (E.inverse.obj Z)))
          ((h (E.inverse.obj X)).homEquiv (E.inverse.obj Y) (E.inverse.obj Z)
            (E.toAdjunction.homEquiv (E.inverse.obj X ⊗ E.inverse.obj Y) Z f)) := by
  let := Monoidal.transport E
  intro f
  simp only [adjunction, Adjunction.comp_homEquiv]
  rfl

/-- The full inverse Hom correspondence
keeps both inverse E correspondences and the source inverse. -/
theorem homEquiv_symm_apply (h : ∀ M : C, tensorLeft M ⊣ R M)
    (X Y Z : D) :
    letI := Monoidal.transport E
    ∀ g : Y ⟶ (mappingFunctor E R X).obj Z,
      ((adjunction E R h X).homEquiv Y Z).symm g =
        (E.toAdjunction.homEquiv (E.inverse.obj X ⊗ E.inverse.obj Y) Z).symm
          (((h (E.inverse.obj X)).homEquiv (E.inverse.obj Y) (E.inverse.obj Z)).symm
            ((E.symm.toAdjunction.homEquiv Y
              ((R (E.inverse.obj X)).obj (E.inverse.obj Z))).symm g)) := by
  let := Monoidal.transport E
  intro g
  simp only [adjunction, Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  rfl

/-- The whole canonical unit retains the original inverse-E unit, source unit and forward-E unit. -/
theorem unit_app (h : ∀ M : C, tensorLeft M ⊣ R M) (X Y : D) :
    letI := Monoidal.transport E
    (adjunction E R h X).unit.app Y =
      E.symm.toAdjunction.unit.app Y ≫
        E.functor.map ((h (E.inverse.obj X)).unit.app (E.inverse.obj Y)) ≫
          E.functor.map ((R (E.inverse.obj X)).map
            (E.toAdjunction.unit.app (E.inverse.obj X ⊗ E.inverse.obj Y))) := by
  let := Monoidal.transport E
  simp only [adjunction, Adjunction.comp_unit_app, Functor.comp_obj, Functor.comp_map,
    Category.assoc]
  rfl

/-- The entire canonical evaluation retains both original E counits and the source evaluation. -/
theorem counit_app (h : ∀ M : C, tensorLeft M ⊣ R M) (X Z : D) :
    letI := Monoidal.transport E
    (adjunction E R h X).counit.app Z =
      E.functor.map ((tensorLeft (E.inverse.obj X)).map
        (E.symm.toAdjunction.counit.app
          ((R (E.inverse.obj X)).obj (E.inverse.obj Z))) ≫
            (h (E.inverse.obj X)).counit.app (E.inverse.obj Z)) ≫
        E.toAdjunction.counit.app Z := by
  let := Monoidal.transport E
  simp only [adjunction, Adjunction.comp_counit_app, Functor.comp_obj]

/-- The original canonical tensor/evaluation triangle is retained at every source object. -/
theorem left_triangle (h : ∀ M : C, tensorLeft M ⊣ R M) (X Y : D) :
    letI := Monoidal.transport E
    (tensorLeft X).map ((adjunction E R h X).unit.app Y) ≫
      (adjunction E R h X).counit.app ((tensorLeft X).obj Y) =
        𝟙 ((tensorLeft X).obj Y) := by
  let := Monoidal.transport E
  exact (adjunction E R h X).left_triangle_components Y

/-- The original canonical function/coevaluation triangle
retains the entire source right functor. -/
theorem right_triangle (h : ∀ M : C, tensorLeft M ⊣ R M) (X Z : D) :
    letI := Monoidal.transport E
    (adjunction E R h X).unit.app ((mappingFunctor E R X).obj Z) ≫
      (mappingFunctor E R X).map ((adjunction E R h X).counit.app Z) =
        𝟙 ((mappingFunctor E R X).obj Z) := by
  let := Monoidal.transport E
  exact (adjunction E R h X).right_triangle_components Z

end CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive

namespace CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal

universe uC vC uV vV uI vI uD vD

/-- The whole target symmetric dictionary is typed against the actual transported tensor. -/
private def SymmetricType {D : Type uD} [Category.{vD} D] (tensor : MonoidalCategory D) : Type _ :=
  letI := tensor
  SymmetricCategory D

/-- The whole original symmetric dictionary is transported before source data specialization. -/
private def transportedSymmetric {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    [SymmetricCategory C] {D : Type uD} [Category.{vD} D] (E : C ≌ D) :
    SymmetricType (Monoidal.transport E) :=
  inferInstanceAs (SymmetricCategory (Monoidal.Transported E))

open EnrichedDayKernel
attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] Enriched.SphereModuleMappingEnd.moduleCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (B : EnrichedFunctor.LaxBraidedData L)

section SourceFactories

attribute [local irreducible] Closed.monoidalClosed
set_option backward.isDefEq.respectTransparency true

/-- The whole selected module tensor is the actual source tensor, from genuine Day preservation. -/
theorem moduleMonoidal_eq :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
    letI : ∀ X : EnrichedFunctorCat V I,
        PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
      (Closed.smallTensorPreservationFamilies d b).1
    letI : ∀ X : EnrichedFunctorCat V I,
        PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
      (Closed.smallTensorPreservationFamilies d b).2
    RightModuleFree.tensorMonoidal (⟨S⟩ : EnrichedFunctorCat V I) =
      Enriched.ModuleMappingR.moduleMonoidal d b S L B := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (Closed.smallTensorPreservationFamilies d b).1
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    (Closed.smallTensorPreservationFamilies d b).2
  rfl

end SourceFactories

variable {D : Type uD} [Category.{vD} D]

/-- The entire canonical adjunction uses the literal source equalizer on the selected tensor. -/
def adjunctionFromSource
    (E : Enriched.ModuleMappingR.Module d S L ≌ D) (X : D) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
    letI := Enriched.ModuleMappingR.moduleMonoidal d b S L B
    letI := Monoidal.transport E
    tensorLeft X ⊣
      Primitive.mappingFunctor E (Enriched.ModuleMappingR.functor d b S L B) X := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  letI := Enriched.ModuleMappingR.moduleMonoidal d b S L B
  exact Primitive.adjunction E (Enriched.ModuleMappingR.functor d b S L B)
    (Enriched.ModuleMappingR.leftAdjunction d b S L B) X

/-- Construct the canonical closed tensor from the actual source/E maps and genuine source end. -/
@[instance_reducible]
def fromSource
    (E : Enriched.ModuleMappingR.Module d S L ≌ D) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := BraidingMonoidal.symmetricCategory d b
    letI := LaxMonoid.monObj d S L
    letI := LaxMonoid.isCommMonObj d b S L B
    letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
    letI := Enriched.ModuleMappingR.moduleMonoidal d b S L B
    letI := Monoidal.transport E
    MonoidalClosed D := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  letI := Enriched.ModuleMappingR.moduleMonoidal d b S L B
  letI := Enriched.ModuleMappingR.moduleClosed d b S L B
  exact Primitive.monoidalClosed E (fun M => ihom M) (fun M => ihom.adjunction M)

/-- The complete original adjunction function type keeps both E adjunctions and the full source
right adjoint. -/
def AdjunctionFamily
    (E : Enriched.ModuleMappingR.Module d S L ≌ D) : Type _ :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  letI := Enriched.ModuleMappingR.moduleMonoidal d b S L B
  letI := Monoidal.transport E
  ∀ (X : D), tensorLeft X ⊣
    Primitive.mappingFunctor E (Enriched.ModuleMappingR.functor d b S L B) X

/-- The original complete source/E composite is supplied before native data specialization. -/
def completeAdjunctionFromSource
    (E : Enriched.ModuleMappingR.Module d S L ≌ D) :
    AdjunctionFamily d b S L B E := by
  intro X
  exact adjunctionFromSource d b S L B E X

/-- Equality of the entire chosen adjunction records, retaining the actual closed dictionary and
full maps. -/
def IhomAdjunctionFormula
    (E : Enriched.ModuleMappingR.Module d S L ≌ D) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  letI := Enriched.ModuleMappingR.moduleMonoidal d b S L B
  letI := Monoidal.transport E
  letI := fromSource d b S L B E
  ∀ (X : D), ihom.adjunction X = completeAdjunctionFromSource d b S L B E X

/-- The chosen full closed adjunction is the exact original source/E composite as a whole record. -/
theorem ihomAdjunctionFromSource
    (E : Enriched.ModuleMappingR.Module d S L ≌ D) :
    IhomAdjunctionFormula d b S L B E := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let := Enriched.ModuleMappingR.moduleMonoidal d b S L B
  let := Monoidal.transport E
  let := fromSource d b S L B E
  intro X
  exact Primitive.monoidalClosed_adjunction E (Enriched.ModuleMappingR.functor d b S L B)
    (Enriched.ModuleMappingR.leftAdjunction d b S L B) X

/-- The entire original left tensor preserves every original small colimit shape. -/
def TensorLeftPreservesFamily
    (E : Enriched.ModuleMappingR.Module d S L ≌ D) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  letI := Enriched.ModuleMappingR.moduleMonoidal d b S L B
  letI := Monoidal.transport E
  ∀ (X : D), PreservesColimitsOfSize.{0, 0} (tensorLeft X)

/-- Preservation follows from the full original source/E composite adjunction. -/
theorem tensorLeftPreservesFromSource
    (E : Enriched.ModuleMappingR.Module d S L ≌ D) :
    TensorLeftPreservesFamily d b S L B E := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let := Enriched.ModuleMappingR.moduleMonoidal d b S L B
  let := Monoidal.transport E
  intro X
  exact (adjunctionFromSource d b S L B E X).leftAdjoint_preservesColimits

/-- The complete original right tensor preserves the same entire small colimit family. -/
def TensorRightPreservesFamily
    (E : Enriched.ModuleMappingR.Module d S L ≌ D) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := LaxMonoid.monObj d S L
  letI := LaxMonoid.isCommMonObj d b S L B
  letI : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  letI := Enriched.ModuleMappingR.moduleMonoidal d b S L B
  letI := Monoidal.transport E
  ∀ (X : D), PreservesColimitsOfSize.{0, 0} (tensorRight X)

/-- The original full source symmetry and braid preserve colimits in the other orientation. -/
theorem tensorRightPreservesFromSource
    (E : Enriched.ModuleMappingR.Module d S L ≌ D) :
    TensorRightPreservesFamily d b S L B E := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := LaxMonoid.monObj d S L
  let := LaxMonoid.isCommMonObj d b S L B
  let : HasCoequalizers (EnrichedFunctorCat V I) := inferInstance
  let := Enriched.ModuleMappingR.moduleMonoidal d b S L B
  let := Enriched.ModuleMappingR.moduleSymmetric d b S L B
  let := Monoidal.transport E
  let : SymmetricCategory D := transportedSymmetric E
  intro X
  exact ((adjunctionFromSource d b S L B E X).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight X)).leftAdjoint_preservesColimits

end CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Internal

namespace CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected

universe uV vV uI vI uD vD
open EnrichedDayKernel
attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] Enriched.SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  {q : Enriched.ModuleMappingR.SelectedSource V I}
  {D : Type uD} [Category.{vD} D]

/-- The full closed-structure type is written against the actual typed source transport. -/
abbrev ClosedStructureType (c : ModuleMappingR.SourceContext q D) : Type _ :=
  letI := c.monoidalCategory
  MonoidalClosed D

/-- The source chooses its full Mapping_R, then uses Mathlib's canonical closed transport. -/
@[instance_reducible]
def monoidalClosed (c : ModuleMappingR.SourceContext q D) : ClosedStructureType c := by
  letI := q.moduleMonoidal
  letI := q.moduleClosed
  exact Primitive.monoidalClosed c.equivalence (fun M => ihom M) (fun M => ihom.adjunction M)

/-- The entire source Mapping_R functor is restricted and reconstructed by the same two functors. -/
def mappingFunctor (c : ModuleMappingR.SourceContext q D) (X : D) : D ⥤ D :=
  letI := q.moduleMonoidal
  Primitive.mappingFunctor c.equivalence q.mappingFunctor X

/-- The complete original adjunction family is independently written for every target object. -/
def AdjunctionFamily (c : ModuleMappingR.SourceContext q D) : Type _ :=
  letI := c.monoidalCategory
  ∀ (X : D), tensorLeft X ⊣ mappingFunctor c X

/-- Both original equivalence adjunctions compose with the whole selected source adjunction. -/
def adjunction (c : ModuleMappingR.SourceContext q D) : AdjunctionFamily c := by
  letI := q.moduleMonoidal
  intro X
  exact Primitive.adjunction c.equivalence q.mappingFunctor q.leftAdjunction X

/-- The chosen full internal Hom is exactly the original reconstructed Mapping_R. -/
theorem ihom (c : ModuleMappingR.SourceContext q D) (X : D) :
    letI := c.monoidalCategory
    letI := monoidalClosed c
    CategoryTheory.ihom X = mappingFunctor c X := rfl

/-- The full homogeneous Eq compares the entire chosen and original source/E adjunction records. -/
def IhomAdjunctionFormula (c : ModuleMappingR.SourceContext q D) : Prop :=
  letI := c.monoidalCategory
  letI := monoidalClosed c
  ∀ (X : D), CategoryTheory.ihom.adjunction X = adjunction c X

/-- The canonical transported choice is the entire original source/E composite record. -/
theorem ihomAdjunction (c : ModuleMappingR.SourceContext q D) : IhomAdjunctionFormula c := by
  let := q.moduleMonoidal
  let := c.monoidalCategory
  let := monoidalClosed c
  intro X
  exact Primitive.monoidalClosed_adjunction c.equivalence q.mappingFunctor q.leftAdjunction X

/-- The entire left tensor preserves all original small colimit shapes at every target object. -/
def TensorLeftPreservesFamily (c : ModuleMappingR.SourceContext q D) : Prop :=
  letI := c.monoidalCategory
  ∀ (X : D), PreservesColimitsOfSize.{0, 0} (tensorLeft X)

/-- The full original adjunction proves left tensor preservation before native specialization. -/
theorem tensorLeftPreserves (c : ModuleMappingR.SourceContext q D) :
    TensorLeftPreservesFamily c := by
  let := c.monoidalCategory
  intro X
  exact (adjunction c X).leftAdjoint_preservesColimits

/-- The entire right tensor preserves the same original small colimit family. -/
def TensorRightPreservesFamily (c : ModuleMappingR.SourceContext q D) : Prop :=
  letI := c.monoidalCategory
  ∀ (X : D), PreservesColimitsOfSize.{0, 0} (tensorRight X)

/-- The same original full symmetry and adjunction prove the right tensor family. -/
theorem tensorRightPreserves (c : ModuleMappingR.SourceContext q D) :
    TensorRightPreservesFamily c := by
  let := c.monoidalCategory
  let := c.symmetricCategory
  intro X
  exact ((adjunction c X).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight X)).leftAdjoint_preservesColimits

end CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected


end
end OriginalSourceClosed

section OriginalSourceMappingEndAdjunctionReadbacks

set_option autoImplicit false
noncomputable section
universe u v uV vV uI vI uD vD

universe uP vP uQ vQ
namespace CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

variable {C : Type uP} [Category.{vP} C] [MonoidalCategory C]
  {D : Type uQ} [Category.{vQ} D]
  (E : C ≌ D) (R : C → C ⥤ C) (h : ∀ M : C, tensorLeft M ⊣ R M)

/-- Both complete original E Hom functions and the entire source transpose. -/
def TransposeOriginalFormula : Prop :=
  letI := Monoidal.transport E
  ∀ (X Y Z : D) (f : X ⊗ Y ⟶ Z),
    (adjunction E R h X).homEquiv Y Z f =
      (E.symm.toAdjunction.homEquiv Y ((R (E.inverse.obj X)).obj (E.inverse.obj Z)))
        ((h (E.inverse.obj X)).homEquiv (E.inverse.obj Y) (E.inverse.obj Z)
          (E.toAdjunction.homEquiv (E.inverse.obj X ⊗ E.inverse.obj Y) Z f))

theorem transposeOriginal : TransposeOriginalFormula E R h := by
  let := Monoidal.transport E
  intro X Y Z f
  exact homEquiv_apply E R h X Y Z f

/-- Both complete inverse E Hom functions and the entire original source inverse transpose. -/
def UntransposeOriginalFormula : Prop :=
  letI := Monoidal.transport E
  ∀ (X Y Z : D) (g : Y ⟶ (mappingFunctor E R X).obj Z),
    ((adjunction E R h X).homEquiv Y Z).symm g =
      (E.toAdjunction.homEquiv (E.inverse.obj X ⊗ E.inverse.obj Y) Z).symm
        (((h (E.inverse.obj X)).homEquiv (E.inverse.obj Y) (E.inverse.obj Z)).symm
          ((E.symm.toAdjunction.homEquiv Y
            ((R (E.inverse.obj X)).obj (E.inverse.obj Z))).symm g))

theorem untransposeOriginal : UntransposeOriginalFormula E R h := by
  let := Monoidal.transport E
  intro X Y Z g
  exact homEquiv_symm_apply E R h X Y Z g

/-- The entire chosen unit with both original E units and the full source unit. -/
def UnitOriginalFormula : Prop :=
  letI := Monoidal.transport E
  ∀ (X Y : D),
    (adjunction E R h X).unit.app Y =
      E.symm.toAdjunction.unit.app Y ≫
        E.functor.map ((h (E.inverse.obj X)).unit.app (E.inverse.obj Y)) ≫
          E.functor.map ((R (E.inverse.obj X)).map
            (E.toAdjunction.unit.app (E.inverse.obj X ⊗ E.inverse.obj Y)))

theorem unitOriginal : UnitOriginalFormula E R h := by
  let := Monoidal.transport E
  intro X Y
  exact unit_app E R h X Y

/-- The entire chosen counit with both original E counits and the full source evaluation. -/
def CounitOriginalFormula : Prop :=
  letI := Monoidal.transport E
  ∀ (X Z : D),
    (adjunction E R h X).counit.app Z =
      E.functor.map ((tensorLeft (E.inverse.obj X)).map
        (E.symm.toAdjunction.counit.app ((R (E.inverse.obj X)).obj (E.inverse.obj Z))) ≫
          (h (E.inverse.obj X)).counit.app (E.inverse.obj Z)) ≫
        E.toAdjunction.counit.app Z

theorem counitOriginal : CounitOriginalFormula E R h := by
  let := Monoidal.transport E
  intro X Z
  exact counit_app E R h X Z

/-- The literal full tensor triangle at every original native tensor object. -/
def LeftTriangleFormula : Prop :=
  letI := Monoidal.transport E
  ∀ (X Y : D),
    (tensorLeft X).map ((adjunction E R h X).unit.app Y) ≫
      (adjunction E R h X).counit.app (X ⊗ Y) = 𝟙 (X ⊗ Y)

theorem leftTriangle : LeftTriangleFormula E R h := by
  let := Monoidal.transport E
  intro X Y
  exact (adjunction E R h X).left_triangle_components Y

/-- The literal mapping triangle at every object of the whole original reconstructed functor. -/
def RightTriangleFormula : Prop :=
  letI := Monoidal.transport E
  ∀ (X Z : D),
    (adjunction E R h X).unit.app ((mappingFunctor E R X).obj Z) ≫
      (mappingFunctor E R X).map ((adjunction E R h X).counit.app Z) =
        𝟙 ((mappingFunctor E R X).obj Z)

theorem rightTriangle : RightTriangleFormula E R h := by
  let := Monoidal.transport E
  intro X Z
  exact (adjunction E R h X).right_triangle_components Z

end CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Primitive

namespace CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.Enriched CategoryTheory.EnrichedDayKernel
open scoped MonoidalClosed CategoryTheory.MonObj

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  {q : ModuleMappingR.SelectedSource V I}
  {D : Type uD} [Category.{vD} D]
  (c : ModuleMappingR.SourceContext q D)

/-- The selected transpose retains both E Hom correspondences and the full source transpose. -/
def TransposeOriginalFormula : Prop :=
  letI := q.moduleMonoidal
  Primitive.TransposeOriginalFormula c.equivalence q.mappingFunctor q.leftAdjunction

theorem transposeOriginal : TransposeOriginalFormula c := by
  let := q.moduleMonoidal
  exact Primitive.transposeOriginal c.equivalence q.mappingFunctor q.leftAdjunction

/-- The selected inverse transpose retains both inverse E maps and the full source inverse. -/
def UntransposeOriginalFormula : Prop :=
  letI := q.moduleMonoidal
  Primitive.UntransposeOriginalFormula c.equivalence q.mappingFunctor q.leftAdjunction

theorem untransposeOriginal : UntransposeOriginalFormula c := by
  let := q.moduleMonoidal
  exact Primitive.untransposeOriginal c.equivalence q.mappingFunctor q.leftAdjunction

/-- The selected unit retains both original E units and the complete source unit. -/
def UnitOriginalFormula : Prop :=
  letI := q.moduleMonoidal
  Primitive.UnitOriginalFormula c.equivalence q.mappingFunctor q.leftAdjunction

theorem unitOriginal : UnitOriginalFormula c := by
  let := q.moduleMonoidal
  exact Primitive.unitOriginal c.equivalence q.mappingFunctor q.leftAdjunction

/-- The selected counit retains both original E counits and the complete source evaluation. -/
def CounitOriginalFormula : Prop :=
  letI := q.moduleMonoidal
  Primitive.CounitOriginalFormula c.equivalence q.mappingFunctor q.leftAdjunction

theorem counitOriginal : CounitOriginalFormula c := by
  let := q.moduleMonoidal
  exact Primitive.counitOriginal c.equivalence q.mappingFunctor q.leftAdjunction

/-- The selected left triangle retains the full transported tensor, unit and counit. -/
def LeftTriangleFormula : Prop :=
  letI := q.moduleMonoidal
  Primitive.LeftTriangleFormula c.equivalence q.mappingFunctor q.leftAdjunction

theorem leftTriangle : LeftTriangleFormula c := by
  let := q.moduleMonoidal
  exact Primitive.leftTriangle c.equivalence q.mappingFunctor q.leftAdjunction

/-- The selected right triangle retains the full mapping functor, unit and counit. -/
def RightTriangleFormula : Prop :=
  letI := q.moduleMonoidal
  Primitive.RightTriangleFormula c.equivalence q.mappingFunctor q.leftAdjunction

theorem rightTriangle : RightTriangleFormula c := by
  let := q.moduleMonoidal
  exact Primitive.rightTriangle c.equivalence q.mappingFunctor q.leftAdjunction

end CategoryTheory.Enriched.ModuleMappingR.SourceClosed.Selected


end
end OriginalSourceMappingEndAdjunctionReadbacks
