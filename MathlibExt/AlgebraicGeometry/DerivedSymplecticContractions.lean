/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels

/-!
# Actual symmetric exterior and shifted contraction maps

The exterior-square model splits the actual skew projector of the
source-normalized tensor, up to actual degree-minus-one homotopies.
Contraction uses twice its inclusion, the actual perfect dual evaluation,
and the fixed unitors/associator/symmetry. Thus a wedge x∧y contracts
through x⊗y minus its Koszul transpose, with no hidden factor one-half.

A degree-n contraction is tested by its actual shifted postcomposition
on every representable DG Hom complex. Source-linear global de Rham
comparison and cotangent differential assembly are separate requests;
these definitions do not rename an unrelated operator as a two-form.

Reference: PTVV1111.3209v4 §§1.2 and2.2; HAGII math/0404373v7 §1.4.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open CochainComplex.HomComplex

universe u
variable {k : Type u} [CommRing k] [Algebra ℚ k]
variable {N : MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle.ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S}
    {U : RegularUnitSystem M} {X : Prestack k} {G : QCohEnhancement M U X}
    (H : CoherentMonoidalEnhancement G)

/-- The actual rational one-half scalar, retaining the source coefficient ring. -/
def halfScalar : LargeScalar k := ULift.up (algebraMap ℚ k (1 / 2 : ℚ))

/-- The actual skew projector on L⊗L for this full normalized symmetric tensor. -/
def skewProjector (L : G.category) :
    DGHom (LargeScalar k) 0 (H.monoidal.tensor.obj (L,L)) (H.monoidal.tensor.obj (L,L)) :=
  let b : DGHom (LargeScalar k) 0 (H.monoidal.tensor.obj (L,L)) (H.monoidal.tensor.obj (L,L)) :=
    dgClosedHom (LargeScalar k) (symmetry H.monoidal L L)
  halfScalar (k := k) •
    (dgId (LargeScalar k) (H.monoidal.tensor.obj (L,L)) - b)

/-- The actual exterior square is a homotopy splitting of that fixed skew projector. -/
structure ExteriorSquare (L : G.category) where
  object : G.category
  inclusion : DGHom (LargeScalar k) 0 object (H.monoidal.tensor.obj (L,L))
  inclusion_closed : inclusion ∈ dgCycles (LargeScalar k) object (H.monoidal.tensor.obj (L,L))
  projection : DGHom (LargeScalar k) 0 (H.monoidal.tensor.obj (L,L)) object
  projection_closed : projection ∈ dgCycles (LargeScalar k) (H.monoidal.tensor.obj (L,L)) object
  section_homotopy : DGHom (LargeScalar k) (-1) object object
  section_identity : dgDifferential (LargeScalar k) (-1) section_homotopy =
    dgComp (LargeScalar k) inclusion projection (by omega) - dgId (LargeScalar k) object
  projector_homotopy : DGHom (LargeScalar k) (-1)
    (H.monoidal.tensor.obj (L,L)) (H.monoidal.tensor.obj (L,L))
  projector : dgDifferential (LargeScalar k) (-1) projector_homotopy =
    dgComp (LargeScalar k) projection inclusion (by omega) - skewProjector H L

/-- The natural antisymmetrization is twice the fixed exterior-image inclusion. -/
def antisymmetrization {L : G.category} (E : ExteriorSquare H L) :
    (ForgetEnrichment.of _ E.object : Closed G) ⟶
      ForgetEnrichment.of _ (H.monoidal.tensor.obj (L,L)) :=
  dgClosedHomOf (LargeScalar k) ((2 : LargeScalar k) • E.inclusion) (by
    rw [mem_dgCycles]
    rw [map_smul, (mem_dgCycles (LargeScalar k)).mp E.inclusion_closed, smul_zero])

/-- Actual cap evaluation after tensoring with the perfect dual. -/
def contractionTarget {L : G.category} (E : ExteriorSquare H L)
    (D : PerfectDual H.monoidal L) :
    (ForgetEnrichment.of _ ((H.monoidal.nerve.fixedLeft D.object).functor.obj E.object) : Closed G) ⟶
      ForgetEnrichment.of _ L := by
  letI := H.monoidal.monoidal
  letI := H.monoidal.braided
  letI := H.monoidal.symmetric
  let l : Closed G := ForgetEnrichment.of _ L
  let t : Closed G := ForgetEnrichment.of _ D.object
  let ev : l ⊗ t ⟶ 𝟙_ (Closed G) :=
    eqToHom (H.monoidal.tensor_obj L D.object) ≫ evaluation H.monoidal D ≫
      eqToHom H.monoidal.unit_eq.symm
  exact eqToHom (congrArg (ForgetEnrichment.of _) ((H.monoidal.nerve.fixedLeft D.object).object_eq E.object)) ≫
    eqToHom (H.monoidal.tensor_obj D.object E.object).symm ≫
    (𝟙 t ⊗ₘ antisymmetrization H E) ≫
    (𝟙 t ⊗ₘ eqToHom (H.monoidal.tensor_obj L L).symm) ≫
    (α_ t l l).inv ≫ ((β_ t l).hom ⊗ₘ 𝟙 l) ≫ (ev ⊗ₘ 𝟙 l) ≫ (λ_ l).hom

/-- The true unit source of the tensor-with-dual Hom map. -/
def contractionSource {L : G.category} (D : PerfectDual H.monoidal L) :
    (ForgetEnrichment.of _ D.object : Closed G) ⟶
      ForgetEnrichment.of _ ((H.monoidal.nerve.fixedLeft D.object).functor.obj G.unit) := by
  letI := H.monoidal.monoidal
  exact (ρ_ (ForgetEnrichment.of _ D.object : Closed G)).inv ≫
    (𝟙 _ ⊗ₘ eqToHom H.monoidal.unit_eq) ≫
    eqToHom (H.monoidal.tensor_obj D.object G.unit) ≫
    eqToHom (congrArg (ForgetEnrichment.of _)
      ((H.monoidal.nerve.fixedLeft D.object).object_eq G.unit).symm)

/-- Contraction is the completed actual enriched tensor/cap composite. -/
def contractionMap {L : G.category} (E : ExteriorSquare H L)
    (D : PerfectDual H.monoidal L) :
    globalHom G E.object ⟶ dgHomComplex (LargeScalar k) D.object L :=
  (H.monoidal.nerve.fixedLeft D.object).functor.map G.unit E.object ≫
    eHomWhiskerRight (Cochains (LargeScalar k)) (contractionSource H D)
      (ForgetEnrichment.of _ ((H.monoidal.nerve.fixedLeft D.object).functor.obj E.object) : Closed G) ≫
    eHomWhiskerLeft (Cochains (LargeScalar k)) (ForgetEnrichment.of _ D.object : Closed G)
      (contractionTarget H E D)

/-- A genuine closed degree-n map induces its native shifted postcomposition on Hom. -/
def shiftedPostcomposition (P L T : G.category) (n : ℤ)
    (a : DGHom (LargeScalar k) n T L) (ha : dgDifferential (LargeScalar k) n a = 0) :
    dgHomComplex (LargeScalar k) P T ⟶ (dgHomComplex (LargeScalar k) P L)⟦n⟧ := by
  let F := cochainCorepresentable (k := LargeScalar k) (C := G.category) P
  let z := F.dgMap n a
  have hz : dgDifferential (LargeScalar k) n z = 0 := by
    rw [← F.dgMap_dgDifferential, ha, map_zero]
  refine Cocycle.equivHomShift.symm (Cocycle.mk z (n + 1) rfl ?_)
  simpa only [dgDifferential_linearHomComplex] using hz

/-- Shifted equivalence tests the actual representable complexes, not an abstract flag. -/
def IsShiftedEquivalence (L T : G.category) (n : ℤ)
    (a : DGHom (LargeScalar k) n T L) (ha : dgDifferential (LargeScalar k) n a = 0) : Prop :=
  ∀ P : G.category, QuasiIso (shiftedPostcomposition P L T n a ha)

end MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
