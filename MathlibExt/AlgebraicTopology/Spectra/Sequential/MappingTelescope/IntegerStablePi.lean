/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Category.Grp.FilteredColimits.Successor
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.RUnitDiagonal

/-!
# The ONE original integer stable-pi functor and its actual R-unit Iso

Every integer degree uses the actual positive tail of the SAME original
varying-degree and varying-level diagonal, followed by the genuine
filtered Group colimit. All original spectrum maps, quotient classes
and stage legs are retained. The proved original R-unit diagram square
and SAME successor cofinality construct both comparison directions and
identify the entire Iso hom with the actual original R-unit pi map.
This does not identify selected-point pi-star tests with the original
Omega tests or assert arbitrary underlying weakness or a stable model.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC vC
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

private theorem originalUnitInverseHom
    {C : Type uC} [Category.{vC} C] {A B : C}
    (e : B ≅ A) (a : A ⟶ B) (h : a ≫ e.hom = 𝟙 A) : e.inv = a := by
  apply (cancel_mono e.hom).mp
  exact e.inv_hom_id.trans h.symm

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open GrpCat.FilteredColimits.Successor
open PointedCGWH.SequentialSpectrum.OrderedLoop
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.PositiveStructureGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.RUnitDiagonalGeometry
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The ONE original integer stable-pi functor uses the SAME diagonal and genuine Group colimit. -/
def integerStablePiFunctor (q : ℤ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤ GrpCat.{v} :=
  integerDiagonalDiagramFunctor q ⋙ GrpCat.FilteredColimits.colimitFunctor

/-- The entire original integer pi map is the genuine Group map of the actual diagonal map. -/
theorem integerStablePiFunctor_map (q : ℤ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (integerStablePiFunctor q).map f =
      GrpCat.FilteredColimits.colimitMap ((integerDiagonalDiagramFunctor q).map f) := rfl

/-- Every original diagonal stage keeps the same actual integer homotopy-minus-level degree. -/
theorem integerStablePi_stage_degree (q : ℤ) (n : ℕ) :
    ((integerTailPositiveIndex q + n + 1 : ℕ) : ℤ) -
      ((integerTailLevel q + n : ℕ) : ℤ) = q := integerTail_degree q n

/-- Every original integer stable-pi leg is the SAME actual chosen quotient leg. -/
def integerStablePiLeg (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (piNPositiveFunctor (integerTailPositiveIndex q + n)).obj
        (X.level (integerTailLevel q + n)) ⟶ (integerStablePiFunctor q).obj X :=
  (GrpCat.FilteredColimits.colimitCocone ((integerDiagonalDiagramFunctor q).obj X)).ι.app n

/-- ALL original stage legs preserve the actual positive homotopy function of every input map. -/
theorem integerStablePiLeg_naturality (q : ℤ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ) :
    integerStablePiLeg q X n ≫ (integerStablePiFunctor q).map f =
      (piNPositiveFunctor (integerTailPositiveIndex q + n)).map
        (PointedCGWH.SequentialSpectrum.levelMap f (integerTailLevel q + n)) ≫
          integerStablePiLeg q Y n :=
  GrpCat.FilteredColimits.colimitMap_ι ((integerDiagonalDiagramFunctor q).map f) n

/-- EVERY original integer quotient representative maps by the actual original stage function. -/
theorem integerStablePiFunctor_map_apply (q : ℤ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (n : ℕ)
    (a : piN (integerTailPositiveIndex q + n + 1) (X.level (integerTailLevel q + n))) :
    ((integerStablePiFunctor q).map f).hom
        (GrpCat.FilteredColimits.G.mk ((integerDiagonalDiagramFunctor q).obj X) ⟨n, a⟩) =
      GrpCat.FilteredColimits.G.mk ((integerDiagonalDiagramFunctor q).obj Y)
        ⟨n, piNMap (integerTailPositiveIndex q + n + 1)
          (PointedCGWH.SequentialSpectrum.levelMap f (integerTailLevel q + n)) a⟩ := by
  have h := GrpCat.FilteredColimits.colimitMap_mk
    ((integerDiagonalDiagramFunctor q).map f) n a
  exact h.trans (congrArg (fun b =>
    GrpCat.FilteredColimits.G.mk ((integerDiagonalDiagramFunctor q).obj Y) ⟨n, b⟩)
      (piNPositiveMap_apply (integerTailPositiveIndex q + n)
        (PointedCGWH.SequentialSpectrum.levelMap f (integerTailLevel q + n)) a))

/-- Both full original R-input pi comparison maps use the actual diagram and cofinal Isos. -/
def integerStablePiRInputIso (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor q).obj (functor.obj X) ≅ (integerStablePiFunctor q).obj X :=
  GrpCat.FilteredColimits.colimitFunctor.mapIso
      ((rInputDiagonalNatIso (integerTailLevel q) (integerTailPositiveIndex q)).app X) ≪≫
    successorComparisonIso ((integerDiagonalDiagramFunctor q).obj X)

/-- The ENTIRE original R-input pi hom retains the actual diagonal hom and successor hom. -/
theorem integerStablePiRInputIso_hom (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiRInputIso q X).hom =
      GrpCat.FilteredColimits.colimitMap
          ((rInputDiagonalNatIso (integerTailLevel q) (integerTailPositiveIndex q)).hom.app X) ≫
        (successorComparisonIso ((integerDiagonalDiagramFunctor q).obj X)).hom := rfl

/-- The ENTIRE original R-input pi inv retains the actual successor inv and diagonal inv. -/
theorem integerStablePiRInputIso_inv (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiRInputIso q X).inv =
      (successorComparisonIso ((integerDiagonalDiagramFunctor q).obj X)).inv ≫
        GrpCat.FilteredColimits.colimitMap
          ((rInputDiagonalNatIso (integerTailLevel q) (integerTailPositiveIndex q)).inv.app X) :=
  rfl

/-- EVERY original R-input quotient leg keeps its actual three comparison maps and next leg. -/
theorem integerStablePiRInputIso_hom_leg (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    integerStablePiLeg q (functor.obj X) n ≫ (integerStablePiRInputIso q X).hom =
      (((rInputDiagonalNatIso (integerTailLevel q) (integerTailPositiveIndex q)).hom.app X).app
        n) ≫ integerStablePiLeg q X (n + 1) := by
  have hm := GrpCat.FilteredColimits.colimitMap_ι
    ((rInputDiagonalNatIso (integerTailLevel q) (integerTailPositiveIndex q)).hom.app X) n
  have hc := successorComparisonIso_hom_ι ((integerDiagonalDiagramFunctor q).obj X) n
  have hw := integerStablePiRInputIso_hom q X
  exact (congrArg (fun f => integerStablePiLeg q (functor.obj X) n ≫ f) hw).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫
          (successorComparisonIso ((integerDiagonalDiagramFunctor q).obj X)).hom) hm).trans
        ((Category.assoc _ _ _).trans (congrArg (fun f =>
          (((rInputDiagonalNatIso (integerTailLevel q) (integerTailPositiveIndex q)).hom.app
            X).app n) ≫ f) hc))))

/-- The entire original R-unit pi map is inverse to the SAME actual cofinal R-input comparison. -/
theorem integerStablePiRUnit_comp_hom (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor q).map (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app X) ≫
        (integerStablePiRInputIso q X).hom = 𝟙 ((integerStablePiFunctor q).obj X) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  let D := (integerDiagonalDiagramFunctor q).obj X
  let a := (integerDiagonalDiagramFunctor q).map
    (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app X)
  let b := (rInputDiagonalNatIso (integerTailLevel q) (integerTailPositiveIndex q)).hom.app X
  have h : a ≫ b = successorTransitionNatTrans.app D :=
    congr_app (rInputDiagonal_unit_transition_whole
      (integerTailLevel q) (integerTailPositiveIndex q)) X
  have hm : Q.map a ≫ Q.map b = Q.map (successorTransitionNatTrans.app D) :=
    (Q.map_comp a b).symm.trans (Q.congr_map h)
  rw [integerStablePiRInputIso_hom]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (successorComparisonIso D).hom) hm).trans
      (successorTransition_colimit_comp_hom D))

/-- Both actual original integer R-unit pi Iso functions use the SAME original comparison. -/
def integerStablePiRUnitIso (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor q).obj X ≅ (integerStablePiFunctor q).obj (functor.obj X) :=
  (integerStablePiRInputIso q X).symm

/-- The ENTIRE actual integer R-unit Iso hom is the literal SAME original R-unit pi map. -/
theorem integerStablePiRUnitIso_hom (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiRUnitIso q X).hom =
      (integerStablePiFunctor q).map (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app X) :=
  originalUnitInverseHom (integerStablePiRInputIso q X)
    ((integerStablePiFunctor q).map (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app X))
    (integerStablePiRUnit_comp_hom q X)

/-- The WHOLE original integer R-unit comparison retains all original spectrum input maps. -/
def integerStablePiRUnitNatIso (q : ℤ) : integerStablePiFunctor.{u, v} q ≅
    functor ⋙ integerStablePiFunctor q :=
  NatIso.ofComponents (fun X => integerStablePiRUnitIso q X) (fun f => by
    rw [integerStablePiRUnitIso_hom, integerStablePiRUnitIso_hom]
    exact (Functor.whiskerRight PointedCGWH.SequentialSpectrum.OrderedLoop.unit
      (integerStablePiFunctor q)).naturality f)

/-- The ENTIRE original integer R-unit NatIso hom equals the actual original unit map family. -/
theorem integerStablePiRUnitNatIso_hom (q : ℤ) :
    (integerStablePiRUnitNatIso.{u, v} q).hom =
      Functor.whiskerRight PointedCGWH.SequentialSpectrum.OrderedLoop.unit
        (integerStablePiFunctor q) := by
  apply NatTrans.ext
  funext X
  exact integerStablePiRUnitIso_hom q X

/-- In EVERY original integer degree the SAME original R-unit pi map is genuinely an Iso. -/
theorem integerStablePiRUnit_isIso (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    IsIso ((integerStablePiFunctor q).map
      (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app X)) :=
  (integerStablePiRUnitIso_hom q X) ▸ (integerStablePiRUnitIso q X).isIso_hom

/-- The actual selected-point integer pi-star tests use every original integer functor. -/
def integerPiStarEquivalences : MorphismProperty PointedCGWH.SequentialSpectrum.{u, v} :=
  ⨅ q : ℤ, (MorphismProperty.isomorphisms GrpCat.{v}).inverseImage (integerStablePiFunctor q)

/-- The complete actual original pi-star predicate retains each original integer map. -/
theorem integerPiStarEquivalences_iff
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    integerPiStarEquivalences f ↔ ∀ q : ℤ, IsIso ((integerStablePiFunctor q).map f) :=
  MorphismProperty.iInf_iff _ f

/-- The SAME original R-unit satisfies ALL actual original integer pi-star tests. -/
theorem rUnit_integerPiStarEquivalence (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    integerPiStarEquivalences (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app X) :=
  (integerPiStarEquivalences_iff _).mpr (fun q => integerStablePiRUnit_isIso q X)

/-- The actual original pi-star test class contains the SAME original identity arrows. -/
theorem integerPiStarEquivalences_containsIdentities :
    integerPiStarEquivalences.{u, v}.ContainsIdentities := by
  dsimp only [integerPiStarEquivalences]
  infer_instance

/-- All three two-out-of-three directions hold for the actual original integer pi-star class. -/
theorem integerPiStarEquivalences_hasTwoOutOfThreeProperty :
    integerPiStarEquivalences.{u, v}.HasTwoOutOfThreeProperty := by
  refine { toIsStableUnderComposition := ?_
           of_postcomp := ?_
           of_precomp := ?_ }
  · dsimp only [integerPiStarEquivalences]
    infer_instance
  · intro X Y Z f g hg hfg
    rw [integerPiStarEquivalences_iff] at hg hfg ⊢
    intro q
    exact ((MorphismProperty.isomorphisms GrpCat.{v}).inverseImage
      (integerStablePiFunctor q)).of_postcomp
        (W' := (MorphismProperty.isomorphisms GrpCat.{v}).inverseImage
          (integerStablePiFunctor q)) f g (hg q) (hfg q)
  · intro X Y Z f g hf hfg
    rw [integerPiStarEquivalences_iff] at hf hfg ⊢
    intro q
    exact ((MorphismProperty.isomorphisms GrpCat.{v}).inverseImage
      (integerStablePiFunctor q)).of_precomp
        (W' := (MorphismProperty.isomorphisms GrpCat.{v}).inverseImage
          (integerStablePiFunctor q)) f g (hf q) (hfg q)

/-- Actual whole Arrow retracts preserve ALL of the original integer pi-star tests. -/
theorem integerPiStarEquivalences_isStableUnderRetracts :
    integerPiStarEquivalences.{u, v}.IsStableUnderRetracts where
  of_retract h hg := by
    rw [integerPiStarEquivalences_iff] at hg ⊢
    intro q
    exact MorphismProperty.of_retract
      (P := (MorphismProperty.isomorphisms GrpCat.{v}).inverseImage
        (integerStablePiFunctor q)) h (hg q)

end PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
