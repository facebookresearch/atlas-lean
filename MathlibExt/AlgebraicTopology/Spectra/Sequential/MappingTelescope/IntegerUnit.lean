/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Category.Grp.FilteredColimits.ConstantSource
import MathlibExt.Algebra.Category.Grp.FilteredColimits.PointwiseComparison
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.StageIntegerStablePi

/-!
# The SAME original telescope unit is an actual integer pi-star equivalence

The full original MC diagram is mapped into the ONE original integer
diagonal functor. Genuine original compact group-colimit Isos identify
every pointwise comparison, through all original legs. Actual Group
Fubini therefore identifies the full outer descent as an Iso. The
proved original MC integer-pi transitions give the actual stage-zero
colimit Iso. Their composite has ENTIRE hom equal to the original
telescope-unit integer-pi map, in ALL integer degrees and on EVERY
original input. All original caller-B models, MC/R/stage/Arrow/units,
chosen cocones, diagonal degrees, map functions and naturalities remain.
Arbitrary Omega, pi0/all-point detection, native shifted FS0/FS1,
Omega-test recognition and both original K recognitions are later work.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerUnitGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
open GrpCat.FilteredColimits.Fubini GrpCat.FilteredColimits.PointwiseComparison
open GrpCat.FilteredColimits.ConstantSource
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The actual original MC-by-diagonal matrix retains both full original source diagrams. -/
def stablePiMatrix (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    ℕ ⥤ ℕ ⥤ GrpCat.{v} := diagram X ⋙ integerDiagonalDiagramFunctor q

/-- Every original input Arrow acts on the full SAME original MC-by-diagonal matrix. -/
def stablePiMatrixFunctor (q : ℤ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    (ℕ ⥤ ℕ ⥤ GrpCat.{v}) :=
  diagramFunctor ⋙ (Functor.whiskeringRight ℕ PointedCGWH.SequentialSpectrum.{u, v}
    (ℕ ⥤ GrpCat.{v})).obj (integerDiagonalDiagramFunctor q)

/-- Every actual original matrix row is the ONE diagonal of the original MC stage. -/
theorem stablePiMatrix_obj (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (i : ℕ) :
    (stablePiMatrix q X).obj i =
      (integerDiagonalDiagramFunctor q).obj ((stage i).functor.obj X) := rfl

/-- Every actual original matrix column is the SAME fixed-level positive group MC diagram. -/
theorem stablePiMatrix_flip_obj (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (stablePiMatrix q X).flip.obj n =
      levelDiagram X (integerTailLevel q + n) ⋙
        piNPositiveFunctor (integerTailPositiveIndex q + n) := rfl

/-- The full matrix cocone is the original whole diagonal functor applied to the MC cocone. -/
def stablePiMatrixCocone (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    Cocone (stablePiMatrix q X) :=
  (integerDiagonalDiagramFunctor q).mapCocone (colimit.cocone (diagram X))

/-- EVERY whole matrix cocone leg is the SAME original diagonal map of the original MC leg. -/
theorem stablePiMatrixCocone_leg (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (i : ℕ) :
    (stablePiMatrixCocone q X).ι.app i = (integerDiagonalDiagramFunctor q).map (leg X i) := rfl

/-- The original compact source gives BOTH genuine pointwise group comparison functions. -/
def stablePiMatrixComponentIso (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    GrpCat.FilteredColimits.colimit ((stablePiMatrix q X).flip.obj n) ≅
      (stablePiMatrixCocone q X).pt.obj n :=
  telescopeGroupHomotopyIso X (integerTailLevel q + n) (integerTailPositiveIndex q + n)

/-- ALL original compact legs identify the ENTIRE component-Iso hom with the actual UPL descent. -/
theorem stablePiMatrixComponentIso_hom (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (stablePiMatrixComponentIso q X n).hom =
      pointwiseDesc (stablePiMatrix q X) (stablePiMatrixCocone q X) n := by
  apply (GrpCat.FilteredColimits.colimitCoconeIsColimit
    ((stablePiMatrix q X).flip.obj n)).hom_ext
  intro i
  have hCompact := telescopeGroupHomotopyIso_hom_ι X
    (integerTailLevel q + n) (integerTailPositiveIndex q + n) i
  have hDesc := pointwiseDesc_fac (stablePiMatrix q X) (stablePiMatrixCocone q X) n i
  exact hCompact.trans hDesc.symm

/-- The WHOLE actual pointwise matrix Iso is derived from the original compact components. -/
def stablePiMatrixPointwiseIso (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (stablePiMatrix q X).flip ⋙ GrpCat.FilteredColimits.colimitFunctor ≅
      (stablePiMatrixCocone q X).pt :=
  NatIso.ofComponents (fun n => stablePiMatrixComponentIso q X n) (fun f => by
    rw [stablePiMatrixComponentIso_hom, stablePiMatrixComponentIso_hom]
    exact (pointwiseComparison (stablePiMatrix q X) (stablePiMatrixCocone q X)).naturality f)

/-- The ENTIRE pointwise matrix Iso hom equals the original full UPL comparison. -/
theorem stablePiMatrixPointwiseIso_hom (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (stablePiMatrixPointwiseIso q X).hom =
      pointwiseComparison (stablePiMatrix q X) (stablePiMatrixCocone q X) := by
  apply NatTrans.ext
  funext n
  exact stablePiMatrixComponentIso_hom q X n

/-- EVERY full inverse matrix component is the SAME actual original compact group inverse. -/
theorem stablePiMatrixPointwiseIso_inv_app (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (stablePiMatrixPointwiseIso q X).inv.app n =
      (telescopeGroupHomotopyIso X
        (integerTailLevel q + n) (integerTailPositiveIndex q + n)).inv := rfl

/-- BOTH original telescope integer-pi maps use the actual genuine Fubini construction. -/
def telescopeIntegerPiComparisonIso (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    GrpCat.FilteredColimits.colimit (diagram X ⋙ integerStablePiFunctor q) ≅
      (integerStablePiFunctor q).obj (telescope X) :=
  groupCoconeComparisonIso (stablePiMatrix q X) (stablePiMatrixCocone q X)
    (stablePiMatrixPointwiseIso q X)

/-- The ENTIRE original telescope comparison hom is the actual original outer Group UPL descent. -/
theorem telescopeIntegerPiComparisonIso_hom (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeIntegerPiComparisonIso q X).hom =
      groupCoconeComparisonDesc (stablePiMatrix q X) (stablePiMatrixCocone q X) :=
  groupCoconeComparisonIso_hom (stablePiMatrix q X) (stablePiMatrixCocone q X)
    (stablePiMatrixPointwiseIso q X) (stablePiMatrixPointwiseIso_hom q X)

/-- The ENTIRE original inverse retains the actual compact pointwise inverse and Fubini inverse. -/
theorem telescopeIntegerPiComparisonIso_inv (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeIntegerPiComparisonIso q X).inv =
      GrpCat.FilteredColimits.colimitMap ((stablePiMatrixPointwiseIso q X).inv) ≫
        (fubiniIso (stablePiMatrix q X)).inv := rfl

/-- EVERY original MC integer-pi leg is preserved by the ENTIRE telescope comparison map. -/
theorem telescopeIntegerPiComparisonIso_hom_leg (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (i : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone (diagram X ⋙ integerStablePiFunctor q)).ι.app i ≫
        (telescopeIntegerPiComparisonIso q X).hom = (integerStablePiFunctor q).map (leg X i) :=
  (congrArg (fun f =>
    (GrpCat.FilteredColimits.colimitCocone (diagram X ⋙ integerStablePiFunctor q)).ι.app i ≫ f)
      (telescopeIntegerPiComparisonIso_hom q X)).trans
        (groupCoconeComparisonDesc_fac (stablePiMatrix q X) (stablePiMatrixCocone q X) i)

/-- The whole original matrix input map retains the SAME actual original telescope-leg square. -/
theorem stablePiMatrix_map_cocone_leg (q : ℤ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) (i : ℕ) :
    ((stablePiMatrixFunctor q).map f).app i ≫ (stablePiMatrixCocone q Y).ι.app i =
      (stablePiMatrixCocone q X).ι.app i ≫
        (integerDiagonalDiagramFunctor q).map (telescopeFunctor.map f) := by
  let D := integerDiagonalDiagramFunctor.{u, v} q
  exact (D.map_comp _ _).symm.trans
    ((D.congr_map (leg_naturality f i).symm).trans (D.map_comp _ _))

/-- ALL original spectrum input maps preserve the ENTIRE forward telescope integer-pi comparison. -/
theorem telescopeIntegerPiComparisonIso_hom_naturality (q : ℤ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    GrpCat.FilteredColimits.colimitMap
        (Functor.whiskerRight (diagramMap f) (integerStablePiFunctor q)) ≫
          (telescopeIntegerPiComparisonIso q Y).hom =
      (telescopeIntegerPiComparisonIso q X).hom ≫
        (integerStablePiFunctor q).map (telescopeFunctor.map f) := by
  have h := groupCoconeComparisonDesc_map_square (stablePiMatrixCocone q X)
    (stablePiMatrixCocone q Y) ((stablePiMatrixFunctor q).map f)
    ((integerDiagonalDiagramFunctor q).map (telescopeFunctor.map f))
    (stablePiMatrix_map_cocone_leg q f)
  rw [telescopeIntegerPiComparisonIso_hom, telescopeIntegerPiComparisonIso_hom]
  exact h

/-- The actual original outer MC integer-pi colimit construction retains all input Arrow maps. -/
def stageIntegerPiColimitFunctor (q : ℤ) : PointedCGWH.SequentialSpectrum.{u, v} ⥤ GrpCat.{v} :=
  diagramFunctor ⋙ (Functor.whiskeringRight ℕ PointedCGWH.SequentialSpectrum.{u, v}
    GrpCat.{v}).obj (integerStablePiFunctor q) ⋙
      GrpCat.FilteredColimits.colimitFunctor

/-- The WHOLE actual native telescope comparison retains both original input functors. -/
def telescopeIntegerPiComparisonNatIso (q : ℤ) : stageIntegerPiColimitFunctor.{u, v} q ≅
    telescopeFunctor ⋙ integerStablePiFunctor q :=
  NatIso.ofComponents (fun X => telescopeIntegerPiComparisonIso q X)
    (fun f => telescopeIntegerPiComparisonIso_hom_naturality q f)

/-- ALL original spectrum input maps preserve the ENTIRE inverse telescope comparison. -/
theorem telescopeIntegerPiComparisonIso_inv_naturality (q : ℤ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (integerStablePiFunctor q).map (telescopeFunctor.map f) ≫
        (telescopeIntegerPiComparisonIso q Y).inv = (telescopeIntegerPiComparisonIso q X).inv ≫
      GrpCat.FilteredColimits.colimitMap
        (Functor.whiskerRight (diagramMap f) (integerStablePiFunctor q)) :=
  (telescopeIntegerPiComparisonNatIso q).inv.naturality f

/-- EVERY actual successive MC integer-pi diagram map is the original full transition map. -/
theorem stageIntegerPiDiagram_map_succ (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    (diagram X ⋙ integerStablePiFunctor q).map (homOfLE (Nat.le_succ n)) =
      (integerStablePiFunctor q).map ((transition n).app X) :=
  (integerStablePiFunctor q).congr_map (diagram_map_succ X n)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Every SAME original MC successor map is an integer-pi Iso in the original caller model. -/
theorem stageIntegerPiDiagram_succ_isIso (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    IsIso ((diagram X ⋙ integerStablePiFunctor q).map (homOfLE (Nat.le_succ n))) :=
  (stageIntegerPiDiagram_map_succ q X n).symm ▸ transitionIntegerStablePi_isIso q n X

/-- The original zero-to-stage maps are genuinely Isos from the proved original MC transitions. -/
theorem stageIntegerPiDiagram_zeroTo_isIso (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    IsIso ((diagram X ⋙ integerStablePiFunctor q).map (zeroTo n)) :=
  map_zeroTo_isIso (diagram X ⋙ integerStablePiFunctor q) (stageIntegerPiDiagram_succ_isIso q X) n

/-- BOTH actual original zero-stage comparison functions keep the SAME genuine MC Group quotient. -/
def stageZeroIntegerPiColimitIso (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor q).obj X ≅
      GrpCat.FilteredColimits.colimit (diagram X ⋙ integerStablePiFunctor q) :=
  constantSourceColimitIso (diagram X ⋙ integerStablePiFunctor q)
    (stageIntegerPiDiagram_zeroTo_isIso q X)

/-- The ENTIRE original zero-stage Iso hom is the SAME actual original MC stage-zero Group leg. -/
theorem stageZeroIntegerPiColimitIso_hom (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (stageZeroIntegerPiColimitIso q X).hom =
      (GrpCat.FilteredColimits.colimitCocone (diagram X ⋙ integerStablePiFunctor q)).ι.app 0 :=
  constantSourceColimitIso_hom (diagram X ⋙ integerStablePiFunctor q)
    (stageIntegerPiDiagram_zeroTo_isIso q X)

/-- Both full actual original telescope-unit integer-pi Iso maps use only proved original Isos. -/
def telescopeUnitIntegerPiIso (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor q).obj X ≅ (integerStablePiFunctor q).obj (telescope X) :=
  stageZeroIntegerPiColimitIso q X ≪≫ telescopeIntegerPiComparisonIso q X

/-- The ENTIRE original telescope-unit Iso hom is the actual original telescope-unit pi map. -/
theorem telescopeUnitIntegerPiIso_hom (q : ℤ)
    (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (telescopeUnitIntegerPiIso q X).hom = (integerStablePiFunctor q).map
      (PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app X) :=
  (congrArg (fun f => f ≫ (telescopeIntegerPiComparisonIso q X).hom)
    (stageZeroIntegerPiColimitIso_hom q X)).trans
      (telescopeIntegerPiComparisonIso_hom_leg q X 0)

/-- The WHOLE original telescope-unit integer-pi NatIso retains every original input Arrow. -/
def telescopeUnitIntegerPiNatIso (q : ℤ) : integerStablePiFunctor.{u, v} q ≅
    telescopeFunctor ⋙ integerStablePiFunctor q :=
  NatIso.ofComponents (fun X => telescopeUnitIntegerPiIso q X) (fun f => by
    rw [telescopeUnitIntegerPiIso_hom, telescopeUnitIntegerPiIso_hom]
    exact (Functor.whiskerRight PointedCGWH.SequentialSpectrum.MappingTelescope.unit
      (integerStablePiFunctor q)).naturality f)

/-- The ENTIRE native unit NatIso hom equals the SAME original actual unit map family. -/
theorem telescopeUnitIntegerPiNatIso_hom (q : ℤ) :
    (telescopeUnitIntegerPiNatIso.{u, v} q).hom =
      Functor.whiskerRight PointedCGWH.SequentialSpectrum.MappingTelescope.unit
        (integerStablePiFunctor q) := by
  apply NatTrans.ext
  funext X
  exact telescopeUnitIntegerPiIso_hom q X

/-- In EVERY original integer degree the SAME actual original telescope-unit map induces an Iso. -/
theorem telescopeUnit_integerPi_isIso (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    IsIso ((integerStablePiFunctor q).map
      (PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app X)) :=
  (telescopeUnitIntegerPiIso_hom q X) ▸ (telescopeUnitIntegerPiIso q X).isIso_hom

/-- The SAME original telescope unit is a genuine pi-star equivalence on EVERY original input. -/
theorem telescopeUnit_integerPiStarEquivalence (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    integerPiStarEquivalences (PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app X) :=
  (integerPiStarEquivalences_iff _).mpr (fun q => telescopeUnit_integerPi_isIso q X)

end PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerUnitGeometry
