/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.OmegaLevelWeak
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.StageIntegerStablePi
import MathlibExt.Algebra.Category.Grp.FilteredColimits.ConstantSource

/-!
# Original integer-diagonal recognition on actual Omega inputs

The original positive structure and each original diagonal successor are
Isos on Omega spectra. Every actual quotient leg is then an Iso, and its
full naturality identifies the positive next-level map with the original
integer-pi map at the original cofinal offset. This proves integer pi-star
if and only if native level weakness between original Omega spectra.
The arbitrary-input telescope statements are retained separately; no
unqualified claim that T itself is Omega is used.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerOmegaRecognitionGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.OmegaLevelWeakGeometry
open PointedCGWH.NativeLoopWeakDetectionGeometry
open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.HomotopyStructureGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.GroupUnitCoherenceGeometry
open GrpCat.FilteredColimits.ConstantSource
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- Actual original Omega adjoints give Isos of the SAME complete positive structure maps. -/
theorem omegaGroupStructure_isIso (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : X.IsOmega) (m k : ℕ) : IsIso ((groupStructureNatTrans m k).app X) := by
  let q := PointedCGWH.SequentialSpectrum.adjointStructureMap X m
  have hq : IsIso ((piNPositiveFunctor k).map q) :=
    (positiveGroupMap_isIso_iff_bijective k q).mpr
      (weakMap_selectedPositivePi_bijective q (hX m) k)
  have hs : IsIso ((nativeLoopGroupShiftNatIso k).hom.app (X.level (m + 1))) :=
    ((nativeLoopGroupShiftNatIso k).app (X.level (m + 1))).isIso_hom
  exact (MorphismProperty.isomorphisms GrpCat.{v}).comp_mem
    ((piNPositiveFunctor k).map q)
    ((nativeLoopGroupShiftNatIso k).hom.app (X.level (m + 1))) hq hs

/-- Every SAME original Omega diagonal successor is its ACTUAL group structure and index Iso. -/
theorem omegaDiagonalTransition_isIso (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : X.IsOmega) (m k n : ℕ) : IsIso ((diagonalTransition n m k).app X) := by
  have hs : IsIso ((groupStructureNatTrans (m + n) (k + n)).app X) :=
    omegaGroupStructure_isIso X hX (m + n) (k + n)
  have hi : IsIso ((groupUnitIndexNatIso n m k).hom.app X) :=
    ((groupUnitIndexNatIso n m k).app X).isIso_hom
  exact (diagonalTransition_app n m k X).symm ▸
    (MorphismProperty.isomorphisms GrpCat.{v}).comp_mem _ _ hs hi

/-- Every SAME original Omega finite successor diagonal map is ACTUALLY an Iso. -/
theorem omegaDiagonalMap_succ_isIso (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : X.IsOmega) (m k n : ℕ) :
    IsIso ((diagonalDiagram X m k).map (homOfLE (Nat.le_succ n))) :=
  (diagonalDiagram_map_succ X m k n).symm ▸ omegaDiagonalTransition_isIso X hX m k n

/-- All SAME original Omega zero-to-stage maps are Isos from their actual original transitions. -/
theorem omegaDiagonalMap_zeroTo_isIso (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : X.IsOmega) (m k n : ℕ) : IsIso ((diagonalDiagram X m k).map (zeroTo n)) :=
  map_zeroTo_isIso (diagonalDiagram X m k) (omegaDiagonalMap_succ_isIso X hX m k) n

/-- The genuine SAME original quotient UPL makes EVERY actual Group quotient leg an Iso. -/
theorem originalGroupQuotientLeg_isIso (D : ℕ ⥤ GrpCat.{v})
    (h : ∀ n, IsIso (D.map (zeroTo n))) (n : ℕ) :
    IsIso ((GrpCat.FilteredColimits.colimitCocone D).ι.app n) := by
  let P := MorphismProperty.isomorphisms GrpCat.{v}
  have h0 : IsIso ((GrpCat.FilteredColimits.colimitCocone D).ι.app 0) :=
    constantSource_zero_leg_isIso D h
  have he : IsIso (D.map (zeroTo n) ≫
      (GrpCat.FilteredColimits.colimitCocone D).ι.app n) :=
    ((GrpCat.FilteredColimits.colimitCocone D).w (zeroTo n)).symm ▸ h0
  exact P.of_precomp (W' := P) _ _ (h n) he

/-- Every SAME original integer-pi leg of an ACTUAL Omega spectrum is an Iso. -/
theorem omegaIntegerStablePiLeg_isIso (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : X.IsOmega) (n : ℕ) : IsIso (integerStablePiLeg q X n) :=
  originalGroupQuotientLeg_isIso ((integerDiagonalDiagramFunctor q).obj X)
    (omegaDiagonalMap_zeroTo_isIso X hX (integerTailLevel q) (integerTailPositiveIndex q)) n

/-- The ACTUAL original integer degree for a positive next-level test retains both indices. -/
def recognitionDegree (m k : ℕ) : ℤ := (k : ℤ) - (m : ℤ)

/-- The ACTUAL original cofinal-stage offset uses the SAME original positive-tail level. -/
def recognitionOffset (m k : ℕ) : ℕ := (m + 1) - integerTailLevel (recognitionDegree m k)

/-- EVERY actual next-level test is the SAME original integer-diagonal level at its true offset. -/
theorem recognitionOffset_level (m k : ℕ) :
    integerTailLevel (recognitionDegree m k) + recognitionOffset m k = m + 1 := by
  simp only [recognitionDegree, recognitionOffset, integerTailLevel]
  omega

/-- EVERY actual positive test degree is the SAME original integer-diagonal group degree. -/
theorem recognitionOffset_positive (m k : ℕ) :
    integerTailPositiveIndex (recognitionDegree m k) + recognitionOffset m k = k := by
  simp only [recognitionDegree, recognitionOffset, integerTailLevel, integerTailPositiveIndex]
  omega

/-- Both original Omega quotient-leg Isos reflect the SAME entire original integer input map. -/
theorem omegaIntegerMap_isIso_reflects_positiveLeg (q : ℤ)
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hX : X.IsOmega) (hY : Y.IsOmega) (n : ℕ)
    (hπ : IsIso ((integerStablePiFunctor q).map f)) :
    IsIso ((piNPositiveFunctor (integerTailPositiveIndex q + n)).map
      (PointedCGWH.SequentialSpectrum.levelMap f (integerTailLevel q + n))) := by
  let P := MorphismProperty.isomorphisms GrpCat.{v}
  let a := integerStablePiLeg q X n
  let b := integerStablePiLeg q Y n
  let p := (integerStablePiFunctor q).map f
  let g := (piNPositiveFunctor (integerTailPositiveIndex q + n)).map
    (PointedCGWH.SequentialSpectrum.levelMap f (integerTailLevel q + n))
  have ha : IsIso a := omegaIntegerStablePiLeg_isIso q X hX n
  have hb : IsIso b := omegaIntegerStablePiLeg_isIso q Y hY n
  have h : a ≫ p = g ≫ b := integerStablePiLeg_naturality q f n
  exact P.of_postcomp (W' := P) g b hb (h ▸ P.comp_mem a p ha hπ)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- BOTH original Omega hypotheses give actual pi-star iff the SAME caller-B native level class. -/
theorem omegaMap_integerPiStar_iff_modelWeak
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hX : X.IsOmega) (hY : Y.IsOmega) :
    integerPiStarEquivalences f ↔ weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f := by
  constructor
  · intro h
    apply (omegaMap_modelWeak_iff_positiveGroup_isIso f hX hY).mpr
    intro m k
    have he := omegaIntegerMap_isIso_reflects_positiveLeg (recognitionDegree m k) f hX hY
      (recognitionOffset m k) ((integerPiStarEquivalences_iff f).mp h (recognitionDegree m k))
    rw [recognitionOffset_level, recognitionOffset_positive] at he
    exact he
  · exact levelWeak_le_integerPiStarEquivalences f

end PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerOmegaRecognitionGeometry
