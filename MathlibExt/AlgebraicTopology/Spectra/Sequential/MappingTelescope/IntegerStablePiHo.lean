/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.RTReflection

/-!
# The original integer stable homotopy functors on the level homotopy category

The genuine original positive-group and diagonal isomorphisms show that
each original integer stable homotopy functor inverts every original level
equivalence. The actual localization construction retains all original
objects, quotient maps and inverses. Both original R-after-T units and
the native Q/K units give natural group isomorphisms on all level homotopy
objects and all their morphisms.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.NativeKRTComparisonGeometry
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev H := toHomotopyCategory Carrier.{u, v}
private abbrev Ho := HomotopyCategory Carrier.{u, v}
private abbrev family : NativeStabilizationFamily.{u, v}
    (CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne.{u, v}) ℕ :=
  PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}

/-- The original full diagonal and genuine group colimit invert every original level equivalence. -/
theorem integerStablePiFunctor_invertsLevelWeak (q : ℤ) :
    (weakEquivalences Carrier.{u, v}).IsInvertedBy (integerStablePiFunctor q) :=
  fun _ _ f hf => integerStablePiLevelWeak_isIso q f hf

/-- The actual path and quotient construction descends the same entire original integer functor. -/
def integerStablePiHoFunctor (q : ℤ) : Ho.{u, v} ⥤ GrpCat.{v} :=
  Localization.Construction.lift (integerStablePiFunctor q)
    (integerStablePiFunctor_invertsLevelWeak q)

/-- Every projected original object retains precisely its original integer group and operations. -/
theorem integerStablePiHoFunctor_obj (q : ℤ) (X : Carrier.{u, v}) :
    (integerStablePiHoFunctor q).obj (H.obj X) = (integerStablePiFunctor q).obj X := rfl

/-- Every projected source map retains its entire original diagonal quotient-map function. -/
theorem integerStablePiHoFunctor_map (q : ℤ) {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (integerStablePiHoFunctor q).map (H.map f) = (integerStablePiFunctor q).map f := by
  have h := Functor.congr_hom
    (Localization.Construction.fac (integerStablePiFunctor q)
      (integerStablePiFunctor_invertsLevelWeak q)) f
  change (integerStablePiHoFunctor q).map (H.map f) =
    (𝟙 ((integerStablePiFunctor q).obj X)) ≫ (integerStablePiFunctor q).map f ≫
      (𝟙 ((integerStablePiFunctor q).obj Y)) at h
  simpa only [Category.id_comp, Category.comp_id] using h

/-- The whole projected source functor equals the original integer functor, including all maps. -/
theorem integerStablePiHoFunctor_original (q : ℤ) :
    H ⋙ integerStablePiHoFunctor.{u, v} q = integerStablePiFunctor q :=
  Localization.Construction.fac (integerStablePiFunctor q)
    (integerStablePiFunctor_invertsLevelWeak q)

/-- Every localized original source map is the same complete filtered group-colimit map. -/
theorem integerStablePiHoFunctor_map_originalColimit
    (q : ℤ) {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (integerStablePiHoFunctor q).map (H.map f) =
      GrpCat.FilteredColimits.colimitMap
        ((DiagonalHomotopyGeometry.integerDiagonalDiagramFunctor q).map f) :=
  (integerStablePiHoFunctor_map q f).trans (integerStablePiFunctor_map q f)

/-- Original quotient representatives retain their pointed levels and positive degrees. -/
theorem integerStablePiHoFunctor_map_apply (q : ℤ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) (n : ℕ)
    (a : PointedCGWH.piN (DiagonalHomotopyGeometry.integerTailPositiveIndex q + n + 1)
      (X.level (DiagonalHomotopyGeometry.integerTailLevel q + n))) :
    ((integerStablePiHoFunctor q).map (H.map f)).hom
      (GrpCat.FilteredColimits.G.mk
        ((DiagonalHomotopyGeometry.integerDiagonalDiagramFunctor q).obj X) ⟨n, a⟩) =
      GrpCat.FilteredColimits.G.mk
        ((DiagonalHomotopyGeometry.integerDiagonalDiagramFunctor q).obj Y)
          ⟨n, PointedCGWH.piNMap (DiagonalHomotopyGeometry.integerTailPositiveIndex q + n + 1)
            (PointedCGWH.SequentialSpectrum.levelMap f
              (DiagonalHomotopyGeometry.integerTailLevel q + n)) a⟩ := by
  rw [integerStablePiHoFunctor_map]
  exact integerStablePiFunctor_map_apply q f n a

/-- The full weak-arrow isomorphism is sent to its original diagonal-colimit isomorphism. -/
theorem integerStablePiHoFunctor_map_wIso (q : ℤ) {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences Carrier.{u, v} f) :
    (integerStablePiHoFunctor q).mapIso (Localization.Construction.wIso f hf) =
      integerStablePiLevelWeakIso q f hf := by
  apply Iso.ext
  exact (integerStablePiHoFunctor_map q f).trans
    (integerStablePiLevelWeakIso_hom q f hf).symm

/-- Every formal weak-arrow inverse retains the full original positive-group and colimit inverse. -/
theorem integerStablePiHoFunctor_map_wIso_inv (q : ℤ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) (hf : weakEquivalences Carrier.{u, v} f) :
    (integerStablePiHoFunctor q).map (Localization.Construction.wIso f hf).inv =
      (integerStablePiLevelWeakIso q f hf).inv :=
  congrArg (fun e => e.inv) (integerStablePiHoFunctor_map_wIso q f hf)

/-- The original R-after-T unit is invertible on every integer group of every level-Ho object. -/
theorem reflectionIntegerPiHoUnit_isIso (q : ℤ) (X : Ho.{u, v}) :
    IsIso ((integerStablePiHoFunctor q).map (reflectionHoUnit.app X)) := by
  rcases X with ⟨⟨X⟩⟩
  change IsIso ((integerStablePiHoFunctor q).map (reflectionHoUnit.app (H.obj X)))
  have h : (integerStablePiHoFunctor q).map (reflectionHoUnit.app (H.obj X)) =
      (reflectionUnitIntegerPiIso q X).hom :=
    ((integerStablePiHoFunctor q).congr_map (reflectionHoUnit_app X)).trans
      ((integerStablePiHoFunctor_map q (reflectionUnit.app X)).trans
        (reflectionUnitIntegerPiIso_hom q X).symm)
  exact h.symm ▸ (reflectionUnitIntegerPiIso q X).isIso_hom

/-- Both full functions of the original integer unit are retained on every level-Ho object. -/
def reflectionIntegerPiHoUnitIso (q : ℤ) (X : Ho.{u, v}) :
    (integerStablePiHoFunctor q).obj X ≅
      (integerStablePiHoFunctor q).obj (reflectionHoFunctor.obj X) := by
  let _ := reflectionIntegerPiHoUnit_isIso q X
  exact asIso ((integerStablePiHoFunctor q).map (reflectionHoUnit.app X))

/-- The entire descended unit isomorphism is the image of the original two-map unit. -/
theorem reflectionIntegerPiHoUnitIso_hom (q : ℤ) (X : Ho.{u, v}) :
    (reflectionIntegerPiHoUnitIso q X).hom =
      (integerStablePiHoFunctor q).map (reflectionHoUnit.app X) := rfl

/-- Every original input retains both complete original telescope and R comparison functions. -/
theorem reflectionIntegerPiHoUnitIso_original (q : ℤ) (X : Carrier.{u, v}) :
    reflectionIntegerPiHoUnitIso q (H.obj X) = reflectionUnitIntegerPiIso q X := by
  apply Iso.ext
  rw [reflectionIntegerPiHoUnitIso_hom]
  exact ((integerStablePiHoFunctor q).congr_map (reflectionHoUnit_app X)).trans
    ((integerStablePiHoFunctor_map q (reflectionUnit.app X)).trans
      (reflectionUnitIntegerPiIso_hom q X).symm)

/-- Each inverse is the original R inverse followed by the original telescope inverse. -/
theorem reflectionIntegerPiHoUnitIso_original_inv (q : ℤ) (X : Carrier.{u, v}) :
    (reflectionIntegerPiHoUnitIso q (H.obj X)).inv =
      (IntegerStablePiGeometry.integerStablePiRUnitIso q (telescope X)).inv ≫
        (IntegerUnitGeometry.telescopeUnitIntegerPiIso q X).inv :=
  (congrArg (fun e => e.inv) (reflectionIntegerPiHoUnitIso_original q X)).trans
    (reflectionUnitIntegerPiIso_inv q X)

/-- The complete R-after-T unit is a natural isomorphism on all ordinary level-Ho arrows. -/
def reflectionIntegerPiHoNatIso (q : ℤ) : integerStablePiHoFunctor.{u, v} q ≅
    reflectionHoFunctor ⋙ integerStablePiHoFunctor q :=
  NatIso.ofComponents (fun X => reflectionIntegerPiHoUnitIso q X)
    (fun f => by
      rw [reflectionIntegerPiHoUnitIso_hom, reflectionIntegerPiHoUnitIso_hom]
      exact (Functor.whiskerRight reflectionHoUnit (integerStablePiHoFunctor q)).naturality f)

/-- The whole forward natural transformation is precisely the original descended unit image. -/
theorem reflectionIntegerPiHoNatIso_hom (q : ℤ) :
    (reflectionIntegerPiHoNatIso.{u, v} q).hom =
      Functor.whiskerRight reflectionHoUnit (integerStablePiHoFunctor q) := by
  apply NatTrans.ext
  funext X
  exact reflectionIntegerPiHoUnitIso_hom q X

/-- Every ordinary level-Ho arrow retains the entire original R-after-T integer square. -/
theorem reflectionIntegerPiHoNatIso_naturality (q : ℤ) {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (integerStablePiHoFunctor q).map f ≫ (reflectionIntegerPiHoNatIso q).hom.app Y =
      (reflectionIntegerPiHoNatIso q).hom.app X ≫
        (integerStablePiHoFunctor q).map (reflectionHoFunctor.map f) :=
  (reflectionIntegerPiHoNatIso q).hom.naturality f

/-- Every ordinary level-Ho arrow retains the full inverse R-after-T integer square. -/
theorem reflectionIntegerPiHoNatIso_inverse_naturality (q : ℤ)
    {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (integerStablePiHoFunctor q).map (reflectionHoFunctor.map f) ≫
      (reflectionIntegerPiHoNatIso q).inv.app Y =
      (reflectionIntegerPiHoNatIso q).inv.app X ≫ (integerStablePiHoFunctor q).map f :=
  (reflectionIntegerPiHoNatIso q).inv.naturality f

/-- Both original native Q/K and R-after-T comparison functions are retained in every degree. -/
def nativeQKIntegerPiHoNatIso (q : ℤ) : integerStablePiHoFunctor.{u, v} q ≅
    NativeK.localReplacementHo family ⋙ integerStablePiHoFunctor q :=
  reflectionIntegerPiHoNatIso q ≪≫
    (Functor.isoWhiskerRight nativeQKRTHoIso (integerStablePiHoFunctor q)).symm

/-- The complete native integer comparison uses the original RT unit and inverse Q/K-to-RT map. -/
theorem nativeQKIntegerPiHoNatIso_hom_app (q : ℤ) (X : Ho.{u, v}) :
    (nativeQKIntegerPiHoNatIso q).hom.app X =
      (integerStablePiHoFunctor q).map (reflectionHoUnit.app X) ≫
        (integerStablePiHoFunctor q).map (nativeQKRTHoIso.inv.app X) := rfl

/-- The whole native integer comparison hom is the actual original Q-inverse/K-unit image. -/
theorem nativeQKIntegerPiHoNatIso_originalUnit (q : ℤ) (X : Ho.{u, v}) :
    (nativeQKIntegerPiHoNatIso q).hom.app X =
      (integerStablePiHoFunctor q).map ((NativeK.localReplacementHoUnit family).app X) := by
  rw [nativeQKIntegerPiHoNatIso_hom_app, ← Functor.map_comp]
  apply (integerStablePiHoFunctor q).congr_map
  apply (cancel_mono (nativeQKRTHoIso.hom.app X)).mp
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact (congr_app nativeQKRTHoIso_wholeUnit X).symm

/-- Every native unit gives a genuine integer group isomorphism on every level-Ho object. -/
theorem nativeQKIntegerPiHoUnit_isIso (q : ℤ) (X : Ho.{u, v}) :
    IsIso ((integerStablePiHoFunctor q).map ((NativeK.localReplacementHoUnit family).app X)) := by
  rw [← nativeQKIntegerPiHoNatIso_originalUnit]
  exact ((nativeQKIntegerPiHoNatIso q).app X).isIso_hom

/-- Every level-Ho source arrow retains the complete native Q/K integer naturality square. -/
theorem nativeQKIntegerPiHoNatIso_naturality (q : ℤ) {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (integerStablePiHoFunctor q).map f ≫ (nativeQKIntegerPiHoNatIso q).hom.app Y =
      (nativeQKIntegerPiHoNatIso q).hom.app X ≫
        (integerStablePiHoFunctor q).map ((NativeK.localReplacementHo family).map f) :=
  (nativeQKIntegerPiHoNatIso q).hom.naturality f

/-- Every level-Ho source arrow retains the full inverse original native Q/K integer square. -/
theorem nativeQKIntegerPiHoNatIso_inverse_naturality (q : ℤ)
    {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (integerStablePiHoFunctor q).map ((NativeK.localReplacementHo family).map f) ≫
      (nativeQKIntegerPiHoNatIso q).inv.app Y =
      (nativeQKIntegerPiHoNatIso q).inv.app X ≫ (integerStablePiHoFunctor q).map f :=
  (nativeQKIntegerPiHoNatIso q).inv.naturality f

/-- The original integer testing class on level-Ho uses all original descended degree functors. -/
def integerPiHoEquivalences : MorphismProperty Ho.{u, v} :=
  ⨅ q : ℤ, (MorphismProperty.isomorphisms GrpCat.{v}).inverseImage (integerStablePiHoFunctor q)

/-- Every degree and every whole level-Ho input map appears in the original integer tests. -/
theorem integerPiHoEquivalences_iff {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    integerPiHoEquivalences f ↔ ∀ q : ℤ, IsIso ((integerStablePiHoFunctor q).map f) :=
  MorphismProperty.iInf_iff _ f

/-- On each original projected source arrow these are exactly the original integer testing maps. -/
theorem integerPiHoEquivalences_projected {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    integerPiHoEquivalences (H.map f) ↔ integerPiStarEquivalences f := by
  rw [integerPiHoEquivalences_iff, integerPiStarEquivalences_iff]
  exact forall_congr' (fun q => by
    rw [integerStablePiHoFunctor_map]
    rfl)

/-- The whole original R-after-T unit belongs to every degree test on every level-Ho object. -/
theorem reflectionHoUnit_integerPiHo (X : Ho.{u, v}) :
    integerPiHoEquivalences (reflectionHoUnit.app X) :=
  (integerPiHoEquivalences_iff _).mpr (fun q => reflectionIntegerPiHoUnit_isIso q X)

/-- The whole original native Q-inverse/K-unit belongs to every integer test on every object. -/
theorem nativeQKHoUnit_integerPiHo (X : Ho.{u, v}) :
    integerPiHoEquivalences ((NativeK.localReplacementHoUnit family).app X) :=
  (integerPiHoEquivalences_iff _).mpr (fun q => nativeQKIntegerPiHoUnit_isIso q X)

/-- The original all-degree testing class is unchanged by the actual RT map on every Ho arrow. -/
theorem integerPiHoEquivalences_iff_reflectionMap {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    integerPiHoEquivalences f ↔ integerPiHoEquivalences (reflectionHoFunctor.map f) := by
  rw [integerPiHoEquivalences_iff, integerPiHoEquivalences_iff]
  exact forall_congr' (fun q => NatIso.isIso_map_iff (reflectionIntegerPiHoNatIso q) f)

/-- All original integer tests are unchanged by the actual native Q/K map on every arrow. -/
theorem integerPiHoEquivalences_iff_nativeQKMap {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    integerPiHoEquivalences f ↔
      integerPiHoEquivalences ((NativeK.localReplacementHo family).map f) := by
  rw [integerPiHoEquivalences_iff, integerPiHoEquivalences_iff]
  exact forall_congr' (fun q => NatIso.isIso_map_iff (nativeQKIntegerPiHoNatIso q) f)

end PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry
