/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionDiagonalColimit

/-!
# Original integer stable homotopy under actual scalar suspension

The forward map is induced by the complete original scalar adjunction unit,
followed by the original scalar-loop integer degree comparison. Its source
and target are the original integer-diagonal filtered group quotients. All
maps and equations are on arbitrary original native sequential spectra.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionDiagonalGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStageGeometry

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The full original integer suspension map is realized by the actual scalar adjunction unit. -/
def integerSuspensionPiMap (q : ℤ) : integerStablePiFunctor.{u, v} q ⟶
    SuspensionGeometry.suspension ⋙ integerStablePiFunctor (q + 1) :=
  SuspensionGeometry.integerUnitMap q ≫
    (Functor.associator SuspensionGeometry.suspension SuspensionGeometry.loop
      (integerStablePiFunctor q)).hom ≫
        Functor.whiskerLeft SuspensionGeometry.suspension (scalarLoopIntegerPiNatIso q).hom

/-- Its whole forward component retains both original unit and native loop-degree maps. -/
theorem integerSuspensionPiMap_app (q : ℤ) (X : SequentialSpectrum.{u, v}) :
    (integerSuspensionPiMap q).app X =
      (integerStablePiFunctor q).map (SuspensionGeometry.unit.app X) ≫
        (scalarLoopIntegerPiNatIso q).hom.app (SuspensionGeometry.suspension.obj X) := by
  change (integerStablePiFunctor q).map (SuspensionGeometry.unit.app X) ≫ 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- Every original spectrum map retains the entire forward integer suspension naturality square. -/
theorem integerSuspensionPiMap_naturality (q : ℤ) {X Y : SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (integerStablePiFunctor q).map f ≫ (integerSuspensionPiMap q).app Y =
      (integerSuspensionPiMap q).app X ≫
        (SuspensionGeometry.suspension ⋙ integerStablePiFunctor (q + 1)).map f :=
  (integerSuspensionPiMap q).naturality f

/-- Every whole suspension function acts on the same original scalar-unit quotient class. -/
theorem integerSuspensionPiMap_apply (q : ℤ) (X : SequentialSpectrum.{u, v})
    (a : (integerStablePiFunctor q).obj X) :
    ((integerSuspensionPiMap q).app X).hom a =
      ((scalarLoopIntegerPiNatIso q).hom.app (SuspensionGeometry.suspension.obj X)).hom
        (((integerStablePiFunctor q).map (SuspensionGeometry.unit.app X)).hom a) := by
  rw [integerSuspensionPiMap_app]
  rfl

/-- The actual shifted diagonal normalization retains all original integer and cofinal maps. -/
def suspensionNormalizationNatIso (q : ℤ) :
    diagonalColimitFunctor.{u, v} (integerTailLevel q) (integerTailPositiveIndex q + 1) ≅
      integerStablePiFunctor (q + 1) :=
  integerColimitNatIso (integerTailLevel q) (integerTailPositiveIndex q + 1) ≪≫
    eqToIso (congrArg integerStablePiFunctor (scalarLoop_integerDegree q))

/-- The full actual scalar suspension isomorphism uses both original interleaving quotient maps. -/
def integerSuspensionPiNatIso (q : ℤ) : integerStablePiFunctor.{u, v} q ≅
    SuspensionGeometry.suspension ⋙ integerStablePiFunctor (q + 1) :=
  suspensionColimitNatIso (integerTailLevel q) (integerTailPositiveIndex q) ≪≫
    Functor.isoWhiskerLeft SuspensionGeometry.suspension (suspensionNormalizationNatIso q)

private theorem scalarLoopIntegerPiNatIso_hom_normalized (q : ℤ) (X : SequentialSpectrum.{u, v}) :
    (scalarLoopIntegerPiNatIso q).hom.app X =
      (scalarLoopColimitNatIso (integerTailLevel q) (integerTailPositiveIndex q)).hom.app X ≫
        (suspensionNormalizationNatIso q).hom.app X := by
  change (_ ≫ _) ≫ _ = _ ≫ (_ ≫ _)
  exact Category.assoc _ _ _

/-- The whole suspension isomorphism is realized by the original scalar adjunction unit map. -/
theorem integerSuspensionPiNatIso_hom_app (q : ℤ) (X : SequentialSpectrum.{u, v}) :
    (integerSuspensionPiNatIso q).hom.app X = (integerSuspensionPiMap q).app X := by
  change (suspensionColimitNatIso (integerTailLevel q) (integerTailPositiveIndex q)).hom.app X ≫
      (suspensionNormalizationNatIso q).hom.app (SuspensionGeometry.suspension.obj X) = _
  rw [suspensionColimitNatIso_hom_app, integerSuspensionPiMap_app,
    scalarLoopIntegerPiNatIso_hom_normalized]
  exact Category.assoc _ _ _

/-- The complete forward natural transformation is the same actual scalar-unit-induced family. -/
theorem integerSuspensionPiNatIso_hom (q : ℤ) :
    (integerSuspensionPiNatIso.{u, v} q).hom = integerSuspensionPiMap q := by
  apply NatTrans.ext
  funext X
  exact integerSuspensionPiNatIso_hom_app q X

/-- Every full inverse component keeps original normalization followed by the
structure-map inverse. -/
theorem integerSuspensionPiNatIso_inv_app (q : ℤ) (X : SequentialSpectrum.{u, v}) :
    (integerSuspensionPiNatIso q).inv.app X =
      (suspensionNormalizationNatIso q).inv.app (SuspensionGeometry.suspension.obj X) ≫
        (suspensionColimitNatIso (integerTailLevel q) (integerTailPositiveIndex q)).inv.app X := rfl

/-- Each original forward integer leg retains the signed stage map and whole
cofinal normalization. -/
theorem integerSuspensionPiMap_leg (q : ℤ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    integerStablePiLeg q X n ≫ (integerSuspensionPiMap q).app X =
      (stageForward n (integerTailLevel q) (integerTailPositiveIndex q)).app X ≫
        diagonalLeg (integerTailLevel q) (integerTailPositiveIndex q + 1)
          (SuspensionGeometry.suspension.obj X) n ≫
            (suspensionNormalizationNatIso q).hom.app (SuspensionGeometry.suspension.obj X) := by
  rw [← integerSuspensionPiNatIso_hom_app]
  change diagonalLeg (integerTailLevel q) (integerTailPositiveIndex q) X n ≫
      ((suspensionColimitNatIso (integerTailLevel q) (integerTailPositiveIndex q)).hom.app X ≫
        (suspensionNormalizationNatIso q).hom.app (SuspensionGeometry.suspension.obj X)) = _
  rw [← Category.assoc, suspensionColimitNatIso_hom_leg, Category.assoc]

/-- Every original shifted stage leg is inverted through its actual signed
next-stage structure map. -/
theorem integerSuspensionPiNatIso_inv_shifted_leg (q : ℤ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    diagonalLeg (integerTailLevel q) (integerTailPositiveIndex q + 1)
        (SuspensionGeometry.suspension.obj X) n ≫
      (suspensionNormalizationNatIso q).hom.app (SuspensionGeometry.suspension.obj X) ≫
        (integerSuspensionPiNatIso q).inv.app X =
      (stageBackward n (integerTailLevel q) (integerTailPositiveIndex q)).app X ≫
        integerStablePiLeg q X (n + 1) := by
  rw [integerSuspensionPiNatIso_inv_app]
  rw [← Category.assoc
    ((suspensionNormalizationNatIso q).hom.app (SuspensionGeometry.suspension.obj X))
    ((suspensionNormalizationNatIso q).inv.app (SuspensionGeometry.suspension.obj X)),
    Iso.hom_inv_id_app, Category.id_comp]
  exact suspensionColimitNatIso_inv_leg (integerTailLevel q) (integerTailPositiveIndex q) X n

private theorem integerDegreeIso_inv_leg (p q : ℤ) (h : p = q)
    (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    integerStablePiLeg q X n ≫ (eqToIso (congrArg integerStablePiFunctor h)).inv.app X =
      ((eqToIso (congrArg integerDiagonalDiagramFunctor h)).inv.app X).app n ≫
        integerStablePiLeg p X n := by
  cases h
  simp only [eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.comp_id, Category.id_comp]

/-- Every inverse canonical integer leg retains the actual degree, cofinal
structure and stage maps. -/
theorem integerSuspensionPiNatIso_inv_leg (q : ℤ) (X : SequentialSpectrum.{u, v}) (n : ℕ) :
    integerStablePiLeg (q + 1) (SuspensionGeometry.suspension.obj X) n ≫
        (suspensionNormalizationNatIso q).inv.app (SuspensionGeometry.suspension.obj X) ≫
          (suspensionDiagonalIso (integerTailLevel q) (integerTailPositiveIndex q) X).inv =
      ((eqToIso (congrArg integerDiagonalDiagramFunctor (scalarLoop_integerDegree q))).inv.app
          (SuspensionGeometry.suspension.obj X)).app n ≫
      ((offsetDiagramNatTrans
          (integerTailLevel (integerDegree (integerTailLevel q) (integerTailPositiveIndex q + 1)))
          (integerTailPositiveIndex
            (integerDegree (integerTailLevel q) (integerTailPositiveIndex q + 1)))
          (normalizationOffset (integerTailLevel q) (integerTailPositiveIndex q + 1))).app
          (SuspensionGeometry.suspension.obj X)).app n ≫
      ((normalizationDiagramIso (integerTailLevel q) (integerTailPositiveIndex q + 1)).inv.app
          (SuspensionGeometry.suspension.obj X)).app n ≫
        (stageBackward n (integerTailLevel q) (integerTailPositiveIndex q)).app X ≫
          integerStablePiLeg q X (n + 1) := by
  change integerStablePiLeg (q + 1) (SuspensionGeometry.suspension.obj X) n ≫
      ((eqToIso (congrArg integerStablePiFunctor (scalarLoop_integerDegree q))).inv.app
          (SuspensionGeometry.suspension.obj X) ≫
        (integerColimitNatIso (integerTailLevel q) (integerTailPositiveIndex q + 1)).inv.app
          (SuspensionGeometry.suspension.obj X)) ≫
      (suspensionDiagonalIso (integerTailLevel q) (integerTailPositiveIndex q) X).inv = _
  rw [← Category.assoc, ← Category.assoc,
    integerDegreeIso_inv_leg _ _ (scalarLoop_integerDegree q)]
  let c := ((eqToIso
    (congrArg integerDiagonalDiagramFunctor (scalarLoop_integerDegree q))).inv.app
      (SuspensionGeometry.suspension.obj X)).app n
  let o := ((offsetDiagramNatTrans
    (integerTailLevel (integerDegree (integerTailLevel q) (integerTailPositiveIndex q + 1)))
    (integerTailPositiveIndex
      (integerDegree (integerTailLevel q) (integerTailPositiveIndex q + 1)))
    (normalizationOffset (integerTailLevel q) (integerTailPositiveIndex q + 1))).app
      (SuspensionGeometry.suspension.obj X)).app n
  let t := ((normalizationDiagramIso (integerTailLevel q)
    (integerTailPositiveIndex q + 1)).inv.app (SuspensionGeometry.suspension.obj X)).app n
  let d := (suspensionDiagonalIso (integerTailLevel q) (integerTailPositiveIndex q) X).inv
  have hn := integerColimitNatIso_inv_leg (integerTailLevel q)
    (integerTailPositiveIndex q + 1) (SuspensionGeometry.suspension.obj X) n
  have hs : diagonalLeg (integerTailLevel q) (integerTailPositiveIndex q + 1)
      (SuspensionGeometry.suspension.obj X) n ≫ d =
      (stageBackward n (integerTailLevel q) (integerTailPositiveIndex q)).app X ≫
        integerStablePiLeg q X (n + 1) :=
    suspensionColimitNatIso_inv_leg (integerTailLevel q) (integerTailPositiveIndex q) X n
  calc
    _ = c ≫ ((o ≫ t ≫ diagonalLeg (integerTailLevel q) (integerTailPositiveIndex q + 1)
        (SuspensionGeometry.suspension.obj X) n) ≫ d) := by
      simpa only [Category.assoc] using congrArg (fun a => c ≫ a ≫ d) hn
    _ = c ≫ o ≫ t ≫
        (stageBackward n (integerTailLevel q) (integerTailPositiveIndex q)).app X ≫
          integerStablePiLeg q X (n + 1) := by
      simpa only [Category.assoc] using
        congrArg (fun a => c ≫ o ≫ t ≫ a) hs

/-- The complete original scalar unit induces an isomorphism in every original integer degree. -/
theorem scalarUnit_integerPi_isIso (q : ℤ) (X : SequentialSpectrum.{u, v}) :
    IsIso ((integerStablePiFunctor q).map (SuspensionGeometry.unit.app X)) := by
  let f := (integerStablePiFunctor q).map (SuspensionGeometry.unit.app X)
  let g := (scalarLoopIntegerPiNatIso q).hom.app (SuspensionGeometry.suspension.obj X)
  let _ : IsIso g :=
    ((scalarLoopIntegerPiNatIso q).app (SuspensionGeometry.suspension.obj X)).isIso_hom
  have h : (integerSuspensionPiNatIso q).hom.app X = f ≫ g :=
    (integerSuspensionPiNatIso_hom_app q X).trans (integerSuspensionPiMap_app q X)
  let _ : IsIso (f ≫ g) := h ▸ ((integerSuspensionPiNatIso q).app X).isIso_hom
  exact IsIso.of_isIso_comp_right f g

/-- The actual original scalar unit is a pi-star equivalence for every original prespectrum. -/
theorem scalarUnit_integerPiStarEquivalence (X : SequentialSpectrum.{u, v}) :
    integerPiStarEquivalences (SuspensionGeometry.unit.app X) :=
  (integerPiStarEquivalences_iff _).mpr (fun q => scalarUnit_integerPi_isIso q X)

/-- Every original integer map is invertible exactly when its actual scalar suspension map is. -/
theorem integerPiMap_isIso_iff_suspension (q : ℤ) {X Y : SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    IsIso ((integerStablePiFunctor q).map f) ↔
      IsIso ((SuspensionGeometry.suspension ⋙ integerStablePiFunctor (q + 1)).map f) :=
  NatIso.isIso_map_iff (integerSuspensionPiNatIso q) f

/-- Actual scalar suspension preserves and reflects the original all-integer
pi-star equivalences. -/
theorem suspension_integerPiStarEquivalences_iff {X Y : SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    integerPiStarEquivalences (SuspensionGeometry.suspension.map f) ↔
      integerPiStarEquivalences f := by
  rw [integerPiStarEquivalences_iff, integerPiStarEquivalences_iff]
  change (∀ q : ℤ,
      IsIso ((SuspensionGeometry.suspension ⋙ integerStablePiFunctor q).map f)) ↔
    (∀ q : ℤ, IsIso ((integerStablePiFunctor q).map f))
  constructor
  · intro h q
    exact (integerPiMap_isIso_iff_suspension q f).mpr (h (q + 1))
  · intro h r
    have hr : (r - 1) + 1 = r := by omega
    have hs := (integerPiMap_isIso_iff_suspension (r - 1) f).mp (h (r - 1))
    exact Eq.mp
      (congrArg (fun t : ℤ =>
        IsIso ((SuspensionGeometry.suspension ⋙ integerStablePiFunctor t).map f)) hr) hs

end PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry
