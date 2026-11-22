/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.DiagonalFiberSequence
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.IntegerColimitNormalization

/-!
# Original chosen-fiber connecting maps on every integer homotopy quotient

The actual looped Serre connecting map is transported through the existing
full diagonal comparisons and the original integer tail normalization.
Every chosen fiber, original quotient map, degree cast and stage leg is
retained. No connecting or exactness result is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerSequence

open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams (zeroTo)
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
open PointedCGWH.SequentialSpectrum.StableHomotopy.DiagonalFiberSequence

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
  (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c)
  (hp : ∀ r : ℕ, fibrations PointedCGWH.{u, v} (levelMap p r))

/-- Increasing the positive group degree retains the same actual integer successor degree. -/
theorem integerDegree_succ (m k : ℕ) :
    integerDegree m (k + 1) = integerDegree m k + 1 := by
  simp only [integerDegree, Nat.cast_add, Nat.cast_one]
  omega

/-- The complete source normalization uses the original quotient and the actual degree cast. -/
def sourceNormalization (m k : ℕ) : diagonalColimitFunctor.{u, v} m (k + 1) ≅
    integerStablePiFunctor (integerDegree m k + 1) :=
  integerColimitNatIso m (k + 1) ≪≫
    eqToIso (congrArg integerStablePiFunctor (integerDegree_succ m k))

/-- Both complete source-normalization functions preserve every original spectrum map. -/
theorem sourceNormalization_hom_naturality (m k : ℕ)
    {A B : PointedCGWH.SequentialSpectrum.{u, v}} (f : A ⟶ B) :
    (diagonalColimitFunctor m (k + 1)).map f ≫ (sourceNormalization m k).hom.app B =
      (sourceNormalization m k).hom.app A ≫
        (integerStablePiFunctor (integerDegree m k + 1)).map f :=
  (sourceNormalization m k).hom.naturality f

/-- The inverse source normalization retains the actual original input map. -/
theorem sourceNormalization_inv_naturality (m k : ℕ)
    {A B : PointedCGWH.SequentialSpectrum.{u, v}} (f : A ⟶ B) :
    (integerStablePiFunctor (integerDegree m k + 1)).map f ≫
        (sourceNormalization m k).inv.app B =
      (sourceNormalization m k).inv.app A ≫ (diagonalColimitFunctor m (k + 1)).map f :=
  (sourceNormalization m k).inv.naturality f

/-- The same original connecting quotient has its complete normalized integer group map. -/
def normalizedConnecting (m k : ℕ) :
    (integerStablePiFunctor (integerDegree m k + 1)).obj Y ⟶
      (integerStablePiFunctor (integerDegree m k)).obj c.pt :=
  (sourceNormalization m k).inv.app Y ≫ diagonalConnectingMap p c hc hp m k ≫
    (integerColimitNatIso m k).hom.app c.pt

/-- The exact original connecting quotient is recovered through both full normalizations. -/
theorem normalizedConnecting_reconstruction (m k : ℕ) :
    diagonalConnectingMap p c hc hp m k ≫ (integerColimitNatIso m k).hom.app c.pt =
      (sourceNormalization m k).hom.app Y ≫ normalizedConnecting p c hc hp m k := by
  rw [normalizedConnecting, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- Every original source quotient leg retains the literal looped connecting stage word. -/
theorem normalizedConnecting_leg (m k n : ℕ) :
    diagonalLeg m (k + 1) Y n ≫ (sourceNormalization m k).hom.app Y ≫
        normalizedConnecting p c hc hp m k =
      diagonalLeg m (k + 1) Y n ≫ diagonalConnectingMap p c hc hp m k ≫
        (integerColimitNatIso m k).hom.app c.pt := by
  rw [← normalizedConnecting_reconstruction p c hc hp m k]

/-- Exactness at the original integer fiber quotient retains the original projection map. -/
theorem normalized_exact_at_fiber (m k : ℕ) :
    Function.MulExact (normalizedConnecting p c hc hp m k).hom
      ((integerStablePiFunctor (integerDegree m k)).map c.fst).hom := by
  apply GrpCat.mulExact_of_iso_ladder
    ((sourceNormalization m k).app Y).symm
    ((integerColimitNatIso m k).app c.pt).symm
    ((integerColimitNatIso m k).app X).symm
    (normalizedConnecting p c hc hp m k)
    ((integerStablePiFunctor (integerDegree m k)).map c.fst)
    (diagonalConnectingMap p c hc hp m k)
    ((diagonalColimitFunctor m k).map c.fst)
  · change ((sourceNormalization m k).inv.app Y ≫
        diagonalConnectingMap p c hc hp m k ≫ (integerColimitNatIso m k).hom.app c.pt) ≫
      (integerColimitNatIso m k).inv.app c.pt =
        (sourceNormalization m k).inv.app Y ≫ diagonalConnectingMap p c hc hp m k
    let a := (sourceNormalization m k).inv.app Y
    let d := diagonalConnectingMap p c hc hp m k
    let e := (integerColimitNatIso m k).app c.pt
    change (a ≫ d ≫ e.hom) ≫ e.inv = a ≫ d
    calc
      _ = a ≫ ((d ≫ e.hom) ≫ e.inv) := Category.assoc a (d ≫ e.hom) e.inv
      _ = a ≫ (d ≫ (e.hom ≫ e.inv)) :=
        congrArg (fun z => a ≫ z) (Category.assoc d e.hom e.inv)
      _ = a ≫ (d ≫ 𝟙 _) := congrArg (fun z => a ≫ (d ≫ z)) e.hom_inv_id
      _ = a ≫ d := congrArg (fun z => a ≫ z) (Category.comp_id d)
  · exact (integerColimitNatIso m k).inv.naturality c.fst
  · exact diagonal_exact_at_fiber p c hc hp m k

/-- Exactness at the original integer base quotient retains the full original spectrum map. -/
theorem normalized_exact_at_base (m k : ℕ) :
    Function.MulExact ((integerStablePiFunctor (integerDegree m k + 1)).map p).hom
      (normalizedConnecting p c hc hp m k).hom := by
  apply GrpCat.mulExact_of_iso_ladder
    ((sourceNormalization m k).app X).symm
    ((sourceNormalization m k).app Y).symm
    ((integerColimitNatIso m k).app c.pt).symm
    ((integerStablePiFunctor (integerDegree m k + 1)).map p)
    (normalizedConnecting p c hc hp m k)
    ((diagonalColimitFunctor m (k + 1)).map p)
    (diagonalConnectingMap p c hc hp m k)
  · exact (sourceNormalization m k).inv.naturality p
  · change ((sourceNormalization m k).inv.app Y ≫
        diagonalConnectingMap p c hc hp m k ≫ (integerColimitNatIso m k).hom.app c.pt) ≫
      (integerColimitNatIso m k).inv.app c.pt =
        (sourceNormalization m k).inv.app Y ≫ diagonalConnectingMap p c hc hp m k
    let a := (sourceNormalization m k).inv.app Y
    let d := diagonalConnectingMap p c hc hp m k
    let e := (integerColimitNatIso m k).app c.pt
    change (a ≫ d ≫ e.hom) ≫ e.inv = a ≫ d
    calc
      _ = a ≫ ((d ≫ e.hom) ≫ e.inv) := Category.assoc a (d ≫ e.hom) e.inv
      _ = a ≫ (d ≫ (e.hom ≫ e.inv)) :=
        congrArg (fun z => a ≫ z) (Category.assoc d e.hom e.inv)
      _ = a ≫ (d ≫ 𝟙 _) := congrArg (fun z => a ≫ (d ≫ z)) e.hom_inv_id
      _ = a ≫ d := congrArg (fun z => a ≫ z) (Category.comp_id d)
  · exact diagonal_exact_at_base p c hc hp m k

end PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerSequence
