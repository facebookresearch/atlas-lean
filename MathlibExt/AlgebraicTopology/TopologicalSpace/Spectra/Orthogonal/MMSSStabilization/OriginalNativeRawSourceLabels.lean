/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.ShiftOmega
import MathlibExt.CategoryTheory.Enriched.SphereOperatorSourceNaturality
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialIndexStabilizationArrowTransport

/-!
# Orthogonal stabilization labels and successor adjoints

Naturality of orthogonal structure actions and their adjoints is combined with a
recursive block permutation to normalize successor labels. The formulas retain degree
reassociations and the coefficient comparison used in sequential restriction.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory BraidedCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Enriched CategoryTheory.Enriched.SphereOperator
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalNativeIndexSourceAction

open FunctionSpectrum
/-- The actual continuous original isometry category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- Its actual original direct-sum tensor. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- Its actual original pointed ordinary enrichment. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- Its complete original block symmetry. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
attribute [local instance] MonoidalClosed.enrichedCategorySelf

/-- Actual source-index maps retain the full native coefficient-first action. -/
theorem action_source (X : RightShift.Carrier.{u, v}) (n m k a : OrthogonalIndex)
    (f : RightShift.Arrow.{u, v} n m) (g : RightShift.Arrow.{u, v} (a + m) k) :
    (PointedCGWH.orthogonalSphere.{u, v} a ◁ (RightShift.bare X).map f) ≫
      RightShift.action X m k a g =
    RightShift.action X n k a ((a ◁ f) ≫ g) := by
  let d := OrthogonalIndex.enrichedMonoidalData.{u, v}
  let S := orthogonalSphereFunctor.{u, v}
  let L := orthogonalSphereMonoidalData.{u, v}
  let r := (RightShift.bare X).map f
  have hPre := coefficientAction_precompose d S L X n m k a f g
  have hSource := RightShift.Internal.action_eq_braid d S L X m k a g
  have hTarget := RightShift.Internal.action_eq_braid d S L X n k a ((a ◁ f) ≫ g)
  have hFirst := congrArg (fun h => (S.obj a ◁ r) ≫ h) hSource
  have hBraid : (S.obj a ◁ r) ≫
      (β_ (S.obj a) (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex m))).hom =
    (β_ (S.obj a) (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex n))).hom ≫
      (r ▷ S.obj a) := braiding_naturality_right (S.obj a) r
  exact hFirst.trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun h => h ≫ coefficientAction d S L X m k a g) hBraid).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun h =>
            (β_ (S.obj a) (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex n))).hom ≫ h)
            hPre).trans hTarget.symm))))

/-- The same complete source-index map gives the original full coefficient transpose. -/
theorem adjoint_source (X : RightShift.Carrier.{u, v}) (n m k a : OrthogonalIndex)
    (f : RightShift.Arrow.{u, v} n m) (g : RightShift.Arrow.{u, v} (a + m) k) :
    (RightShift.bare X).map f ≫ RightShift.adjoint X m k a g =
      RightShift.adjoint X n k a ((a ◁ f) ≫ g) := by
  exact (MonoidalClosed.curry_natural_left ((RightShift.bare X).map f)
    (RightShift.action X m k a g)).symm.trans
      (congrArg MonoidalClosed.curry (action_source X n m k a f g))

/-- The same whole target-index map retains the actual full transpose. -/
theorem adjoint_target (X : RightShift.Carrier.{u, v}) (n k l a : OrthogonalIndex)
    (f : RightShift.Arrow.{u, v} (a + n) k) (g : RightShift.Arrow.{u, v} k l) :
    RightShift.adjoint X n k a f ≫
        (ihom (PointedCGWH.orthogonalSphere.{u, v} a)).map ((RightShift.bare X).map g) =
      RightShift.adjoint X n l a (f ≫ g) :=
  RightShift.Internal.adjoint_postcompose OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} X n k l a f g

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalNativeIndexSourceAction

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory BraidedCategory
open CategoryTheory.Spectra

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalRawIndexCorrection

/-- The original continuous orthogonal isometry category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- Its original direct-sum tensor, with the complete index maps. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- Its genuine continuous block-exchange symmetry. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}

/-- The source cast retains the actual reassociation of the native next degree. -/
def lowerCast (n m : ℕ) :
    (m + (n + 1) : OrthogonalIndex) ≅ (m + n) + 1 :=
  eqToIso (Nat.add_assoc m n 1).symm

/-- The target cast retains the actual coefficient-first presentation of that same degree. -/
def upperCast (n m : ℕ) :
    (1 + (m + n) : OrthogonalIndex) ≅ m + (n + 1) :=
  eqToIso ((Nat.add_comm 1 (m + n)).trans (Nat.add_assoc m n 1))

/-- The genuine index word moves each added coordinate ahead of the original fixed level. -/
def ell : ∀ n m : ℕ, (m + n : OrthogonalIndex) ≅ m + n :=
  Nat.rec (fun m => Iso.refl (m : OrthogonalIndex))
    (fun n previous m => lowerCast n m ≪≫ (β_ (1 : OrthogonalIndex) (m + n)).symm ≪≫
      (tensorLeft (1 : OrthogonalIndex)).mapIso (previous m) ≪≫ upperCast n m)

/-- The forward word retains the native nu block label and both degree casts. -/
theorem ell_successor_label (n m : ℕ) :
    (β_ (1 : OrthogonalIndex) (m + n)).hom ≫ (lowerCast n m).inv ≫
        (ell (n + 1) m).hom =
      (1 : OrthogonalIndex) ◁ (ell n m).hom ≫ (upperCast n m).hom := by
  change (β_ (1 : OrthogonalIndex) (m + n)).hom ≫ (lowerCast n m).inv ≫
    ((lowerCast n m).hom ≫ (β_ (1 : OrthogonalIndex) (m + n)).inv ≫
      (tensorLeft (1 : OrthogonalIndex)).map (ell n m).hom ≫ (upperCast n m).hom) = _
  simp only [Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rfl

/-- The inverse word retains the same original block crossing and opposite degree transports. -/
theorem ell_successor_inverse_label (n m : ℕ) :
    (ell (n + 1) m).inv ≫ (lowerCast n m).hom ≫
        (β_ (1 : OrthogonalIndex) (m + n)).inv =
      (upperCast n m).inv ≫ (tensorLeft (1 : OrthogonalIndex)).map (ell n m).inv := by
  have hIso : (β_ (1 : OrthogonalIndex) (m + n)) ≪≫
      (lowerCast n m).symm ≪≫ ell (n + 1) m =
      (tensorLeft (1 : OrthogonalIndex)).mapIso (ell n m) ≪≫ upperCast n m := by
    apply Iso.ext
    exact ell_successor_label n m
  have hInv := congrArg
    (fun e : (1 + (m + n) : OrthogonalIndex) ≅ m + (n + 1) => e.inv) hIso
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc] using hInv


end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalRawIndexCorrection

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalRawIndexCorrection

open FunctionSpectrum OriginalNativeIndexSourceAction
open scoped MonoidalClosed
/-- The continuous isometry category used by the original orthogonal source. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original direct sum tensor on the continuous orthogonal index. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original block symmetry of the continuous orthogonal index. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
attribute [local instance] MonoidalClosed.enrichedCategorySelf

/-- Both full source and target actions retain the genuine ell label and both degree casts. -/
theorem ell_step_action (X : RightShift.Carrier.{u, v}) (n m : ℕ) :
    RightShift.action X (m + n) ((m + n) + 1) 1
        (β_ (1 : OrthogonalIndex) (m + n)).hom ≫
      (RightShift.bare X).map ((lowerCast n m).inv ≫ (ell (n + 1) m).hom) =
    (PointedCGWH.orthogonalSphere.{u, v} 1 ◁ (RightShift.bare X).map (ell n m).hom) ≫
      RightShift.action X (m + n) (m + (n + 1)) 1 (upperCast n m).hom := by
  have hTarget := RightShift.action_target X (m + n) ((m + n) + 1)
    (m + (n + 1)) 1 (β_ (1 : OrthogonalIndex) (m + n)).hom
    ((lowerCast n m).inv ≫ (ell (n + 1) m).hom)
  have hLabel := congrArg (RightShift.action X (m + n) (m + (n + 1)) 1)
    (ell_successor_label n m)
  exact hTarget.trans (hLabel.trans (action_source X (m + n) (m + n)
    (m + (n + 1)) 1 (ell n m).hom (upperCast n m).hom).symm)

/-- The full original native nu transpose retains the same ell source and target words. -/
theorem ell_step_adjoint (X : RightShift.Carrier.{u, v}) (n m : ℕ) :
    ShiftOmega.omegaMap X (m + n) 1 ≫
      (ihom (PointedCGWH.orthogonalSphere.{u, v} 1)).map
        ((RightShift.bare X).map ((lowerCast n m).inv ≫ (ell (n + 1) m).hom)) =
    (RightShift.bare X).map (ell n m).hom ≫
      RightShift.adjoint X (m + n) (m + (n + 1)) 1 (upperCast n m).hom := by
  rw [ShiftOmega.omegaMap_eq_adjoint]
  have hTarget := adjoint_target X (m + n) ((m + n) + 1)
    (m + (n + 1)) 1 (β_ (1 : OrthogonalIndex) (m + n)).hom
    ((lowerCast n m).inv ≫ (ell (n + 1) m).hom)
  have hLabel := congrArg (RightShift.adjoint X (m + n) (m + (n + 1)) 1)
    (ell_successor_label n m)
  exact hTarget.trans (hLabel.trans (adjoint_source X (m + n) (m + n)
    (m + (n + 1)) 1 (ell n m).hom (upperCast n m).hom).symm)

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalRawIndexCorrection

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalNativeIndexSourceAction

open FunctionSpectrum
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential
open CategoryTheory.Spectra.SpectrumIndexMaps
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The actual j successor transpose keeps its entire mapped isometry and coefficient Iso. -/
theorem sequentialOrthogonal_adjoint (X : RightShift.Carrier.{u, v}) (n : ℕ) :
    sequentialAdjoint ((restriction sequentialOrthogonalOperatorIndexFunctor.{u, v}).obj X) n =
      ShiftOmega.omegaMap X n 1 ≫
        (ihom (PointedCGWH.orthogonalSphere.{u, v} 1)).map
          (indexMap X (successorOrthogonalIndexIso n).hom) ≫
        (coefficientPreIso sequentialOrthogonalCoefficientIso
          (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + 1)))).hom :=
  restriction_adjoint_comparison sequentialOrthogonalOperatorIndexFunctor
    (sequentialDegree n) (sequentialDegree (n + 1))
    (OrthogonalOperatorIndex.ofIndex.{u, v} (n + 1))
    sequentialOrthogonalCoefficientIso (successorOrthogonalIndexIso n)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso
      PointedCGWH.sphereOne n).inv
    (OrthogonalOperatorIndex.nu n 1) (sequentialOrthogonal_inclusion_factor n) X

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalNativeIndexSourceAction
