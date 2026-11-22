/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereSmashGammaGeometry
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OperatorStabilizationK
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ThomCofibrant
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CofibrantFree
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeSphereHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IntervalGood
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHHomotopyRelLocalization
import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma

/-!
# The actual orthogonal free-sphere rotation maps

The complete coefficient-first native coend-to-Thom comparison carries the
original identity and block-transposition frame maps. Their actual based
rotation homotopy gives equal native free-map images in the original level
homotopy category. The original good native cylinder then realizes those
two maps with their whole native endpoint and full enriched-Hom equations.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalComplementBundle CategoryTheory.Spectra.OrthogonalCoendThom
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalFreeSphereSmashFlatness

open CategoryTheory.Spectra.OrthogonalSmashGammaGeometry

/-- The same original native free object with the actual representation-sphere coefficient. -/
abbrev sphereFree (n : ℕ) := nativeFree.{u, v} n (PointedCGWH.orthogonalSphere.{u, v} n)

/-- The actual whole native free value retains its complete coefficient-first operator Hom. -/
abbrev sphereFreeValue (n k : ℕ) :=
  nativeFreeValue.{u, v} n k (PointedCGWH.orthogonalSphere.{u, v} n)

/-- The complete original coefficient-first comparison followed by the actual ambient braid. -/
def valueIso (n k : ℕ) : sphereFreeValue.{u, v} n k ≅
    thom.{u, v} n k ⊗ PointedCGWH.orthogonalSphere.{u, v} n :=
  nativeFreeThomComponentIso n k (PointedCGWH.orthogonalSphere n) ≪≫
    β_ (PointedCGWH.orthogonalSphere n) (thom n k)

/-- Every original frame gives its actual whole native coefficient map. -/
def coefficientMap (n k a : ℕ) (g : Frame n k a) :
    PointedCGWH.orthogonalSphere.{u, v} k ⟶ sphereFreeValue.{u, v} n k :=
  pointedSplit n k a g ≫ (valueIso n k).inv

/-- The actual original free/evaluation adjunction extends the full coefficient map. -/
def spectrumMap (n k a : ℕ) (g : Frame n k a) : sphereFree.{u, v} k ⟶ sphereFree.{u, v} n :=
  Free.extend (OrthogonalOperatorIndex.ofIndex k) (PointedCGWH.orthogonalSphere k)
    (sphereFree n) (coefficientMap n k a g)

/-- Every output component retains its complete original enriched Hom and target action. -/
theorem spectrumMap_component (n k a l : ℕ) (g : Frame n k a) :
    component (spectrumMap.{u, v} n k a g) (OrthogonalOperatorIndex.ofIndex l) =
      (coefficientMap n k a g ⊗ₘ
        𝟙 (OrthogonalOperatorIndex.ofIndex k ⟶[PointedCGWH.{u, v}] OrthogonalOperatorIndex.ofIndex l)) ≫
        MonoidalClosed.uncurry ((sphereFree n).toEnrichedFunctor.map
          (OrthogonalOperatorIndex.ofIndex k) (OrthogonalOperatorIndex.ofIndex l)) :=
  Free.extend_component (OrthogonalOperatorIndex.ofIndex k) (PointedCGWH.orthogonalSphere k)
    (sphereFree n) (coefficientMap n k a g) (OrthogonalOperatorIndex.ofIndex l)

/-- The original identity-slot evaluation recovers the entire original coefficient. -/
theorem spectrumMap_evaluate (n k a : ℕ) (g : Frame n k a) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex k) (PointedCGWH.orthogonalSphere k)
        (sphereFree n) (spectrumMap.{u, v} n k a g) = coefficientMap n k a g :=
  Free.evaluate_extend _ _ _ _

/-- The actual native coefficient homotopy retains the two original complete frame maps. -/
def coefficientHomotopyRel (n : ℕ) :
    ContinuousMap.HomotopyRel
      (ConcreteCategory.hom (C := CGWH.{u, v})
        (coefficientMap.{u, v} n (n + n) n (OrthogonalMatrixHom.id (n + n))).right)
      (ConcreteCategory.hom (C := CGWH.{u, v})
        (coefficientMap.{u, v} n (n + n) n (OrthogonalIndex.blockSwap n n)).right)
      (Set.range (ConcreteCategory.hom (C := CGWH.{u, v})
        (PointedCGWH.orthogonalSphere.{u, v} (n + n)).hom)) :=
  (pointedSplitHomotopyRel n).compContinuousMap
    (ConcreteCategory.hom (C := CGWH.{u, v}) (valueIso n (n + n)).inv.right)

/-- Every original interval/sphere point keeps the full proper native coefficient formula. -/
theorem coefficientHomotopyRel_apply (n : ℕ) (t : unitInterval)
    (x : (PointedCGWH.orthogonalSphere.{u, v} (n + n)).right) :
    coefficientHomotopyRel.{u, v} n (t, x) =
      (valueIso n (n + n)).inv.right (pointedSplitHomotopy n (t, x)) := rfl

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The full original native free-sphere source is cofibrant in the same original level model. -/
theorem sphereFree_isCofibrant (n : ℕ) : IsCofibrant (sphereFree.{u, v} n) := by
  let _ : IsCofibrant (PointedCGWH.orthogonalSphere.{u, v} n) := originalOrthogonalSphere_isCofibrant n
  exact freeAt_obj_isCofibrant (OrthogonalOperatorIndex.ofIndex n) (PointedCGWH.orthogonalSphere n)

private theorem extend_leftHomotopyRel (a : OrthogonalOperatorIndex.{u, v})
    (K : PointedCGWH.{u, v}) [IsCofibrant K] (X : Actual.OrthogonalCarrier.{u, v})
    (f g : K ⟶ X.toEnrichedFunctor.obj a) (h : LeftHomotopyRel f g) :
    LeftHomotopyRel (Free.extend a K X f) (Free.extend a K X g) := by
  let _ : (Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
    freeAtEvaluation_isQuillenAdjunction a
  convert QuillenOrdinaryHoHom.inverseAdjunct_leftHomotopyRel (Free.adjunction a) h using 1 <;>
    rw [Free.adjunction_homEquiv] <;> rfl

/-- The original two whole native free maps are equal in the same original level homotopy category. -/
theorem spectrumMap_rotation_map_eq (n : ℕ) :
    (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map
        (spectrumMap n (n + n) n (OrthogonalMatrixHom.id (n + n))) =
      (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map
        (spectrumMap n (n + n) n (OrthogonalIndex.blockSwap n n)) := by
  let K := PointedCGWH.orthogonalSphere.{u, v} (n + n)
  let a := OrthogonalOperatorIndex.ofIndex (n + n)
  let X := sphereFree.{u, v} n
  let _ : IsCofibrant K := originalOrthogonalSphere_isCofibrant (n + n)
  have h := extend_leftHomotopyRel a K X
    (coefficientMap n (n + n) n (OrthogonalMatrixHom.id (n + n)))
    (coefficientMap n (n + n) n (OrthogonalIndex.blockSwap n n))
    (PointedCGWH.leftHomotopyRel_of_homotopyRel _ _ (coefficientHomotopyRel n))
  exact (h.factorsThroughLocalization Actual.OrthogonalCarrier.{u, v}).map_eq
    (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v})

/-- The same original good native cylinder realizes the two complete native rotation maps. -/
def nativeRotationHomotopy (n : ℕ) :
    { H : PointedCGWH.EnrichedIntervalCylinder.object (sphereFree.{u, v} (n + n)) ⟶ sphereFree.{u, v} n //
      PointedCGWH.EnrichedIntervalCylinder.inclusion 0 (sphereFree (n + n)) ≫ H =
        spectrumMap n (n + n) n (OrthogonalMatrixHom.id (n + n)) ∧
      PointedCGWH.EnrichedIntervalCylinder.inclusion 1 (sphereFree (n + n)) ≫ H =
        spectrumMap n (n + n) n (OrthogonalIndex.blockSwap n n) } := by
  let _ : IsCofibrant (sphereFree.{u, v} (n + n)) := sphereFree_isCofibrant (n + n)
  let P := PointedCGWH.EnrichedIntervalCylinderModel.cylinder (sphereFree.{u, v} (n + n))
  let _ : P.IsGood := PointedCGWH.EnrichedIntervalCylinderModel.cylinder_isGood _
  have h : LeftHomotopyRel
      (spectrumMap n (n + n) n (OrthogonalMatrixHom.id (n + n)))
      (spectrumMap n (n + n) n (OrthogonalIndex.blockSwap n n)) :=
    (LeftHomotopyRel.iff_map_eq
      (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}) _ _).mpr
      (spectrumMap_rotation_map_eq n)
  let H := h.leftHomotopy P
  exact ⟨H.h, H.h₀, H.h₁⟩

/-- The actual whole native homotopy has its full original enriched-Hom naturality. -/
theorem nativeRotationHomotopy_fullHom (n : ℕ) (a b : OrthogonalOperatorIndex.{u, v}) :
    MonoidalClosed.uncurry
        ((PointedCGWH.EnrichedIntervalCylinder.object (sphereFree.{u, v} (n + n))).toEnrichedFunctor.map a b) ≫
        component (nativeRotationHomotopy n).val b =
      (component (nativeRotationHomotopy n).val a ⊗ₘ 𝟙 (a ⟶[PointedCGWH.{u, v}] b)) ≫
        MonoidalClosed.uncurry ((sphereFree.{u, v} n).toEnrichedFunctor.map a b) :=
  (nativeRotationHomotopy n).val.uncurriedNaturality a b

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalFreeSphereSmashFlatness
