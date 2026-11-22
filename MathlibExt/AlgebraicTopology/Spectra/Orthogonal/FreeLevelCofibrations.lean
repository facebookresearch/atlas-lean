/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ThomCofibrant
import MathlibExt.CategoryTheory.Enriched.FreeLifting
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSmashModel
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantTensorPowers

/-!
# Actual original orthogonal Free maps, liftings and level cofibrations

The ordinary Free functor and all its evaluated maps are the original right-oriented
enriched Free construction on OrthogonalOperatorIndex. The proved native Hom cofibrancy
supplies the tensor factor. The comparison to Thom components is the complete actual
coend comparison. No native RM equivalence or spectrum model is installed by these functions.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open CategoryTheory.Spectra HomotopicalAlgebra
open scoped MonoidalClosed CGWH.modelCategory ZeroObject

namespace CategoryTheory.Spectra.OrthogonalCoendThom

open CategoryTheory.Spectra.OrthogonalComplementBundle
attribute [local instance] HasZeroObject.zeroMorphismsOfZeroObject

/-- The entire original ordinary coefficient functor of native orthogonal Free objects. -/
def nativeFreeFunctor (n : ℕ) :
    PointedCGWH.{u, v} ⥤ EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v} :=
  EnrichedFunctorCat.Free.functor (OrthogonalOperatorIndex.ofIndex n)

/-- Evaluate the full original coefficient map at its actual native target label. -/
def nativeFreeMapValue (n k : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    nativeFreeValue.{u, v} n k X ⟶ nativeFreeValue.{u, v} n k Y :=
  EnrichedFunctorCat.component
    (EnrichedFunctorCat.Free.coefficientMap (OrthogonalOperatorIndex.ofIndex n) f)
    (OrthogonalOperatorIndex.ofIndex k)

/-- The whole original ordinary Free coefficient functor evaluated at the native target. -/
def nativeFreeValueFunctor (n k : ℕ) : PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  nativeFreeFunctor n ⋙ EnrichedFunctorCat.evaluation (OrthogonalOperatorIndex.ofIndex k)

/-- The complete evaluated coefficient map and actual Thom tensor map form an Arrow Iso. -/
def nativeFreeThomMapArrowIso (n k : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    Arrow.mk (nativeFreeMapValue.{u, v} n k f) ≅ Arrow.mk (f ▷ thom.{u, v} n k) :=
  Arrow.isoMk (nativeFreeThomComponentIso n k X) (nativeFreeThomComponentIso n k Y)
    (nativeFreeThom_coefficient_naturality n k f).symm

/-- The original symmetry carries fixed-left tensor to the actual original right Free map. -/
def nativeFreeMapSymmetryArrowIso (n k : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    Arrow.mk (nativeHom.{u, v} n k ◁ f) ≅ Arrow.mk (nativeFreeMapValue.{u, v} n k f) :=
  Arrow.isoMk (β_ (nativeHom n k) X) (β_ (nativeHom n k) Y) (by
    change (β_ (nativeHom n k) X).hom ≫ nativeFreeMapValue n k f =
      (nativeHom n k ◁ f) ≫ (β_ (nativeHom n k) Y).hom
    rw [nativeFreeMapValue, EnrichedFunctorCat.Free.coefficientMap_component]
    simpa only [id_tensorHom, tensorHom_id] using
      (braiding_naturality (𝟙 (nativeHom.{u, v} n k)) f).symm)

/-- Actual native Hom cofibrancy makes every original evaluated Free cofibration a cofibration. -/
theorem nativeFreeMapValue_mem_cofibrations (n k : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) (hf : cofibrations PointedCGWH.{u, v} f) :
    cofibrations PointedCGWH.{u, v} (nativeFreeMapValue n k f) := by
  let _ : IsCofibrant (nativeHom.{u, v} n k) := nativeHom_isCofibrant n k
  exact ((cofibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (nativeFreeMapSymmetryArrowIso n k f)).mp
      (IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_cofibrations
        (nativeHom n k) f hf)

/-- The selected pointed model marks the complete actual native Free level map as a cofibration. -/
theorem nativeFreeMapValue_cofibration (n k : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) [Cofibration f] : Cofibration (nativeFreeMapValue.{u, v} n k f) := by
  rw [HomotopicalAlgebra.cofibration_iff]
  exact nativeFreeMapValue_mem_cofibrations n k f (mem_cofibrations f)

/-- Actual native Hom cofibrancy preserves every complete original trivial Free cofibration
level. -/
theorem nativeFreeMapValue_mem_trivialCofibrations (n k : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : trivialCofibrations PointedCGWH.{u, v} f) :
    trivialCofibrations PointedCGWH.{u, v} (nativeFreeMapValue n k f) := by
  let _ : IsCofibrant (nativeHom.{u, v} n k) := nativeHom_isCofibrant n k
  exact ((trivialCofibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (nativeFreeMapSymmetryArrowIso n k f)).mp
      (IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_trivialCofibrations
        (nativeHom n k) f hf)

/-- The complete actual evaluated Free map is trivial when the original coefficient map is
trivial. -/
theorem nativeFreeMapValue_trivialCofibration (n k : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) [Cofibration f] [WeakEquivalence f] :
    trivialCofibrations PointedCGWH.{u, v} (nativeFreeMapValue n k f) :=
  nativeFreeMapValue_mem_trivialCofibrations n k f (mem_trivialCofibrations f)

/-- All actual target labels retain the original coefficient cofibration. -/
theorem nativeFreeMapValue_all_levels_cofibration (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) [Cofibration f] :
    ∀ k : ℕ, Cofibration (nativeFreeMapValue.{u, v} n k f) :=
  fun k => nativeFreeMapValue_cofibration n k f

/-- All actual target labels retain the full original trivial coefficient cofibration. -/
theorem nativeFreeMapValue_all_levels_trivial (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) [Cofibration f] [WeakEquivalence f] :
    ∀ k : ℕ, trivialCofibrations PointedCGWH.{u, v} (nativeFreeMapValue n k f) :=
  fun k => nativeFreeMapValue_trivialCofibration n k f

/-- Every genuine native Free component of a cofibrant coefficient is cofibrant. -/
theorem nativeFreeValue_isCofibrant (n k : ℕ) (X : PointedCGWH.{u, v}) [IsCofibrant X] :
    IsCofibrant (nativeFreeValue.{u, v} n k X) := by
  let _ : IsCofibrant (nativeHom.{u, v} n k) := nativeHom_isCofibrant n k
  exact IsClosedSymmetricMonoidalModelCategory.isCofibrant_tensorObj X (nativeHom n k)

/-- All original native Free object levels keep that genuine cofibrant coefficient. -/
theorem nativeFreeValue_all_levels_isCofibrant (n : ℕ) (X : PointedCGWH.{u, v})
    [IsCofibrant X] : ∀ k : ℕ, IsCofibrant (nativeFreeValue.{u, v} n k X) :=
  fun k => nativeFreeValue_isCofibrant n k X

/-- The actual Thom tensor coefficient map is a cofibration through the proved full Arrow Iso. -/
theorem thomFreeMap_mem_cofibrations (n k : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) (hf : cofibrations PointedCGWH.{u, v} f) :
    cofibrations PointedCGWH.{u, v} (f ▷ thom.{u, v} n k) :=
  ((cofibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (nativeFreeThomMapArrowIso n k f)).mp (nativeFreeMapValue_mem_cofibrations n k f hf)

/-- The full actual Thom coefficient tensor is trivial through the same original comparison. -/
theorem thomFreeMap_mem_trivialCofibrations (n k : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) (hf : trivialCofibrations PointedCGWH.{u, v} f) :
    trivialCofibrations PointedCGWH.{u, v} (f ▷ thom.{u, v} n k) :=
  ((trivialCofibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (nativeFreeThomMapArrowIso n k f)).mp (nativeFreeMapValue_mem_trivialCofibrations n k f hf)

section Liftings

variable (n : ℕ) {X Y : PointedCGWH.{u, v}}
  {F G : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}}
  (i : X ⟶ Y) (p : F ⟶ G) (u : nativeFree n X ⟶ F) (v : nativeFree n Y ⟶ G)

/-- The whole original native Free square evaluates at its actual coefficient label. -/
theorem nativeCoefficientSquare (s : CommSq u ((nativeFreeFunctor n).map i) p v) :
    CommSq
      (EnrichedFunctorCat.Free.evaluate (OrthogonalOperatorIndex.ofIndex n) X F u) i
      (EnrichedFunctorCat.component p (OrthogonalOperatorIndex.ofIndex n))
      (EnrichedFunctorCat.Free.evaluate (OrthogonalOperatorIndex.ofIndex n) Y G v) :=
  EnrichedFunctorCat.Free.coefficientSquare (OrthogonalOperatorIndex.ofIndex n) i p u v s

/-- The full native Free and actual coefficient lift spaces are in genuine bijection. -/
def nativeCoefficientLiftStructEquiv (s : CommSq u ((nativeFreeFunctor n).map i) p v) :
    s.LiftStruct ≃ (nativeCoefficientSquare n i p u v s).LiftStruct :=
  EnrichedFunctorCat.Free.coefficientLiftStructEquiv
    (OrthogonalOperatorIndex.ofIndex n) i p u v s

/-- Extend the entire coefficient lift into the original native Free natural transformation. -/
def nativeExtensionLift (s : CommSq u ((nativeFreeFunctor n).map i) p v)
    (l : (nativeCoefficientSquare n i p u v s).LiftStruct) : s.LiftStruct :=
  (nativeCoefficientLiftStructEquiv n i p u v s).symm l

/-- The entire native lift uses exactly the original Free extension function. -/
theorem nativeExtensionLift_l (s : CommSq u ((nativeFreeFunctor n).map i) p v)
    (l : (nativeCoefficientSquare n i p u v s).LiftStruct) :
    (nativeExtensionLift n i p u v s l).l =
      EnrichedFunctorCat.Free.extend (OrthogonalOperatorIndex.ofIndex n) Y F l.l :=
  EnrichedFunctorCat.Free.extendLift_l (OrthogonalOperatorIndex.ofIndex n) i p u v s l

/-- Every original native target level uses the full source-first Hom action of the lift. -/
theorem nativeExtensionLift_component (s : CommSq u ((nativeFreeFunctor n).map i) p v)
    (l : (nativeCoefficientSquare n i p u v s).LiftStruct) (k : ℕ) :
    EnrichedFunctorCat.component (nativeExtensionLift n i p u v s l).l
        (OrthogonalOperatorIndex.ofIndex k) =
      EnrichedFunctorCat.Free.extensionComponent (OrthogonalOperatorIndex.ofIndex n) Y F l.l
        (OrthogonalOperatorIndex.ofIndex k) := by
  rw [nativeExtensionLift_l]
  exact EnrichedFunctorCat.Free.extend_component
    (OrthogonalOperatorIndex.ofIndex n) Y F l.l (OrthogonalOperatorIndex.ofIndex k)

/-- The complete native lift has an actual Thom component through the proved coend inverse. -/
def nativeExtensionLiftThomComponent
    (s : CommSq u ((nativeFreeFunctor n).map i) p v)
    (l : (nativeCoefficientSquare n i p u v s).LiftStruct) (k : ℕ) :
    Y ⊗ thom.{u, v} n k ⟶ F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex k) :=
  (nativeFreeThomComponentIso n k Y).inv ≫
    EnrichedFunctorCat.component (nativeExtensionLift n i p u v s l).l
      (OrthogonalOperatorIndex.ofIndex k)

/-- Every Thom lift component is the entire original Free extension on the actual coefficient. -/
theorem nativeExtensionLiftThomComponent_eq
    (s : CommSq u ((nativeFreeFunctor n).map i) p v)
    (l : (nativeCoefficientSquare n i p u v s).LiftStruct) (k : ℕ) :
    nativeExtensionLiftThomComponent n i p u v s l k =
      thomExtensionComponent n k Y F l.l := by
  rw [nativeExtensionLiftThomComponent, nativeExtensionLift_component]
  rfl

/-- The original native Free comparison recovers the complete lifted component at every target. -/
theorem nativeExtensionLiftThomComponent_reconstruction
    (s : CommSq u ((nativeFreeFunctor n).map i) p v)
    (l : (nativeCoefficientSquare n i p u v s).LiftStruct) (k : ℕ) :
    (nativeFreeThomComponentIso n k Y).hom ≫
        nativeExtensionLiftThomComponent n i p u v s l k =
      EnrichedFunctorCat.component (nativeExtensionLift n i p u v s l).l
        (OrthogonalOperatorIndex.ofIndex k) := by
  exact (nativeFreeThomComponentIso n k Y).hom_inv_id_assoc
    (EnrichedFunctorCat.component (nativeExtensionLift n i p u v s l).l
      (OrthogonalOperatorIndex.ofIndex k))

/-- Actual coefficient evaluation of the whole lifted native map recovers the original lift. -/
theorem nativeExtensionLift_evaluate
    (s : CommSq u ((nativeFreeFunctor n).map i) p v)
    (l : (nativeCoefficientSquare n i p u v s).LiftStruct) :
    EnrichedFunctorCat.Free.evaluate (OrthogonalOperatorIndex.ofIndex n) Y F
        (nativeExtensionLift n i p u v s l).l = l.l := by
  rw [nativeExtensionLift_l, EnrichedFunctorCat.Free.evaluate_extend]

end Liftings
end CategoryTheory.Spectra.OrthogonalCoendThom
