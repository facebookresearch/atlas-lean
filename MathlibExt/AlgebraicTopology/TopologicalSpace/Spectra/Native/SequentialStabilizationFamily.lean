/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.DerivedLocalMapping
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialIndexOmegaTransport

/-!
# Original sequential stabilization and every higher sphere coefficient

The original one-step family is the already constructed `StableK.stabilizationFamily`.
Its free arrows are the original unit-normalized suspension/evaluation transposes.
The full higher family retains every degree pair `(n, a)`, the original ordered
sphere power, and the entire inverse enriched-Hom comparison. Its local objects
are exactly the original sequential Omega spectra.

The derived comparisons use the constructed native level model and singular
mapping enrichment, together with the actual cofibrancy of both free endpoints.
They apply `DerivedLocalMapping.stabilization_derivedWeak_iff` and the existing
derived-locality/Omega recognition theorems. The higher-family equivalence also
uses the original successor recognition and the proved higher-power weak tests
in `IndexStabilizationTransport.Sequential`.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.SequentialSpectrum.StabilizationDerived

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- Every higher sequential stabilization retains the full original sphere-power Hom. -/
def higherFamily : NativeStabilizationFamily.{u, v}
    PointedCGWH.Spectra.Sequential.Index.{u, v} (ℕ × ℕ) where
  source na := IndexStabilizationTransport.Sequential.sequentialDegree na.1
  target na := IndexStabilizationTransport.Sequential.sequentialDegree (na.1 + na.2)
  coefficient na := TensorPower.tensorPowObj PointedCGWH.sphereOne na.2
  inclusion na := (IndexStabilizationTransport.Sequential.sequentialPowerIso na.1 na.2).inv
  coefficient_cofibrant na :=
    PointedCGWH.modelCategory.tensorPowObj_sphereOne_isCofibrant na.2
  coefficient_bound na := Actual.spherePower_bound na.2

/-- The higher-family operator action is the original complete higher sequential transpose. -/
theorem higherFamily_adjoint (X : PointedCGWH.SequentialSpectrum.{u, v}) (n a : ℕ) :
    NativeK.adjoint higherFamily (n, a) X =
      IndexStabilizationTransport.Sequential.sequentialPowerAdjoint X n a := rfl

private theorem successor_inclusion_eq_power (n : ℕ) :
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso
      PointedCGWH.sphereOne.{u, v} n).inv =
        (λ_ PointedCGWH.sphereOne.{u, v}).inv ≫
          (IndexStabilizationTransport.Sequential.sequentialPowerIso.{u, v} n 1).inv := by
  rfl

/-- The original one-circle transpose is the full power-one transpose through the actual unitor. -/
theorem higherFamily_oneStep_adjoint (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    X.adjointStructureMap n = NativeK.adjoint higherFamily (n, 1) X ≫
      (IndexStabilizationTransport.Sequential.coefficientPreIso
        ((λ_ PointedCGWH.sphereOne.{u, v}).symm)
        (X.toEnrichedFunctor.obj
          (IndexStabilizationTransport.Sequential.sequentialDegree (n + 1)))).hom := by
  let K : PointedCGWH.{u, v} := PointedCGWH.sphereOne
  let i := IndexStabilizationTransport.Sequential.sequentialDegree.{u, v} n
  let j := IndexStabilizationTransport.Sequential.sequentialDegree.{u, v} (n + 1)
  let P : PointedCGWH.{u, v} := TensorPower.tensorPowObj K 1
  let D : P ⟶ (i ⟶[PointedCGWH.{u, v}] j) :=
    (IndexStabilizationTransport.Sequential.sequentialPowerIso.{u, v} n 1).inv
  let D₁ : K ⟶ (i ⟶[PointedCGWH.{u, v}] j) :=
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso K n).inv
  let e : K ≅ P := (λ_ K).symm
  have hD : D₁ = e.hom ≫ D := successor_inclusion_eq_power n
  have hOriginal : X.adjointStructureMap n = CurrentFree.adjoint i j K D₁ X :=
    (IndexStabilizationTransport.Sequential.sequential_adjoint_eq n X).symm
  change X.adjointStructureMap n = CurrentFree.adjoint i j P D X ≫
    (MonoidalClosed.pre e.hom).app (X.toEnrichedFunctor.obj j)
  rw [hOriginal]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, CurrentFree.adjoint_uncurry,
    CurrentFree.adjoint_uncurry]
  unfold CurrentFree.action
  rw [hD, comp_whiskerRight]
  simp only [Category.assoc]

/-- All higher source transposes are weak exactly when the original one-circle maps are weak. -/
theorem higherFamily_isOmega_iff (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    NativeK.IsOmega higherFamily X ↔ X.IsOmega := by
  constructor
  · intro h
    apply (IndexStabilizationTransport.Sequential.sequential_isOmega_iff X).mp
    intro n
    have hn := h (n, 1)
    let e := IndexStabilizationTransport.Sequential.coefficientPreIso
      ((λ_ PointedCGWH.sphereOne.{u, v}).symm)
      (X.toEnrichedFunctor.obj
        (IndexStabilizationTransport.Sequential.sequentialDegree (n + 1)))
    have he : weakEquivalences PointedCGWH.{u, v} e.hom :=
      (weakEquivalences PointedCGWH.{u, v}).of_isIso _
    have hcomp := (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _ hn he
    change weakEquivalences PointedCGWH.{u, v}
      (IndexStabilizationTransport.Sequential.sequentialAdjoint X n)
    rw [IndexStabilizationTransport.Sequential.sequential_adjoint_eq]
    exact (higherFamily_oneStep_adjoint X n).symm ▸ hcomp
  · intro h na
    exact IndexStabilizationTransport.Sequential.sequentialPowerAdjoint_weak X h na.1 na.2

section Derived

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  SimplicialEnrichment.simplicialCategory
open PointedCGWH.SingularHomotopyGeometry

/-- Derived mapping by each original normalized free arrow detects its actual successor transpose. -/
theorem oneStep_derivedWeak_iff (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    SSet.realizationWeakEquivalences
        (derivedMappingPrecomp (C := PointedCGWH.SequentialSpectrum.{u, v})
          (unitStabilizationMap PointedCGWH.sphereOne n) X) ↔
      CGWH.weakHomotopyEquivalences (X.adjointStructureMap n).right := by
  have h := DerivedLocalMapping.stabilization_derivedWeak_iff
    StableK.stabilizationFamily.{u, v} n X
  have ha : NativeK.adjoint StableK.stabilizationFamily.{u, v} n X =
      X.adjointStructureMap n :=
    (IndexStabilizationTransport.Sequential.sequentialAdjoint_eq_native X n).symm.trans
      (IndexStabilizationTransport.Sequential.sequential_adjoint_eq n X)
  rw [ha] at h
  have hw : weakEquivalences PointedCGWH.{u, v} (X.adjointStructureMap n) ↔
      CGWH.weakHomotopyEquivalences (X.adjointStructureMap n).right :=
    (HomotopicalAlgebra.weakEquivalence_iff _).symm.trans
      ((PointedCGWH.weakEquivalence_iff _).trans (CGWH.modelCategory.weakEquivalence_iff _))
  have result := h.trans hw
  change SSet.realizationWeakEquivalences
    (derivedMappingPrecomp (C := PointedCGWH.SequentialSpectrum.{u, v})
      (NativeK.stabilization StableK.stabilizationFamily n) X) ↔ _ at result
  rw [StableK.stabilizationFamily_stabilization_eq_unitStabilizationMap] at result
  exact result

/-- The whole original natural-number Arrow family detects exactly sequential Omega spectra. -/
theorem oneStep_isDerivedLocal_iff (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    isDerivedLocal (fun n : ℕ =>
      Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n)) X ↔ X.IsOmega := by
  have h := (DerivedLocalMapping.isDerivedLocal_iff_isOmega
    StableK.stabilizationFamily.{u, v} X).trans
      (IndexStabilizationTransport.Sequential.sequential_isOmega_iff X)
  have hs : DerivedLocalMapping.stabilizationArrows StableK.stabilizationFamily.{u, v} =
      fun n : ℕ => Arrow.mk (unitStabilizationMap PointedCGWH.sphereOne.{u, v} n) := by
    funext n
    exact congrArg Arrow.mk (StableK.stabilizationFamily_stabilization_eq_unitStabilizationMap n)
  rw [hs] at h
  exact h

/-- The complete higher-pair stabilization Arrow family has those same original local objects. -/
theorem higherFamily_isDerivedLocal_iff (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    isDerivedLocal (DerivedLocalMapping.stabilizationArrows higherFamily.{u, v}) X ↔
      X.IsOmega :=
  (DerivedLocalMapping.isDerivedLocal_iff_isOmega higherFamily X).trans
    (higherFamily_isOmega_iff X)

/-- Original level fibrancy and the complete higher-family locality are exactly Omega structure. -/
theorem higherFamily_isLocalFibrant_iff (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    isLocalFibrant (DerivedLocalMapping.stabilizationArrows higherFamily.{u, v}) X ↔
      X.IsOmega :=
  (DerivedLocalMapping.isLocalFibrant_iff_isOmega higherFamily X).trans
    (higherFamily_isOmega_iff X)

end Derived
end PointedCGWH.SequentialSpectrum.StabilizationDerived
