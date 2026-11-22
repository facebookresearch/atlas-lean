/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeIntervalBoundary
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeIntervalModel
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHGeneratorSourceSmallness
public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder

/-!
# The original native good coefficient cylinder and its same-cardinal source

The joint endpoints inherit cofibrancy from the original native costar
boundary generator. Its actual source preserves the same original closed
continuous chain colimits through the whole source Arrow isomorphism. The
original interval and maps therefore give a genuine good cylinder of the
native pointed tensor unit. No cylinder/model/source dictionary is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.IntervalCoefficient

/-- Each original costar boundary is a cofibration in the actual native pointed model. -/
theorem originalBoundary_cofibration (n : ℕ) :
    cofibrations PointedCGWH.{u, v}
      ((Under.costar CGWH.point.{u, v}).map (CGWH.realizedBoundaryInclusion.{v, u} n)) := by
  have h : CGWH.realizedBoundaryInclusions.{u, v}.rlp.llp
      (CGWH.realizedBoundaryInclusion.{v, u} n) :=
    CGWH.realizedBoundaryInclusions.le_llp_rlp _ (CGWH.boundary_mem_realizedBoundaryInclusions n)
  change CGWH.cofibrantGenerationData.{u, v}.I.rlp.llp
    (CGWH.realizedBoundaryInclusion.{v, u} n) at h
  rw [CGWH.cofibrantGenerationData.I_rlp, trivialFibrations_llp] at h
  exact (Under.costarAdjForget_isQuillenAdjunction CGWH.point.{u, v}).preservesCofibrations _ h

/-- The literal native joint endpoint arrow is an actual pointed cofibration. -/
theorem jointEndpoints_cofibration : Cofibration jointEndpoints.{u, v} :=
  (HomotopicalAlgebra.cofibration_iff _).mpr
    ((jointEndpoints_property_iff (cofibrations PointedCGWH.{u, v})).mpr
      (originalBoundary_cofibration 1))

set_option backward.isDefEq.respectTransparency false in
/-- The actual joint-endpoint source preserves the original κ closed-chain colimit. -/
theorem jointSource_preservesClosedColimit
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [E.IsWellOrderContinuous]
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (ConcreteCategory.hom (E.map φ).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op
      ((𝟙_ PointedCGWH.{u, v}) ⨿ (𝟙_ PointedCGWH.{u, v})))) := by
  let g := (Under.costar CGWH.point.{u, v}).map (CGWH.realizedBoundaryInclusion.{v, u} 1)
  have hg : (CGWH.realizedBoundaryInclusions.{u, v}.strictMap
      (Under.costar CGWH.point.{u, v})) g :=
    .map (CGWH.boundary_mem_realizedBoundaryInclusions 1)
  let _ : PreservesColimit E (coyoneda.obj (Opposite.op
      (Arrow.leftFunc.obj (Arrow.mk ((Under.costar CGWH.point.{u, v}).map
        (CGWH.realizedBoundaryInclusion.{v, u} 1)))))) :=
    PointedCGWH.realizedBoundarySource_preservesClosedColimit g hg E hE
  exact preservesColimit_of_natIso E
    (coyoneda.mapIso (Arrow.leftFunc.mapIso jointBoundaryArrowIso.{u, v}).op)

/-- The original native interval and both original endpoints give a genuine unit cylinder. -/
def coefficientCylinder : Cylinder (𝟙_ PointedCGWH.{u, v}) where
  I := interval
  i₀ := endpoint 0
  i₁ := endpoint 1
  π := augmentation
  i₀_π := endpoint_augmentation 0
  i₁_π := endpoint_augmentation 1
  weakEquivalence_π := augmentation_weakEquivalence

/-- The entire original joint endpoint map makes this same native cylinder good. -/
theorem coefficientCylinder_isGood : coefficientCylinder.{u, v}.IsGood where
  cofibration_i := jointEndpoints_cofibration

/-- Every selected cylinder object and map is the original native one. -/
theorem coefficientCylinder_fields :
    coefficientCylinder.{u, v}.I = interval.{u, v} ∧
      coefficientCylinder.{u, v}.i₀ = endpoint.{u, v} 0 ∧
        coefficientCylinder.{u, v}.i₁ = endpoint.{u, v} 1 ∧
          coefficientCylinder.{u, v}.π = augmentation.{u, v} := ⟨rfl, rfl, rfl, rfl⟩

end PointedCGWH.IntervalCoefficient
