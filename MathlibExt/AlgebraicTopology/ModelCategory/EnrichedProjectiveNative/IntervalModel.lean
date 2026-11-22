/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Interval
public import MathlibExt.Topology.Category.PointedCGWH.TensorMappingAdjunction
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeIntervalModel
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarCompatibility
public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder

/-!
# The actual coefficient Quillen functor and native interval cylinders

For a genuine cofibrant native diagram, the original scalar pushout-product
at initial→X gives both coefficient-model left classes. The original native
tensor/mapping adjunction is therefore Quillen. The original interval action
has acyclic-cofibration inclusions and a weak contraction, giving its same
literal native cylinder. No Quillen, lifting, model or cylinder dictionary
is an input. The native model is the original constructor at caller B/κ.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open CategoryTheory.EnrichedFunctorCat.ScalarLeibniz
open PointedCGWH.EnrichedFunctorMapping
open PointedCGWH.EnrichedIntervalCylinder
open HomotopicalAlgebra.EnrichedProjective.Native.ScalarCompatibility
open scoped CGWH.modelCategory

namespace PointedCGWH.EnrichedIntervalCylinderModel

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  MonoidalClosed.enrichedCategorySelf

omit B in
private instance tensorPreservesInitial (T : PointedCGWH.{u, v}) :
    PreservesColimitsOfShape (Discrete PEmpty.{1})
      ((ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)).obj T) := by
  let _ : PreservesColimits (EnrichedFunctorCat.tensorLeft T :
      EnrichedFunctorCat PointedCGWH.{u, v} I ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I) :=
    (ScalarLeibniz.adjunction T).leftAdjoint_preservesColimits
  change PreservesColimitsOfShape (Discrete PEmpty.{1}) (EnrichedFunctorCat.tensorLeft T)
  infer_instance

/-- The original scalar map of a cofibrant native diagram preserves
actual coefficient cofibrations. -/
theorem scalarTensorMap_cofibration
    {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X]
    (hi : cofibrations PointedCGWH.{u, v} i) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (scalarTensorMap i X) := by
  let sq := Functor.PushoutObjObj.ofIsInitialRight
    (ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I))
      i (initial.to X) initialIsInitial
  have hj : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (initial.to X) :=
    (HomotopicalAlgebra.cofibration_iff _).mp inferInstance
  exact scalarPushoutProduct_cofibration
    i (initial.to X) hi hj sq

/-- The same original scalar map preserves actual coefficient acyclic cofibrations. -/
theorem scalarTensorMap_trivialCofibration
    {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X]
    (hi : trivialCofibrations PointedCGWH.{u, v} i) :
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (scalarTensorMap i X) := by
  let sq := Functor.PushoutObjObj.ofIsInitialRight
    (ScalarLeibniz.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I))
      i (initial.to X) initialIsInitial
  have hj : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (initial.to X) :=
    (HomotopicalAlgebra.cofibration_iff _).mp inferInstance
  exact scalarPushoutProduct_trivial_left
    i (initial.to X) hi hj sq

/-- The same actual native tensor/mapping adjunction is Quillen in its coefficient variable. -/
theorem coefficient_isQuillen
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X] :
    (tensorMappingAdjunction X).IsQuillenAdjunction where
  preservesCofibrations := by
    intro M N i hi
    exact scalarTensorMap_cofibration i X hi
  preservesTrivialCofibrations := by
    intro M N i hi
    exact scalarTensorMap_trivialCofibration i X hi

/-- Both original interval inclusions are native projective acyclic cofibrations. -/
theorem inclusion_trivialCofibration (i : Fin 2)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X] :
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (inclusion i X) := by
  have hUnit : trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)
      (scalarUnitIso X).inv := by
    exact ⟨(HomotopicalAlgebra.cofibration_iff _).mp inferInstance,
      (HomotopicalAlgebra.weakEquivalence_iff _).mp inferInstance⟩
  have hEndpoint := scalarTensorMap_trivialCofibration (IntervalCoefficient.endpoint i) X
    (IntervalCoefficient.endpoint_trivialCofibration i)
  rw [inclusion_eq]
  exact (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)).comp_mem _ _
    hUnit hEndpoint

/-- The literal original interval contraction is native level weak for each cofibrant diagram. -/
theorem projection_weakEquivalence
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X] :
    WeakEquivalence (projection X) := by
  let _ : WeakEquivalence (inclusion 0 X) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (inclusion_trivialCofibration 0 X).2
  exact weakEquivalence_of_precomp_of_fac (inclusion_projection 0 X)

/-- The same original object, inclusions and contraction form an actual native diagram cylinder. -/
def cylinder (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X] : Cylinder X where
  toPrecylinder := EnrichedIntervalCylinder.precylinder.app X
  weakEquivalence_π := projection_weakEquivalence X

/-- Every chosen native cylinder map is the literal original interval action map. -/
theorem cylinder_fields (X : EnrichedFunctorCat PointedCGWH.{u, v} I) [IsCofibrant X] :
    (cylinder X).I = EnrichedIntervalCylinder.object X ∧
      (cylinder X).i₀ = inclusion 0 X ∧ (cylinder X).i₁ = inclusion 1 X ∧
        (cylinder X).π = projection X := ⟨rfl, rfl, rfl, rfl⟩

end PointedCGWH.EnrichedIntervalCylinderModel
