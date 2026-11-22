/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeCoefficientCardinal
public import MathlibExt.CategoryTheory.Enriched.ScalarFreeTensor
public import MathlibExt.CategoryTheory.Enriched.PointwiseSizeInstances
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.CategoryTheory.Enriched.ScalarCoherence

/-!
# Bounded actual free sources and their scalar tensors

The original free/evaluation adjunction and the proved complete scalar/free
isomorphism carry actual bounded coefficient sources to the genuine native
enriched diagrams. Every selected closed transition and the original κ are
retained. No model or source-preservation dictionary is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.CoefficientCardinal
open scoped Cardinal

namespace PointedCGWH.EnrichedSource

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

private instance nativeColimits : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
  infer_instance

private theorem evaluationContinuous (a : I) :
    PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType
      (evaluation (V := PointedCGWH.{u, v}) a) where
  preservesColimitsOfShape := fun _ _ => by infer_instance

set_option backward.isDefEq.respectTransparency false in
private def freeCoyonedaIso (a : I) (T : PointedCGWH.{u, v}) :
    evaluation a ⋙ coyoneda.obj (Opposite.op T) ≅
      coyoneda.obj (Opposite.op (Free.object a T)) :=
  ((Free.adjunction a).compCoyonedaIso.app (Opposite.op T)).symm

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- A genuinely bounded coefficient gives the actual original free source at the same κ. -/
theorem free_preservesClosedColimit (a : I) (T : PointedCGWH.{u, v})
    (hT : #↥T.right ≤ Cardinal.continuum)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op (Free.object a T))) := by
  let U := evaluation (V := PointedCGWH.{u, v}) a
  let _ : PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType U :=
    evaluationContinuous a
  let _ : (E ⋙ U).IsWellOrderContinuous := inferInstance
  let _ : PreservesColimit (E ⋙ U) (coyoneda.obj (Opposite.op T)) :=
    PointedCGWH.BoundedSource.preservesClosedColimit T (carrier_bound T hT) (E ⋙ U) (hE a)
  let _ : PreservesColimit E (U ⋙ coyoneda.obj (Opposite.op T)) := inferInstance
  exact preservesColimit_of_natIso E (freeCoyonedaIso a T)

/-- The actual scalar tensor of a free source retains the original scalar/free comparison. -/
theorem scalarFree_preservesClosedColimit (a : I) (M T : PointedCGWH.{u, v})
    (hM : #↥M.right ≤ Cardinal.continuum) (hT : #↥T.right ≤ Cardinal.continuum)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E
      (coyoneda.obj (Opposite.op (tensorLeftObject M (Free.object a T)))) := by
  let _ : PreservesColimit E (coyoneda.obj (Opposite.op (Free.object a (M ⊗ T)))) :=
    free_preservesClosedColimit a (M ⊗ T) (smash_mk_le_continuum M T hM hT) E hE
  exact preservesColimit_of_natIso E (coyoneda.mapIso (Free.scalarFreeIso M T a).op)

/-- The complete scalar associator transfers the actual doubly tensored free source. -/
theorem scalarScalarFree_preservesClosedColimit (a : I) (M N T : PointedCGWH.{u, v})
    (hM : #↥M.right ≤ Cardinal.continuum) (hN : #↥N.right ≤ Cardinal.continuum)
    (hT : #↥T.right ≤ Cardinal.continuum)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I)
    [E.IsWellOrderContinuous]
    (hE : ∀ i : I, ∀ ⦃a b⦄ (φ : a ⟶ b),
      IsClosedEmbedding (ConcreteCategory.hom (component (E.map φ) i).right)) :
    PreservesColimit E (coyoneda.obj
      (Opposite.op (tensorLeftObject M (tensorLeftObject N (Free.object a T))))) := by
  let _ : PreservesColimit E
      (coyoneda.obj (Opposite.op (tensorLeftObject (M ⊗ N) (Free.object a T)))) :=
    scalarFree_preservesClosedColimit a (M ⊗ N) T
      (smash_mk_le_continuum M N hM hN) hT E hE
  exact preservesColimit_of_natIso E
    (coyoneda.mapIso (scalarAssociatorIso M N (Free.object a T)).symm.op)

end PointedCGWH.EnrichedSource
