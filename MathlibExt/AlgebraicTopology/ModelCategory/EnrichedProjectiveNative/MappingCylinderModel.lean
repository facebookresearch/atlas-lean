/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinder
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IntervalModel

/-!
# Original native mapping-cylinder weakness

For a genuine native cofibrant source, the literal original interval
inclusion makes the actual pushout target leg an acyclic cofibration. Its
same original section forces the actual original retraction to be level
weak. The result retains every native enriched evaluation at original B/κ.
No target weak predicate, supplied cylinder or factorization is an input.
Source-factor cofibrancy and stable K/localization are separate joins.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.EnrichedIntervalMappingCylinderModel

open PointedCGWH.EnrichedIntervalMappingCylinder
open PointedCGWH.EnrichedIntervalCylinder
open PointedCGWH.EnrichedIntervalCylinderModel

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  MonoidalClosed.enrichedCategorySelf

/-- The original pushout target leg is an acyclic cofibration
for a cofibrant native source. -/
theorem targetLeg_trivialCofibration
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) [IsCofibrant f.left] :
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) (targetLeg f) :=
  (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)).pushout_inr
    (inclusion 0 f.left) f.hom (inclusion_trivialCofibration 0 f.left)

/-- The same original native retraction is level weak by its actual original target section. -/
theorem retraction_weakEquivalence
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) [IsCofibrant f.left] :
    WeakEquivalence (retraction f) := by
  let _ : WeakEquivalence (targetLeg f) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (targetLeg_trivialCofibration f).2
  exact weakEquivalence_of_precomp_of_fac (targetLeg_retraction f)

/-- Every original native evaluation sees the literal same mapping-cylinder retraction as weak. -/
theorem retraction_evaluation_weak
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I)) [IsCofibrant f.left] (a : I) :
    weakEquivalences PointedCGWH.{u, v} ((EnrichedFunctorCat.evaluation a).map (retraction f)) := by
  have h : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) (retraction f) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp (retraction_weakEquivalence f)
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq] at h
  exact (HomotopicalAlgebra.EvaluationTransfer.evaluationProperty_iff
    (fun b : I => EnrichedFunctorCat.evaluation b) (weakEquivalences PointedCGWH.{u, v})
    (retraction f)).mp h a

end PointedCGWH.EnrichedIntervalMappingCylinderModel
