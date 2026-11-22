/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.SourceClosedRecords
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.OriginalSourcePreMate

/-!
# Closed precomposition and module mapping-end maps

For right modules over a commutative monoid in a symmetric monoidal closed category,
matching selected closed records identify closed precomposition with the module
mapping-end source transformation. The selected enriched Day module source supplies
these record equalities under its colimit, product and equalizer hypotheses.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration
open scoped MonoidalClosed CategoryTheory.MonObj

namespace OrthogonalIGeneratorProbe.ChosenPre.Primitive
universe uC vC
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
  (R : C) [MonObj R] [IsCommMonObj R]

theorem pre_heq_of_original_records
    {D : Type uC} [Category.{vC} D] [MonoidalCategory D] [all : MonoidalClosed D]
    {K P : D} (k : Closed K) (p : Closed P)
    (hk : k = all.closed K) (hp : p = all.closed P) (f : K ⟶ P) :
    HEq (@MonoidalClosed.pre D _ _ P K (all.closed P) (all.closed K) f)
      (conjugateEquiv p.adj k.adj ((tensoringLeft D).map f)) := by
  subst k
  subst p
  rfl

/-- The chosen closed precomposition map is heterogeneously equal to the original right-module
source transformation. -/
def PreRecordsType (H : letI := RightModuleFree.tensorMonoidal R
    MonoidalClosed (CommutativeModuleConversion.RightModule R))
    {M M' : CommutativeModuleConversion.RightModule R} (f : M' ⟶ M) : Prop :=
  letI := RightModuleFree.tensorMonoidal R
  letI := H
  HEq (MonoidalClosed.pre f) (RightModuleMappingEnd.sourceNatTrans R f)

theorem pre_from_records (H : letI := RightModuleFree.tensorMonoidal R
    MonoidalClosed (CommutativeModuleConversion.RightModule R))
    {M M' : CommutativeModuleConversion.RightModule R}
    (hk : letI := RightModuleFree.tensorMonoidal R
      H.closed M' = (SourceTransport.sourceClosed R).closed M')
    (hp : letI := RightModuleFree.tensorMonoidal R
      H.closed M = (SourceTransport.sourceClosed R).closed M)
    (f : M' ⟶ M) : PreRecordsType R H f := by
  let := RightModuleFree.tensorMonoidal R
  let : MonoidalClosed (CommutativeModuleConversion.RightModule R) := H
  change HEq (MonoidalClosed.pre f) (RightModuleMappingEnd.sourceNatTrans R f)
  let k := (SourceTransport.sourceClosed R).closed M'
  let p := (SourceTransport.sourceClosed R).closed M
  have h := pre_heq_of_original_records k p hk.symm hp.symm f
  exact h.trans (heq_of_eq (Source.originalPreMate R f))



end OrthogonalIGeneratorProbe.ChosenPre.Primitive

namespace OrthogonalIGeneratorProbe.ChosenPre

attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits SphereModuleMappingEnd.moduleCategory
attribute [local irreducible] EnrichedDayKernel.Closed.monoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]
  (q : ModuleMappingR.SelectedSource V I)

/-- The selected source closed precomposition map is heterogeneously equal to the original module
mapping-end pre-map. -/
def SourcePreHEq {M M' : q.Module} (f : M' ⟶ M) : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  letI := q.moduleClosed
  HEq (MonoidalClosed.pre f) (RightModuleMappingEnd.sourceNatTrans q.coefficient f)

theorem sourcePre_heq {M M' : q.Module} (f : M' ⟶ M) : SourcePreHEq q f := by
  unfold SourcePreHEq
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.dayClosed
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.moduleMonoidal
  let := q.moduleClosed
  exact Primitive.pre_from_records q.coefficient q.moduleClosed
    (SourceTransport.selectedSourceClosedAt_eq q M')
    (SourceTransport.selectedSourceClosedAt_eq q M) f



end OrthogonalIGeneratorProbe.ChosenPre
