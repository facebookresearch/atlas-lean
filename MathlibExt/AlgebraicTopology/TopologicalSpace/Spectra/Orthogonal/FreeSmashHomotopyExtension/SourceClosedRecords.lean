/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FreeSmashHomotopyExtension.OriginalSourceClosed

/-!
# Equality of right-module closed records

Identifies closed records from equality of their right-adjoint functors and dependent
adjunctions. For the selected enriched module presentation, relates closed precomposition to
adjunction conjugation under the coefficient limit and colimit hypotheses.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
noncomputable section
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.SourceTransport
universe uC vC uV vV uI vI

theorem closed_eq_of_parts {C : Type uC} [Category.{vC} C] [MonoidalCategory C] {K : C}
    (a b : Closed K) (hF : a.rightAdj = b.rightAdj) (hAdj : HEq a.adj b.adj) : a = b := by
  cases a with
  | mk F adj =>
    cases b with
    | mk F' adj' =>
      cases hF
      have h : adj = adj' := eq_of_heq hAdj
      cases h
      rfl

theorem pre_heq_of_records {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    [all : MonoidalClosed C] {K P : C} (k : Closed K) (p : Closed P)
    (hk : k = all.closed K) (hp : p = all.closed P) (f : K ⟶ P) :
    HEq (MonoidalClosed.pre f)
      (conjugateEquiv p.adj k.adj ((tensoringLeft C).map f)) := by
  subst k
  subst p
  rfl

attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits SphereModuleMappingEnd.moduleCategory
attribute [local irreducible] EnrichedDayKernel.Closed.monoidalClosed
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]
  (q : ModuleMappingR.SelectedSource V I)

/-- At one source module, the selected closed record equals the original module mapping-end closed
record. -/
def SourceClosedAtEquation (M : q.Module) : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.dayClosed
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.moduleMonoidal
  q.moduleClosed.closed M = (sourceClosed q.coefficient).closed M

theorem selectedSourceClosedAt_eq (M : q.Module) : SourceClosedAtEquation q M := by
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
  apply closed_eq_of_parts
  · exact (q.moduleClosed_ihom M).trans
      (ModuleMappingR.functor_eq_source q.monoidalData q.braidedData q.coefficientFunctor
        q.coefficientMonoidal q.coefficientBraided M)
  · exact heq_of_eq
      (ModuleMappingR.leftAdjunction_eq_source q.monoidalData q.braidedData q.coefficientFunctor
        q.coefficientMonoidal q.coefficientBraided M)




end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration.SourceTransport
