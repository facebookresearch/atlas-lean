/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricScalarSmashCoefficientBase

/-!
# Whole original free-source functor transport

The actual Day free functor equals its original coefficient-sequence/free-module
recipe before an object or coefficient map is selected. That entire equality
transports both original closed pre-map endpoints and the complete operator
whiskering. The homogeneous coefficient comparison is a separate obligation.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalCategory MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricFreeSourceFunctorTransport.Primitive
universe uC vC uP vP uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
  {P : Type uP} [Category.{vP} P] {D : Type uD} [Category.{vD} D]
  (A : CommMon C) (E : Mod C A.X ≌ D)
/-- The module tensor used to transport the whole free-functor equality to the native source
pre-map. -/
local instance functorEqModuleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
/-- The module internal Hom structure used by the whole free-functor precomposition comparison. -/
local instance functorEqModuleClosed : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A

/-- Equality of the entire original free functor transports its complete closed pre-map and both operator
whiskers. -/
theorem whiskeredFreePre_of_functor_eq (L : P ⥤ Mod C A.X) (K : P ⥤ C)
    (hL : L = K ⋙ Mod.free A.X) {T T' : P} (p : T ⟶ T') :
    HEq (Functor.whiskerLeft E.inverse
      (Functor.whiskerRight (MonoidalClosed.pre (L.map p)) E.functor))
      (Functor.whiskerLeft E.inverse
        (Functor.whiskerRight (FreeModuleSource.pre A (K.map p)) E.functor)) := by
  cases hL
  rfl

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricFreeSourceFunctorTransport.Primitive

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricFreeSourceFunctorTransport

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric

private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}

private theorem A_eq_original : A.{u, v} = PointedCGWH.sphereSequenceCommMon.{u, v} := rfl

private abbrev E := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}

private theorem E_eq_original :
    E.{u, v} = PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v} :=
  rfl

open PointedCGWH.SymmetricModulePresentation
open NativeOmegaRecovery.NativeSymmetricFreeFunction
open NativeOmegaRecovery.NativeScalarCoefficient

attribute [local irreducible] moduleComparisonNat moduleOperatorComparison comparison

/-- The original coefficient sequence functor retains both the evaluation adjoint and full Day wrapper. -/
def coefficientSequenceFunctor (r : I) : V.{u, v} ⥤ PointedCGWH.SymmetricSequence.{u, v} :=
  evaluationLeftAdjoint V.{u, v} r ⋙ (DayFunctor.equiv I V.{u, v}).symm.functor

/-- Every original coefficient arrow has the original representable sequence map. -/
theorem coefficientSequenceFunctor_map (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    (coefficientSequenceFunctor r).map p = DayFreeCoefficient.freeSequenceMap r p := rfl

/-- The complete original Day free functor is the coefficient-sequence functor followed by the original module
free functor. -/
theorem dayFree_eq_coefficientFree (r : I) :
    Mod.dayFreeAt S.{u, v} r = coefficientSequenceFunctor r ⋙ Mod.free A.{u, v}.X := by
  have hL := NativeOmegaRecovery.NativeSymmetricSourceMatch.chosenFreeFunctor_eq_recipe.{u, v} r
  have hFree := congrArg (fun L => coefficientSequenceFunctor r ⋙ L)
    (coefficientFreeFunctor_eq_original.{u, v})
  exact hL.trans hFree.symm

/-- The tensor on modules over the original commutative symmetric sphere sequence. -/
local instance actualModuleMonoidal : MonoidalCategory (OriginalModule.{u, v}) :=
  Mod.instMonoidalCategory A.{u, v}
/-- The internal Hom structure on modules over the original commutative symmetric sphere sequence. -/
local instance actualModuleClosed : MonoidalClosed (OriginalModule.{u, v}) :=
  Mod.instMonoidalClosed A.{u, v}

set_option maxHeartbeats 500000 in
-- The original full free functor equality fixes both closed pre-map endpoints.
/-- The complete original operator pre-map retains both original source endpoints before any native component
is selected. -/
theorem precompose_whole_heq (r : I) {T T' : V.{u, v}} (p : T ⟶ T') :
    type_of% (Primitive.whiskeredFreePre_of_functor_eq A.{u, v} E.{u, v}
      (Mod.dayFreeAt S.{u, v} r) (coefficientSequenceFunctor r) (dayFree_eq_coefficientFree r) p) :=
  Primitive.whiskeredFreePre_of_functor_eq A.{u, v} E.{u, v}
    (Mod.dayFreeAt S.{u, v} r) (coefficientSequenceFunctor r) (dayFree_eq_coefficientFree r) p

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricFreeSourceFunctorTransport
