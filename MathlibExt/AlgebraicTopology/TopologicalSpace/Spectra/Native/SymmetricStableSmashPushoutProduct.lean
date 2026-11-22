/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricStableGeneratorProducts
import MathlibExt.CategoryTheory.Monoidal.PushoutProductFunctor
import MathlibExt.CategoryTheory.Monoidal.FreePairTransport

/-!
# Original symmetric smash pushout products

The free pair comparison transports the literal coefficient pushout and both
of its original legs. The three free functors retain their separate degrees;
the output free functor is not assumed to be monoidal.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped MonoidalCategory

open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CGWH.modelCategory CGWH.limits CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash

universe u v

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev Operator := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} Operator.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

private theorem originalBoundary_cof {M N : V.{u, v}} (i : M ⟶ N)
    (hi : PointedCGWH.realizedBoundaryInclusions i) : cofibrations V.{u, v} i := by
  have h := PointedCGWH.realizedBoundaryInclusions.{u, v}.le_llp_rlp i hi
  have hI : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
      trivialFibrations V.{u, v} := PointedCGWH.cofibrantGenerationData.{u, v}.I_rlp
  rwa [hI, trivialFibrations_llp] at h

private theorem originalHorn_trivial {M N : V.{u, v}} (i : M ⟶ N)
    (hi : PointedCGWH.realizedHornInclusions i) : trivialCofibrations V.{u, v} i := by
  have h := PointedCGWH.realizedHornInclusions.{u, v}.le_llp_rlp i hi
  have hJ : PointedCGWH.realizedHornInclusions.{u, v}.rlp =
      fibrations V.{u, v} := PointedCGWH.cofibrantGenerationData.{u, v}.J_rlp
  rwa [hJ, fibrations_llp] at h

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The literal native free-coefficient pushout product is the original
coefficient pushout product carried by the actual output free functor. -/
def freeCoefficientPushoutProductIso (r s : I)
    {M M' N N' : V.{u, v}} (i : M ⟶ M') (j : N ⟶ N') :
    (Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj.{u, v} (s ⊗ r))).mapArrow.obj
        (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j) ≅
      CategoryTheory.Arrow.mk (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} r) i) □
        CategoryTheory.Arrow.mk
          (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} s) j) := by
  let F : V.{u, v} ⥤ Carrier.{u, v} :=
    Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj.{u, v} r)
  let G : V.{u, v} ⥤ Carrier.{u, v} :=
    Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj.{u, v} s)
  let L : V.{u, v} ⥤ Carrier.{u, v} :=
    Free.functor (V := V.{u, v}) (PointedCGWH.symmetricOperatorObj.{u, v} (s ⊗ r))
  let _ : L.IsLeftAdjoint :=
    (Free.adjunction (V := V.{u, v})
      (PointedCGWH.symmetricOperatorObj.{u, v} (s ⊗ r))).isLeftAdjoint
  let e : F.prod G ⋙ tensor Carrier.{u, v} ≅ tensor V.{u, v} ⋙ L := freePairBifunctorIso r s
  exact CategoryTheory.FreePairTransport.pairPushoutProductIso F G L e i j

/-- Every pair of actual coefficient cofibrations gives a native smash
cofibration, through the original coefficient pushout and original Free. -/
theorem freeCoefficientPushoutProduct_cofibrations (r s : I)
    {M M' N N' : V.{u, v}} (i : M ⟶ M') (j : N ⟶ N')
    (hi : cofibrations V.{u, v} i) (hj : cofibrations V.{u, v} j) :
    cofibrations Carrier.{u, v}
      (CategoryTheory.Arrow.mk
          (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} r) i) □
        CategoryTheory.Arrow.mk
          (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} s) j)).hom := by
  have hBase : cofibrations V.{u, v}
      (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom :=
    IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct i j hi hj
  have hNative := freeAt_map_mem_cofibrations
    (PointedCGWH.symmetricOperatorObj.{u, v} (s ⊗ r))
    (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom hBase
  exact ((cofibrations Carrier.{u, v}).arrow_mk_iso_iff
    (freeCoefficientPushoutProductIso r s i j)).mp hNative

/-- An original coefficient trivial cofibration in the first variable
gives the full original native level trivial pushout product. -/
theorem freeCoefficientPushoutProduct_trivial_left (r s : I)
    {M M' N N' : V.{u, v}} (i : M ⟶ M') (j : N ⟶ N')
    (hi : trivialCofibrations V.{u, v} i) (hj : cofibrations V.{u, v} j) :
    trivialCofibrations Carrier.{u, v}
      (CategoryTheory.Arrow.mk
          (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} r) i) □
        CategoryTheory.Arrow.mk
          (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} s) j)).hom := by
  have hBase : trivialCofibrations V.{u, v}
      (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom :=
    IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left i j hi hj
  have hNative := freeAt_map_mem_trivialCofibrations
    (PointedCGWH.symmetricOperatorObj.{u, v} (s ⊗ r))
    (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom hBase
  exact ((trivialCofibrations Carrier.{u, v}).arrow_mk_iso_iff
    (freeCoefficientPushoutProductIso r s i j)).mp hNative

/-- An original coefficient trivial cofibration in the second variable
gives the full original native level trivial pushout product. -/
theorem freeCoefficientPushoutProduct_trivial_right (r s : I)
    {M M' N N' : V.{u, v}} (i : M ⟶ M') (j : N ⟶ N')
    (hi : cofibrations V.{u, v} i) (hj : trivialCofibrations V.{u, v} j) :
    trivialCofibrations Carrier.{u, v}
      (CategoryTheory.Arrow.mk
          (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} r) i) □
        CategoryTheory.Arrow.mk
          (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} s) j)).hom := by
  have hBase : trivialCofibrations V.{u, v}
      (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom :=
    IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right i j hi hj
  have hNative := freeAt_map_mem_trivialCofibrations
    (PointedCGWH.symmetricOperatorObj.{u, v} (s ⊗ r))
    (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom hBase
  exact ((trivialCofibrations Carrier.{u, v}).arrow_mk_iso_iff
    (freeCoefficientPushoutProductIso r s i j)).mp hNative

/-- The complete original I-by-I family, with all operator objects and
every realized boundary, gives actual native smash cofibrations. -/
theorem levelI_pushoutProduct_levelI_cofibrations :
    MorphismProperty.PushoutProductLe
      (NativeK.levelI (I := Operator.{u, v})) (NativeK.levelI (I := Operator.{u, v}))
      (cofibrations Carrier.{u, v}) := by
  apply CategoryTheory.FreePairTransport.generatorPair_pushoutProductLe
    (fun a : Operator.{u, v} => Free.functor (V := V.{u, v}) a)
    (fun a : Operator.{u, v} => Free.functor (V := V.{u, v}) a)
    PointedCGWH.realizedBoundaryInclusions PointedCGWH.realizedBoundaryInclusions
    (cofibrations Carrier.{u, v})
  intro a b M M' N N' i j hi hj
  have ha : PointedCGWH.symmetricOperatorObj.{u, v} a.asIndex = a := rfl
  have hb : PointedCGWH.symmetricOperatorObj.{u, v} b.asIndex = b := rfl
  have hA : CategoryTheory.Arrow.mk ((Free.functor (V := V.{u, v}) a).map i) =
      CategoryTheory.Arrow.mk
        (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} a.asIndex) i) :=
    congrArg (fun x : Operator.{u, v} => CategoryTheory.Arrow.mk (Free.coefficientMap x i)) ha.symm
  have hB : CategoryTheory.Arrow.mk ((Free.functor (V := V.{u, v}) b).map j) =
      CategoryTheory.Arrow.mk
        (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} b.asIndex) j) :=
    congrArg (fun x : Operator.{u, v} => CategoryTheory.Arrow.mk (Free.coefficientMap x j)) hb.symm
  exact CategoryTheory.FreePairTransport.pushoutProduct_mem_of_pairArrow_eq (cofibrations Carrier.{u, v})
    ((Free.functor (V := V.{u, v}) a).map i) ((Free.functor (V := V.{u, v}) b).map j)
    _ _ hA hB
    (freeCoefficientPushoutProduct_cofibrations a.asIndex b.asIndex i j
      (originalBoundary_cof i hi) (originalBoundary_cof j hj))

/-- The entire original realized-horn by realized-boundary family gives
actual level trivial cofibrations of the original native carrier. -/
theorem levelJ_pushoutProduct_levelI_trivialCofibrations :
    MorphismProperty.PushoutProductLe
      (NativeK.levelJ (I := Operator.{u, v})) (NativeK.levelI (I := Operator.{u, v}))
      (trivialCofibrations Carrier.{u, v}) := by
  apply CategoryTheory.FreePairTransport.generatorPair_pushoutProductLe
    (fun a : Operator.{u, v} => Free.functor (V := V.{u, v}) a)
    (fun a : Operator.{u, v} => Free.functor (V := V.{u, v}) a)
    PointedCGWH.realizedHornInclusions PointedCGWH.realizedBoundaryInclusions
    (trivialCofibrations Carrier.{u, v})
  intro a b M M' N N' i j hi hj
  have ha : PointedCGWH.symmetricOperatorObj.{u, v} a.asIndex = a := rfl
  have hb : PointedCGWH.symmetricOperatorObj.{u, v} b.asIndex = b := rfl
  have hA : CategoryTheory.Arrow.mk ((Free.functor (V := V.{u, v}) a).map i) =
      CategoryTheory.Arrow.mk
        (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} a.asIndex) i) :=
    congrArg (fun x : Operator.{u, v} => CategoryTheory.Arrow.mk (Free.coefficientMap x i)) ha.symm
  have hB : CategoryTheory.Arrow.mk ((Free.functor (V := V.{u, v}) b).map j) =
      CategoryTheory.Arrow.mk
        (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} b.asIndex) j) :=
    congrArg (fun x : Operator.{u, v} => CategoryTheory.Arrow.mk (Free.coefficientMap x j)) hb.symm
  exact CategoryTheory.FreePairTransport.pushoutProduct_mem_of_pairArrow_eq (trivialCofibrations Carrier.{u, v})
    ((Free.functor (V := V.{u, v}) a).map i) ((Free.functor (V := V.{u, v}) b).map j)
    _ _ hA hB
    (freeCoefficientPushoutProduct_trivial_left a.asIndex b.asIndex i j
      (originalHorn_trivial i hi) (originalBoundary_cof j hj))

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash
