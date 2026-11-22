/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SymmetricFreeSmashComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableGeneratorClasses
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKPushoutProduct

/-!
# Original symmetric stable generator products

Every original K generator, including each realized horn and every correlated
boundary/mapping-cylinder pair, satisfies the Omega-target tests after taking
its pushout-product with any original I generator. The proof uses the actual
balanced smash, its native free-function comparison, the actual tensor
pushout, and its two original legs. No stable model value or all-source
cofibrant-factor tensor preservation is an input to these generator tests.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC uD vD uS

open CategoryTheory MonoidalCategory Limits MorphismProperty HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalCategory MonoidalClosed CGWH.modelCategory CategoryTheory.MonObj

/-- Transport an entire map property along a typed equality of its source functors. -/
private theorem map_mem_of_functor_eq
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (P : MorphismProperty D) (F G : C ⥤ D) (h : F = G)
    {X Y : C} (f : X ⟶ Y) (hf : P (G.map f)) : P (F.map f) := by
  cases h
  exact hf

private theorem rightTensor_mem_of_left
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    (P : MorphismProperty C) [P.RespectsIso] (K : C) {X Y : C}
    (f : X ⟶ Y) (hf : P (K ◁ f)) : P (f ▷ K) := by
  let e : CategoryTheory.Arrow.mk (K ◁ f) ≅ CategoryTheory.Arrow.mk (f ▷ K) :=
    CategoryTheory.Arrow.isoMk (β_ K X) (β_ K Y)
      (CategoryTheory.BraidedCategory.braiding_naturality_right K f).symm
  exact (P.arrow_mk_iso_iff e).mp hf

private theorem pushoutProduct_mem_of_pushout_leg
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [HasPushouts C]
    (W : MorphismProperty C) [W.HasOfPrecompProperty W]
    {X Y K L : C} (i : X ⟶ Y) (j : K ⟶ L)
    (hPush : ∀ (Q : C) (inl : Y ⊗ K ⟶ Q) (inr : X ⊗ L ⟶ Q),
      IsPushout (i ▷ K) (X ◁ j) inl inr → W inr)
    (hRight : W (i ▷ L)) : W (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom := by
  have hLeg := hPush (pushout (i ▷ K) (X ◁ j))
    (pushout.inl (i ▷ K) (X ◁ j)) (pushout.inr (i ▷ K) (X ◁ j))
    (IsPushout.of_hasPushout (i ▷ K) (X ◁ j))
  have hFac : pushout.inr (i ▷ K) (X ◁ j) ≫
      (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom = i ▷ L := by
    change pushout.inr (i ▷ K) (X ◁ j) ≫
      pushout.desc (Y ◁ j) (i ▷ L) ((whisker_exchange i j).symm) = i ▷ L
    exact pushout.inr_desc _ _ _
  exact W.of_precomp (pushout.inr (i ▷ K) (X ◁ j))
    (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom hLeg
    (by rw [hFac]; exact hRight)

private theorem pushoutProduct_mem_of_rightArrow_eq
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [HasPushouts C]
    (W : MorphismProperty C) {X Y K L : C} (i : X ⟶ Y) (j : K ⟶ L)
    (right : CategoryTheory.Arrow C) (h : CategoryTheory.Arrow.mk j = right)
    (hRight : W (CategoryTheory.Arrow.mk i □ right).hom) :
    W (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom := by
  rw [h]
  exact hRight

private theorem pushoutProductLe_adjointFamily_right
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    [MonoidalCategory D] [HasPushouts D] {S : Type uS}
    (L : S → C ⥤ D) (P : MorphismProperty C) (Q R : MorphismProperty D)
    (hMaps : ∀ (a : S) ⦃M N : C⦄ (j : M ⟶ N), P j →
      ∀ ⦃X Y : D⦄ (i : X ⟶ Y), Q i →
        R (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk ((L a).map j)).hom) :
    PushoutProductLe Q (MorphismProperty.adjointFamilyGenerators L P) R := by
  intro X Y K T i j hi hj
  obtain ⟨q, hq⟩ := (MorphismProperty.adjointFamilyGenerators_iff L P j).mp hj
  exact pushoutProduct_mem_of_rightArrow_eq R i j _ hq
    (hMaps q.1 q.2.1.hom q.2.2 i hi)

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash

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
  monoidalCategory symmetricCategory monoidalClosed

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

attribute [local irreducible] monoidalCategory symmetricCategory monoidalClosed
  NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor
  NativeK.omegaTests
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Apply the complete native cobase-change theorem before substituting tensor endpoints. -/
private theorem omegaTests_pushout_leg
    {A D Z P : Carrier.{u, v}}
    [cofA : IsCofibrant A] [cofD : IsCofibrant D] [cofZ : IsCofibrant Z]
    (k : A ⟶ D) (f : A ⟶ Z) (inl : D ⟶ P) (inr : Z ⟶ P)
    (h : IsPushout k f inl inr) (hk : cofibrations Carrier.{u, v} k)
    (hw : NativeK.omegaTests Actual.symmetricFamily.{u, v} k) :
    NativeK.omegaTests Actual.symmetricFamily.{u, v} inr :=
  (NativeK.pushout_cofibration_omegaTests Actual.symmetricFamily.{u, v}
    k f inl inr h hk hw).2

/-- Right smash with the original free cofibrant coefficient preserves every
native level cofibration, through the whole original braiding square. -/
theorem freeRightTensor_cofibration (r : I) (M : V.{u, v}) [IsCofibrant M]
    {X Y : Carrier.{u, v}} (i : X ⟶ Y) (hi : cofibrations Carrier.{u, v} i) :
    cofibrations Carrier.{u, v} (i ▷ free.{u, v} r M) := by
  let _ := symmetricFreeSmash_isQuillen.{u, v} (B := B) r M
  have hLeft := Adjunction.IsQuillenAdjunction.preservesCofibrations
    (adj := NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} (free.{u, v} r M)) i hi
  have hTensor : cofibrations Carrier.{u, v} ((tensorLeft (free.{u, v} r M)).map i) := by
    rw [tensorLeft_eq_originalSmash]
    exact hLeft
  exact rightTensor_mem_of_left (cofibrations Carrier.{u, v}) (free.{u, v} r M) i hTensor

/-- The same right smash preserves the full original Omega tests on maps
between genuine cofibrant endpoints. -/
theorem freeRightTensor_omegaTests (r : I) (M : V.{u, v}) [IsCofibrant M]
    {X Y : Carrier.{u, v}} [IsCofibrant X] [IsCofibrant Y]
    (i : X ⟶ Y) (hi : NativeK.omegaTests Actual.symmetricFamily.{u, v} i) :
    NativeK.omegaTests Actual.symmetricFamily.{u, v} (i ▷ free.{u, v} r M) := by
  have hLeft := symmetricFreeSmashMap_omegaTests.{u, v} (B := B) r M i hi
  have hTensor : NativeK.omegaTests Actual.symmetricFamily.{u, v}
      ((tensorLeft (free.{u, v} r M)).map i) :=
    map_mem_of_functor_eq (NativeK.omegaTests Actual.symmetricFamily.{u, v})
      (tensorLeft (free.{u, v} r M))
      (NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor (free.{u, v} r M))
      (tensorLeft_eq_originalSmash (free.{u, v} r M)) i hLeft
  exact rightTensor_mem_of_left (NativeK.omegaTests Actual.symmetricFamily.{u, v})
    (free.{u, v} r M) i hTensor

/-- A genuine cofibrant spectrum remains cofibrant after right smash with
the original free cofibrant coefficient. -/
theorem freeRightTensor_obj_isCofibrant (r : I) (M : V.{u, v}) [IsCofibrant M]
    (X : Carrier.{u, v}) [IsCofibrant X] : IsCofibrant (X ⊗ free.{u, v} r M) := by
  let _ := symmetricFreeSmash_isQuillen.{u, v} (B := B) r M
  have hNative : IsCofibrant
      ((NativeOmegaPreparation.NativeSymmetricFunction.smashFunctor (free.{u, v} r M)).obj X) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := NativeOmegaPreparation.NativeSymmetricFunction.adjunction.{u, v} (free.{u, v} r M))
      inferInstance
  let _ : IsCofibrant (free.{u, v} r M ⊗ X) :=
    (tensorObj_eq_originalSmash (free.{u, v} r M) X).symm ▸ hNative
  exact isCofibrant_of_cofibration (β_ (free.{u, v} r M) X).hom

/-- The literal tensor pushout gives the stable test conclusion against
every coefficient map with cofibrant endpoints. The coefficient map need
not itself be a cofibration for this test conclusion. -/
theorem freeCoefficientPushoutProduct_omegaTests
    {X Y : Carrier.{u, v}} [IsCofibrant X] [IsCofibrant Y]
    (i : X ⟶ Y) (hiC : cofibrations Carrier.{u, v} i)
    (hiW : NativeK.omegaTests Actual.symmetricFamily.{u, v} i)
    (r : I) {M N : V.{u, v}} [IsCofibrant M] [IsCofibrant N] (j : M ⟶ N) :
    NativeK.omegaTests Actual.symmetricFamily.{u, v}
      ((Arrow.mk i □ Arrow.mk (Free.coefficientMap
        (PointedCGWH.symmetricOperatorObj.{u, v} r) j)).hom) := by
  let K := free.{u, v} r M
  let L := free.{u, v} r N
  let j' := Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} r) j
  have hXK : IsCofibrant (X ⊗ K) := freeRightTensor_obj_isCofibrant.{u, v} (B := B) r M X
  have hYK : IsCofibrant (Y ⊗ K) := freeRightTensor_obj_isCofibrant.{u, v} (B := B) r M Y
  have hXL : IsCofibrant (X ⊗ L) := freeRightTensor_obj_isCofibrant.{u, v} (B := B) r N X
  let _ : IsCofibrant (X ⊗ K) := hXK
  let _ : IsCofibrant (Y ⊗ K) := hYK
  let _ : IsCofibrant (X ⊗ L) := hXL
  have hiK := freeRightTensor_cofibration.{u, v} (B := B) r M i hiC
  have hiKW := freeRightTensor_omegaTests.{u, v} (B := B) r M i hiW
  apply pushoutProduct_mem_of_pushout_leg
    (NativeK.omegaTests Actual.symmetricFamily.{u, v}) i j'
  · intro Q inl inr hPush
    exact omegaTests_pushout_leg (B := B)
      (A := X ⊗ K) (D := Y ⊗ K) (Z := X ⊗ L) (P := Q)
      (cofA := hXK) (cofD := hYK) (cofZ := hXL)
      (i ▷ K) (X ◁ j') inl inr hPush hiK hiKW
  · exact freeRightTensor_omegaTests.{u, v} (B := B) r N i hiW

/-- Every actual K generator has the test conclusion against every free
coefficient map with cofibrant endpoints. All original generator labels remain. -/
theorem generatorPushoutProductFree_omegaTests
    {X Y : Carrier.{u, v}} (i : X ⟶ Y)
    (hi : NativeK.generators Actual.symmetricFamily.{u, v} i)
    (r : I) {M N : V.{u, v}} [IsCofibrant M] [IsCofibrant N] (j : M ⟶ N) :
    NativeK.omegaTests Actual.symmetricFamily.{u, v}
      ((Arrow.mk i □ Arrow.mk (Free.coefficientMap
        (PointedCGWH.symmetricOperatorObj.{u, v} r) j)).hom) := by
  have hEnds := NativeK.generatorEndpoints Actual.symmetricFamily.{u, v} i hi
  let _ : IsCofibrant X := hEnds.1
  let _ : IsCofibrant Y := hEnds.2
  exact freeCoefficientPushoutProduct_omegaTests i
    (NativeK.generators_le_cofibrations Actual.symmetricFamily.{u, v} i hi)
    (PointedCGWH.Spectra.NativeStable.symmetricKLeft_le_omegaTests i
      ((NativeK.generators Actual.symmetricFamily.{u, v}).le_llp_rlp i hi)) r j

/-- The full original K-by-I generator test, with every original free
degree and every realized-boundary coefficient map. -/
theorem generators_pushoutProduct_levelI_omegaTests :
    PushoutProductLe (NativeK.generators Actual.symmetricFamily.{u, v})
      (NativeK.levelI (I := Operator.{u, v}))
      (NativeK.omegaTests Actual.symmetricFamily.{u, v}) := by
  apply pushoutProductLe_adjointFamily_right
    (fun a : Operator.{u, v} => Free.functor (V := V.{u, v}) a)
    PointedCGWH.realizedBoundaryInclusions
    (NativeK.generators Actual.symmetricFamily.{u, v})
    (NativeK.omegaTests Actual.symmetricFamily.{u, v})
  intro a M N j hj X Y i hi
  have hEnds := NativeK.pointedBoundary_endpoints j hj
  let _ : IsCofibrant M := hEnds.1
  let _ : IsCofibrant N := hEnds.2
  apply pushoutProduct_mem_of_rightArrow_eq
    (NativeK.omegaTests Actual.symmetricFamily.{u, v}) i ((Free.functor a).map j)
    (CategoryTheory.Arrow.mk (Free.coefficientMap a j)) rfl
  have hIndex : PointedCGWH.symmetricOperatorObj.{u, v} a.asIndex = a := rfl
  have hArrow : CategoryTheory.Arrow.mk (Free.coefficientMap a j) =
      CategoryTheory.Arrow.mk
        (Free.coefficientMap (PointedCGWH.symmetricOperatorObj.{u, v} a.asIndex) j) :=
    congrArg (fun t : Operator.{u, v} => CategoryTheory.Arrow.mk (Free.coefficientMap t j))
      hIndex.symm
  apply pushoutProduct_mem_of_rightArrow_eq
    (NativeK.omegaTests Actual.symmetricFamily.{u, v}) i (Free.coefficientMap a j) _ hArrow
  exact generatorPushoutProductFree_omegaTests i hi a.asIndex j

/-- The level-horn summand of the original K union retains its actual
maps in the same stable generator product test. -/
theorem levelJ_pushoutProduct_levelI_omegaTests :
    PushoutProductLe (NativeK.levelJ (I := Operator.{u, v}))
      (NativeK.levelI (I := Operator.{u, v}))
      (NativeK.omegaTests Actual.symmetricFamily.{u, v}) := by
  intro X Y K L i j hi hj
  exact generators_pushoutProduct_levelI_omegaTests i j
    ((NativeK.generators_iff Actual.symmetricFamily.{u, v} i).mpr (Or.inl hi)) hj

/-- Each full correlated boundary/cylinder generator uses its literal
original paired stabilization label and boundary dimension. -/
theorem additional_pushoutProduct_levelI_omegaTests
    (l : I × I) (m : ℕ) {X Y : Carrier.{u, v}} (j : X ⟶ Y)
    (hj : NativeK.levelI j) :
    NativeK.omegaTests Actual.symmetricFamily.{u, v}
      ((Arrow.mk (NativeK.generatorMap Actual.symmetricFamily.{u, v} l m) □ Arrow.mk j).hom) :=
  generators_pushoutProduct_levelI_omegaTests _ j
    ((NativeK.generators_iff Actual.symmetricFamily.{u, v} _).mpr
      (Or.inr (NativeK.generatorMap_mem Actual.symmetricFamily.{u, v} l m))) hj

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash
