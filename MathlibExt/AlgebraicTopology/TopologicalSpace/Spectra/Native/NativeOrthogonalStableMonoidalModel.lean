/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceFreeSmash
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeOrthogonalFreeCoefficientProducts
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceSmashClosed
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceSmashUnit
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.ShiftOmega
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableGeneratorClasses
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKIsoTransport
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKMonoidal
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKSmashReduction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOrthogonalStableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductGeneratorCriterion
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalUnitModelChange
import MathlibExt.CategoryTheory.Monoidal.FreePairTransport

/-!
# The actual native orthogonal smash pushout products and unit

The entire original free-pair comparison transports the chosen coefficient
pushout and both of its legs through the genuine output free adjoint.
The actual closed free function spectrum is the original shifted cotensor,
so it preserves every original paired Omega condition. Literal products
of the complete original K and I families supply stable trivial products.
The unit uses the genuine sphere/free-zero comparison and the entire
original same-cardinal initial-unit factor.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped MonoidalCategory

open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra MonoidalOpposite
open scoped MonoidalClosed CategoryTheory.MonObj CGWH.modelCategory CGWH.limits

open CategoryTheory.MorphismProperty

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalUnitTransport

universe uC vC

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]

/-- The entire left unit replacement family is typed at the selected model
before the concrete unit witness or its original right factor is selected. -/
def LeftReplacementFamily (M : ModelCategory C)
    (w : letI : ModelCategory C := M; MonoidalUnitAxiomWitness C) : Prop :=
  ∀ (X : C), (letI : ModelCategory C := M; IsCofibrant X) →
    (letI : ModelCategory C := M;
      weakEquivalences C ((leftUnitReplacementMap w.q).app X))

/-- The entire right unit replacement family retains every input and the
complete right unitor map at the same selected model and witness. -/
def RightReplacementFamily (M : ModelCategory C)
    (w : letI : ModelCategory C := M; MonoidalUnitAxiomWitness C) : Prop :=
  ∀ (X : C), (letI : ModelCategory C := M; IsCofibrant X) →
    (letI : ModelCategory C := M;
      weakEquivalences C ((rightUnitReplacementMap w.q).app X))

variable (M₀ M₁ : ModelCategory C)
    (hCof : (letI : ModelCategory C := M₀; cofibrations C) =
      (letI : ModelCategory C := M₁; cofibrations C))
    (hPP : letI : ModelCategory C := M₁; MonoidalPushoutProductAxiom C)
    (hUnit : letI : ModelCategory C := M₀; IsCofibrant (𝟙_ C))
    (d : letI : ModelCategory C := M₀;
      MapFactorizationData (cofibrations C) (trivialFibrations C) (initial.to (𝟙_ C)))

/-- Both models and the full original unit factor supply the whole left
replacement family before any native input or witness getter is read. -/
theorem unitWitness_leftFamily :
    LeftReplacementFamily M₁
      (HomotopicalAlgebra.ModelCategory.unitAxiomWitnessOfCofibrationsEqUnitFactor
        M₀ M₁ hCof hPP hUnit d) :=
  HomotopicalAlgebra.ModelCategory.TypedUnitModelChange.leftUnitReplacement
    M₀ M₁ hCof hPP hUnit d

/-- The same original right factor supplies the entire right replacement
family with every genuinely cofibrant input retained. -/
theorem unitWitness_rightFamily :
    RightReplacementFamily M₁
      (HomotopicalAlgebra.ModelCategory.unitAxiomWitnessOfCofibrationsEqUnitFactor
        M₀ M₁ hCof hPP hUnit d) :=
  HomotopicalAlgebra.ModelCategory.TypedUnitModelChange.rightUnitReplacement
    M₀ M₁ hCof hPP hUnit d

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalUnitTransport

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSmash

universe u v
open PointedCGWH.Spectra.Orthogonal

private abbrev V := PointedCGWH.{u, v}
private abbrev Operator := OrthogonalOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}

attribute [local instance]
  PointedCGWH.copowerUnderlyingEnrichedOrdinary
  CanonicalSourceSmash.monoidalCategory CanonicalSourceSmash.symmetricCategory
  CanonicalSourceSmashClosed.monoidalClosed PointedCGWH.EnrichedMapping.hasSmallLimits

/-- The original ordinary category on orthogonal indices. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original direct-sum monoidal structure on orthogonal indices. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original enrichment recovers the same ordinary orthogonal-index arrows. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block-swap symmetry on orthogonal indices. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}

/-- Both entire original free functors and their r+s output use the public canonical tensor. -/
def FreePairBifunctorFormulaType : Type _ :=
  ∀ (r s : OrthogonalIndex),
    (CanonicalSourceFreeSmash.freeFunctor.{u, v} r).prod
        (CanonicalSourceFreeSmash.freeFunctor.{u, v} s) ⋙ tensor (EnrichedFunctorCat PointedCGWH.{u, v}
          OrthogonalOperatorIndex.{u, v}) ≅
      tensor PointedCGWH.{u, v} ⋙ CanonicalSourceFreeSmash.freeFunctor.{u, v} (r + s)

/-- The same complete original source comparison is typed at the public tensor before coefficients. -/
def freePairBifunctorIso : FreePairBifunctorFormulaType.{u, v} :=
  OrthogonalSourcePair.CanonicalCoefficientProducts.bifunctorFamily
    CanonicalSourceSmash.sourceContext.{u, v}
    OrthogonalOperatorIndex.ofIndex.{u, v}
    CanonicalSourceRightModuleFreeEvaluation.evaluationComparison.{u, v}
    SphereSmashFree.tensorIndex.{u, v} SphereSmashFree.diagramPair.{u, v}
    CanonicalSourceFreeSmash.pairData.{u, v}.diagramPairCoefficient

/-- All original component indices and coefficients use that same public tensor. -/
def FreePairComponentFormulaType : Type _ :=
  ∀ (r s : OrthogonalIndex) (X Y : PointedCGWH.{u, v}),
    CanonicalSourceFreeSmash.freeObject r X ⊗ CanonicalSourceFreeSmash.freeObject s Y ≅
      CanonicalSourceFreeSmash.freeObject (r + s) (X ⊗ Y)

/-- The same entire source pair retains its exact native coefficient-object endpoints. -/
def freePairComponentIso : FreePairComponentFormulaType.{u, v} := by
  intro r s X Y
  let er : (CanonicalSourceFreeSmash.freeFunctor.{u, v} r).obj X ≅
      CanonicalSourceFreeSmash.freeObject r X := Iso.refl _
  let es : (CanonicalSourceFreeSmash.freeFunctor.{u, v} s).obj Y ≅
      CanonicalSourceFreeSmash.freeObject s Y := Iso.refl _
  let eo : (CanonicalSourceFreeSmash.freeFunctor.{u, v} (r + s)).obj (X ⊗ Y) ≅
      CanonicalSourceFreeSmash.freeObject (r + s) (X ⊗ Y) := Iso.refl _
  exact CategoryTheory.FreePairTransport.componentOnObjects
    (CanonicalSourceFreeSmash.freeFunctor.{u, v} r)
    (CanonicalSourceFreeSmash.freeFunctor.{u, v} s)
    (CanonicalSourceFreeSmash.freeFunctor.{u, v} (r + s))
    (freePairBifunctorIso r s) X Y er es eo

section CoefficientPushoutData
variable [H : HasPushouts (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})]

/-- The original native coefficient-product family includes all degrees and both full maps. -/
def FreeCoefficientProductsFormulaType : Type _ :=
  ∀ (r s : OrthogonalIndex) {M M' N N' : PointedCGWH.{u, v}} (i : M ⟶ M') (j : N ⟶ N'),
    (CanonicalSourceFreeSmash.freeFunctor.{u, v} (r + s)).mapArrow.obj
        (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j) ≅
      CategoryTheory.Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} r) i) □
        CategoryTheory.Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} s) j)

/-- Both original PP legs retain their actual native output functor and full source pair. -/
def freeCoefficientPushoutProductIso : FreeCoefficientProductsFormulaType.{u, v} :=
  OrthogonalSourcePair.CoefficientTargetStage.ofPairFamily
    OrthogonalOperatorIndex.ofIndex.{u, v}
    (HAdd.hAdd : OrthogonalIndex → OrthogonalIndex → OrthogonalIndex) freePairBifunctorIso.{u, v}

end CoefficientPushoutData

private theorem originalBoundary_cof {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    (hi : PointedCGWH.realizedBoundaryInclusions i) : cofibrations PointedCGWH.{u, v} i := by
  have h := PointedCGWH.realizedBoundaryInclusions.{u, v}.le_llp_rlp i hi
  have hI : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
      trivialFibrations PointedCGWH.{u, v} := PointedCGWH.cofibrantGenerationData.{u, v}.I_rlp
  rwa [hI, trivialFibrations_llp] at h

private theorem originalHorn_trivial {M N : PointedCGWH.{u, v}} (i : M ⟶ N)
    (hi : PointedCGWH.realizedHornInclusions i) : trivialCofibrations PointedCGWH.{u, v} i := by
  have h := PointedCGWH.realizedHornInclusions.{u, v}.le_llp_rlp i hi
  have hJ : PointedCGWH.realizedHornInclusions.{u, v}.rlp =
      fibrations PointedCGWH.{u, v} := PointedCGWH.cofibrantGenerationData.{u, v}.J_rlp
  rwa [hJ, fibrations_llp] at h

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
open scoped CGWH.modelCategory CGWH.limits
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

private def originalLevelI : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
  NativeK.levelI (I := OrthogonalOperatorIndex.{u, v})

private def originalLevelJ : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
  NativeK.levelJ (I := OrthogonalOperatorIndex.{u, v})

omit B in
private theorem originalCoefficientArrow (a : OrthogonalOperatorIndex.{u, v})
    {M N : PointedCGWH.{u, v}} (i : M ⟶ N) :
    CategoryTheory.Arrow.mk ((Free.functor (V := PointedCGWH.{u, v}) a).map i) =
      CategoryTheory.Arrow.mk
        (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} a.asIndex) i) := by
  have ha : OrthogonalOperatorIndex.ofIndex.{u, v} a.asIndex = a := rfl
  exact congrArg
    (fun x : OrthogonalOperatorIndex.{u, v} => CategoryTheory.Arrow.mk (Free.coefficientMap x i)) ha.symm

section CoefficientMemberships
variable [H : HasPushouts (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})]

/-- All original coefficient cofibrations retain their native source-pair product. -/
def FreeCoefficientCofibrationsFormulaType : Prop :=
  ∀ (r s : OrthogonalIndex) {M M' N N' : PointedCGWH.{u, v}}
    (i : M ⟶ M') (j : N ⟶ N'),
    cofibrations PointedCGWH.{u, v} i → cofibrations PointedCGWH.{u, v} j →
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
      (CategoryTheory.Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} r) i) □
        CategoryTheory.Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} s) j)).hom

/-- The full supplier retains the original native context before either coefficient map. -/
private theorem coefficientCofibrationsFamily : FreeCoefficientCofibrationsFormulaType.{u, v} := by
  let : HasPushouts (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) := H
  exact OrthogonalSourcePair.CoefficientTargetStage.literalMembershipFamily (V := PointedCGWH.{u, v})
    OrthogonalOperatorIndex.ofIndex.{u, v}
    (HAdd.hAdd : OrthogonalIndex → OrthogonalIndex → OrthogonalIndex) (freeCoefficientPushoutProductIso.{u, v} (H := H))
    (cofibrations PointedCGWH.{u, v}) (cofibrations PointedCGWH.{u, v}) (cofibrations PointedCGWH.{u, v})
    (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
    IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
    (fun a {_ _} f hf => freeAt_map_mem_cofibrations a f hf)


/-- Genuine output Free preservation supplies every original coefficient cofibration product. -/
theorem freeCoefficientPushoutProduct_cofibrations
    (r s : OrthogonalIndex) {M M' N N' : PointedCGWH.{u, v}}
    (i : M ⟶ M') (j : N ⟶ N')
    (hi : cofibrations PointedCGWH.{u, v} i) (hj : cofibrations PointedCGWH.{u, v} j) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
      (CategoryTheory.Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} r) i) □
        CategoryTheory.Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} s) j)).hom :=
  coefficientCofibrationsFamily (B := B) (H := H) r s i j hi hj

/-- All original trivial left coefficient maps retain the full native level product. -/
def FreeCoefficientTrivialLeftFormulaType : Prop :=
  ∀ (r s : OrthogonalIndex) {M M' N N' : PointedCGWH.{u, v}}
    (i : M ⟶ M') (j : N ⟶ N'),
    trivialCofibrations PointedCGWH.{u, v} i → cofibrations PointedCGWH.{u, v} j →
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
      (CategoryTheory.Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} r) i) □
        CategoryTheory.Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} s) j)).hom

/-- The complete trivial-left supplier uses the actual native context and both full maps. -/
private theorem coefficientTrivialLeftFamily : FreeCoefficientTrivialLeftFormulaType.{u, v} := by
  let : HasPushouts (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) := H
  exact OrthogonalSourcePair.CoefficientTargetStage.literalMembershipFamily (V := PointedCGWH.{u, v})
    OrthogonalOperatorIndex.ofIndex.{u, v}
    (HAdd.hAdd : OrthogonalIndex → OrthogonalIndex → OrthogonalIndex) (freeCoefficientPushoutProductIso.{u, v} (H := H))
    (trivialCofibrations PointedCGWH.{u, v}) (cofibrations PointedCGWH.{u, v}) (trivialCofibrations PointedCGWH.{u, v})
    (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
    IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
    (fun a {_ _} f hf => freeAt_map_mem_trivialCofibrations a f hf)

/-- The scalar trivial-product law and stock output Free prove the entire native family. -/
theorem freeCoefficientPushoutProduct_trivial_left
    (r s : OrthogonalIndex) {M M' N N' : PointedCGWH.{u, v}}
    (i : M ⟶ M') (j : N ⟶ N')
    (hi : trivialCofibrations PointedCGWH.{u, v} i) (hj : cofibrations PointedCGWH.{u, v} j) :
    trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
      (CategoryTheory.Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} r) i) □
        CategoryTheory.Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} s) j)).hom :=
  coefficientTrivialLeftFamily (B := B) (H := H) r s i j hi hj

end CoefficientMemberships

/-- Both complete original freely pointed boundary classes occur in the native formula. -/
def LevelIProductFormulaType : Prop :=
  MorphismProperty.PushoutProductLe originalLevelI.{u, v}
    originalLevelI.{u, v} (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))

/-- Every original operator degree and boundary retains its native I-by-I product. -/
theorem levelI_pushoutProduct_levelI_cofibrations : LevelIProductFormulaType.{u, v} := by
  have h := OrthogonalSourcePair.CoefficientTargetStage.generatorProducts (V := PointedCGWH.{u, v})
    OrthogonalOperatorIndex.ofIndex.{u, v}
    (HAdd.hAdd : OrthogonalIndex → OrthogonalIndex → OrthogonalIndex) freeCoefficientPushoutProductIso.{u, v}
    (fun a : OrthogonalOperatorIndex.{u, v} => a.asIndex) (fun _ => rfl)
    PointedCGWH.realizedBoundaryInclusions PointedCGWH.realizedBoundaryInclusions
    (cofibrations PointedCGWH.{u, v}) (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v}
      OrthogonalOperatorIndex.{u, v}))
    (fun {_ _ _ _} i j hi hj =>
      IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct i j
        (originalBoundary_cof i hi) (originalBoundary_cof j hj))
    (fun a {_ _} f hf => freeAt_map_mem_cofibrations a f hf)

  exact h

/-- The entire original horn and boundary classes occur in the native trivial-product formula. -/
def LevelJProductFormulaType : Prop :=
  MorphismProperty.PushoutProductLe originalLevelJ.{u, v}
    originalLevelI.{u, v} (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))

/-- Every original horn, boundary and operator degree retains the native J-by-I product. -/
theorem levelJ_pushoutProduct_levelI_trivialCofibrations : LevelJProductFormulaType.{u, v} := by
  have h := OrthogonalSourcePair.CoefficientTargetStage.generatorProducts (V := PointedCGWH.{u, v})
    OrthogonalOperatorIndex.ofIndex.{u, v}
    (HAdd.hAdd : OrthogonalIndex → OrthogonalIndex → OrthogonalIndex) freeCoefficientPushoutProductIso.{u, v}
    (fun a : OrthogonalOperatorIndex.{u, v} => a.asIndex) (fun _ => rfl)
    PointedCGWH.realizedHornInclusions PointedCGWH.realizedBoundaryInclusions
    (trivialCofibrations PointedCGWH.{u, v}) (trivialCofibrations (EnrichedFunctorCat PointedCGWH.{u, v}
      OrthogonalOperatorIndex.{u, v}))
    (fun {_ _ _ _} i j hi hj =>
      IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left i j
        (originalHorn_trivial i hi) (originalBoundary_cof j hj))
    (fun a {_ _} f hf => freeAt_map_mem_trivialCofibrations a f hf)

  exact h


/-- The original native generation data extend both complete level-generator products. -/
theorem levelPushoutProductAxiom : MonoidalPushoutProductAxiom (EnrichedFunctorCat PointedCGWH.{u, v}
  OrthogonalOperatorIndex.{u, v}) := by
  apply (HomotopicalAlgebra.EnrichedProjective.Native.Data.generationData
    (A := OrthogonalOperatorIndex.{u, v}) (B := B)).pushoutProductAxiom_of_generatorProducts
  · exact levelI_pushoutProduct_levelI_cofibrations
  · exact levelJ_pushoutProduct_levelI_trivialCofibrations

/-- Both full original I-left classes retain the actual native level cofibration product. -/
theorem originalILeft_pushoutProduct_originalILeft :
    MorphismProperty.PushoutProductLe originalLevelI.{u, v}.rlp.llp
      originalLevelI.{u, v}.rlp.llp originalLevelI.{u, v}.rlp.llp := by
  simpa only [originalLevelI, HomotopicalAlgebra.EnrichedProjective.Native.cofibrations_eq] using
    (levelPushoutProductAxiom (B := B)).cofibration_pushoutProduct


/-- The chosen actual free function spectrum preserves every original paired Omega test. -/
theorem freeFunction_isOmega (r : OrthogonalIndex) (M : PointedCGWH.{u, v}) [IsCofibrant M]
    (E : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})) (hE : Actual.OrthogonalIsOmega E) :
    Actual.OrthogonalIsOmega ((ihom (CanonicalSourceFreeSmash.freeObject r M)).obj E) := by
  change Actual.OrthogonalIsOmega
    ((MMSSStabilization.FunctionIteration.mappingFunctor
      (MMSSStabilization.FunctionIteration.nativeFree r M)).obj E)
  apply NativeOmegaRecovery.NativeOmegaIsoTransport.isOmega_obj_of_natIso Actual.orthogonalFamily
    (MMSSStabilization.FunctionIteration.nativeFreeFunctionNatIso r M) E
  exact NativeK.cotensor_isOmega Actual.orthogonalFamily M _
    (FunctionSpectrum.ShiftOmega.shift_isOmega r E hE)

/-- Original right smash by a genuine free cofibrant coefficient preserves full Omega tests
between cofibrant native endpoints. -/
theorem freeRightTensor_omegaTests (r : OrthogonalIndex) (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})} [IsCofibrant X] [IsCofibrant Y]
    (i : X ⟶ Y) (hi : NativeK.omegaTests Actual.orthogonalFamily.{u, v} i) :
    NativeK.omegaTests Actual.orthogonalFamily.{u, v}
      (i ▷ CanonicalSourceFreeSmash.freeObject r M) := by
  exact NativeK.SmashReduction.rightTensorTests Actual.orthogonalFamily
    (levelPushoutProductAxiom (B := B)) (CanonicalSourceFreeSmash.freeObject r M)
    (freeAt_obj_isCofibrant (OrthogonalOperatorIndex.ofIndex.{u, v} r) M)
    (freeFunction_isOmega r M) inferInstance inferInstance i hi

/-- The whole original free coefficient family supplies every literal tensor PP Omega test
before native maps are applied. -/
theorem freeCoefficientPushoutProduct_omegaTests :
    NativeK.SmashReduction.FreeCoefficientTestsClass Actual.orthogonalFamily.{u, v}
      (fun r : OrthogonalIndex => CanonicalSourceFreeSmash.freeFunctor.{u, v} r) := by
  apply NativeK.SmashReduction.originalFreeCoefficientTests Actual.orthogonalFamily
    (fun r : OrthogonalIndex => OrthogonalOperatorIndex.ofIndex.{u, v} r)
    (levelPushoutProductAxiom (B := B))
  intro r M hM E hE
  let _ : IsCofibrant M := hM
  exact freeFunction_isOmega r M E hE

/-- The whole original native K-by-free coefficient family is proved before selecting any generator or endpoint. -/
private theorem originalGeneratorFreeCoefficientFamily :
    NativeK.SmashReduction.OriginalGeneratorCoefficientTests Actual.orthogonalFamily.{u, v}
      OrthogonalOperatorIndex.ofIndex.{u, v} :=
  NativeK.SmashReduction.originalGeneratorCoefficientTests Actual.orthogonalFamily
    OrthogonalOperatorIndex.ofIndex.{u, v}
    (levelPushoutProductAxiom (B := B)) (by
      intro r M hM E hE
      let _ : IsCofibrant M := hM
      exact freeFunction_isOmega r M E hE)
    PointedCGWH.Spectra.NativeStable.orthogonalHom_isCofibrant

section GeneratorCoefficientCallers
variable [H : HasPushouts (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})]

/-- The complete original coefficient-product test at the caller's existing pushout. -/
def OriginalGeneratorCoefficientResultType (r : OrthogonalIndex)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}} (i : X ⟶ Y)
    {M N : PointedCGWH.{u, v}} (j : M ⟶ N) : Prop :=
  NativeK.omegaTests Actual.orthogonalFamily.{u, v}
    (Arrow.mk i □ Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} r) j)).hom

/-- The complete original native generator formula before any coefficient map is chosen. -/
def OriginalGeneratorCoefficientFormulaType : Prop :=
  ∀ {X Y : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}} (i : X ⟶ Y),
    NativeK.generators Actual.orthogonalFamily.{u, v} i →
    ∀ (r : OrthogonalIndex) {M N : PointedCGWH.{u, v}} [IsCofibrant M] [IsCofibrant N] (j : M ⟶ N),
      NativeK.omegaTests Actual.orthogonalFamily.{u, v}
        (Arrow.mk i □ Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} r) j)).hom

/-- The actual original family retains the caller's pushout proof before choosing generator values. -/
private theorem originalGeneratorFamilyAtCallerPushouts : OriginalGeneratorCoefficientFormulaType.{u, v} :=
  @NativeK.SmashReduction.callerGeneratorCoefficientTests.{u, v}
    OrthogonalOperatorIndex.{u, v} _ OrthogonalIndex orthogonalOperatorEnrichedCategory.{u, v}
    Actual.orthogonalFamily.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
    B CanonicalSourceSmash.monoidalCategory.{u, v} H
    (originalGeneratorFreeCoefficientFamily.{u, v} (B := B))

/-- Every original K generator retains the literal coefficient product and all original named arguments. -/
theorem generatorPushoutProductFree_omegaTests
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}} (i : X ⟶ Y)
    (hi : NativeK.generators Actual.orthogonalFamily.{u, v} i)
    (r : OrthogonalIndex) {M N : PointedCGWH.{u, v}} [IsCofibrant M] [IsCofibrant N] (j : M ⟶ N) :
    NativeK.omegaTests Actual.orthogonalFamily.{u, v}
      (Arrow.mk i □ Arrow.mk (Free.coefficientMap (OrthogonalOperatorIndex.ofIndex.{u, v} r) j)).hom :=
  originalGeneratorFamilyAtCallerPushouts.{u, v} (B := B) (H := H) i hi r j

end GeneratorCoefficientCallers

/-- The full original K-by-I generator product satisfies every original Omega-target test. -/
theorem generators_pushoutProduct_levelI_omegaTests :
    MorphismProperty.PushoutProductLe (NativeK.generators Actual.orthogonalFamily.{u, v})
      originalLevelI.{u, v} (NativeK.omegaTests Actual.orthogonalFamily.{u, v}) := by
  apply NativeK.SmashReduction.originalGeneratorProducts Actual.orthogonalFamily
    (levelPushoutProductAxiom (B := B))
    ?_ PointedCGWH.Spectra.NativeStable.orthogonalHom_isCofibrant
  intro a M hM E hE
  let _ : IsCofibrant M := hM
  exact freeFunction_isOmega a.asIndex M E hE

/-- Every literal original K-by-I product lies in the exact native stable left candidate class. -/
theorem originalGenerators_pushoutProduct_originalILeft_omegaTests :
    MorphismProperty.PushoutProductLe (NativeK.generators Actual.orthogonalFamily.{u, v})
      originalLevelI.{u, v}
      (originalLevelI.{u, v}.rlp.llp ⊓ NativeK.omegaTests Actual.orthogonalFamily.{u, v}) :=
  HomotopicalAlgebra.OriginalStableSmashAssembly.generatorProducts_intersection
    originalLevelI.{u, v} (NativeK.generators Actual.orthogonalFamily.{u, v})
    (NativeK.omegaTests Actual.orthogonalFamily.{u, v})
    (NativeK.SmashReduction.originalGenerators_le_ILeft Actual.orthogonalFamily)
    (originalILeft_pushoutProduct_originalILeft (B := B))
    (generators_pushoutProduct_levelI_omegaTests (B := B))

/-- The genuine original free-zero comparison independently proves actual sphere unit cofibrancy. -/
theorem levelTensorUnit_isCofibrant : IsCofibrant (𝟙_ (EnrichedFunctorCat PointedCGWH.{u, v}
  OrthogonalOperatorIndex.{u, v})) :=
  CanonicalSourceSmashUnit.isCofibrant_tensorUnit

local instance originalLevelSphereUnitCofibrant : IsCofibrant (𝟙_ (EnrichedFunctorCat PointedCGWH.{u, v}
  OrthogonalOperatorIndex.{u, v})) :=
  levelTensorUnit_isCofibrant (B := B)

/-- The whole original native I-factorization at its actual initial sphere-unit map. -/
def originalLevelUnitFactor :
    MapFactorizationData (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
      (trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
      (initial.to (𝟙_ (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))) :=
  (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
    (A := OrthogonalOperatorIndex.{u, v}) (B := B)).factorizationData (initial.to (𝟙_ (EnrichedFunctorCat
      PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})))

/-- The actual level unit witness retains this original same-cardinal factor. -/
def levelUnitAxiomWitness : MonoidalUnitAxiomWitness (EnrichedFunctorCat PointedCGWH.{u, v}
  OrthogonalOperatorIndex.{u, v}) :=
  (levelPushoutProductAxiom (B := B)).unitAxiomWitnessOfUnitFactor (originalLevelUnitFactor (B := B))

/-- The full actual native level tensor satisfies the closed symmetric monoidal model laws. -/
theorem levelSmashMonoidalModel : IsClosedSymmetricMonoidalModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
  OrthogonalOperatorIndex.{u, v}) :=
  (levelPushoutProductAxiom (B := B)).monoidalModelOfUnitFactor (originalLevelUnitFactor (B := B))


/-- The stable model is the actual original-family construction on this native carrier. -/
private abbrev constructedStableModel : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
  OrthogonalOperatorIndex.{u, v}) :=
  HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.orthogonalModelCategory
    (B := B)

private theorem level_cofibrations_eq_stable :
    (letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := OrthogonalOperatorIndex.{u, v}) (B := B)
     cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})) =
      (letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
        constructedStableModel (B := B)
       cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})) := by
  exact
    (HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.orthogonal_cofibrations_eq_level
      (B := B)).symm

/-- All three stable pushout-product laws follow from the literal original I/K products,
the actual original generation data and the whole Arrow braid. -/
theorem stablePushoutProductAxiom :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      constructedStableModel (B := B)
    MonoidalPushoutProductAxiom (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) := by
  let M : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
    constructedStableModel (B := B)
  let G : HomotopicalAlgebra.OriginalStableSmashAssembly.GenerationDataType M
      realizedGeneratorCardinal.{v} :=
    HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.orthogonalGenerationData (B := B)
  apply HomotopicalAlgebra.OriginalStableSmashAssembly.pushoutProductAxiom M
    realizedGeneratorCardinal.{v} G (NativeK.levelI (I := OrthogonalOperatorIndex.{u, v}))
    (NativeK.generators Actual.orthogonalFamily.{u, v}) (NativeK.omegaTests Actual.orthogonalFamily.{u, v})
  · rfl
  · rfl
  · exact
      (HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.orthogonal_five_classes
        (B := B)).2.1
  · exact
      ((HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.orthogonal_five_classes
        (B := B)).2.2.2.1).trans
        (HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.orthogonal_left_class_eq (B := B))
  · intro X Y K L i j hi hj
    exact originalILeft_pushoutProduct_originalILeft i j
      ((NativeK.levelI (I := OrthogonalOperatorIndex.{u, v})).le_llp_rlp i hi)
      ((NativeK.levelI (I := OrthogonalOperatorIndex.{u, v})).le_llp_rlp j hj)
  · exact originalGenerators_pushoutProduct_originalILeft_omegaTests (B := B)

/-- The original initial-unit Arrow is fixed in the original native level model before transport. -/
private def originalInitialUnitArrow :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := OrthogonalOperatorIndex.{u, v}) (B := B)
    (⊥_ (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})) ⟶ (𝟙_ (EnrichedFunctorCat
      PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})) :=
  letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
    HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := OrthogonalOperatorIndex.{u, v}) (B := B)
  initial.to (𝟙_ (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))

/-- The original same-cardinal factor source is fixed before the stable witness getter. -/
private def originalUnitFactorSource : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
  (originalLevelUnitFactor (B := B)).Z

/-- The whole original factor source is its original functor value at that original Arrow. -/
private theorem originalUnitFactorSource_eq_functor :
    originalUnitFactorSource (B := B) =
      (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
        (A := OrthogonalOperatorIndex.{u, v}) (B := B)).Z.obj
          (CategoryTheory.Arrow.mk (originalInitialUnitArrow)) := rfl

/-- The original right factor keeps the same actual domain and sphere unit. -/
private def originalUnitFactorRight : originalUnitFactorSource (B := B) ⟶
    (𝟙_ (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})) :=
  (originalLevelUnitFactor (B := B)).p

/-- The original right factor is the actual original natural map at the same Arrow. -/
private theorem originalUnitFactorRight_eq_functor :
    originalUnitFactorRight (B := B) =
      (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
        (A := OrthogonalOperatorIndex.{u, v}) (B := B)).p.app
          (CategoryTheory.Arrow.mk (originalInitialUnitArrow)) := rfl

/-- Actual sphere-unit cofibrancy transports through the unchanged original I-left class. -/
theorem stableTensorUnit_isCofibrant :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      constructedStableModel (B := B)
    IsCofibrant (𝟙_ (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})) :=
  HomotopicalAlgebra.ModelCategory.TypedUnitModelChange.selectedUnit_isCofibrant
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := OrthogonalOperatorIndex.{u, v}) (B := B))
    (constructedStableModel (B := B)) (level_cofibrations_eq_stable (B := B))
    (levelTensorUnit_isCofibrant (B := B))

/-- Only memberships change in the original initial-unit factor record at its original Arrow. -/
def originalStableUnitFactor :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      constructedStableModel (B := B)
    MapFactorizationData (cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
      (trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
      (originalInitialUnitArrow) :=
  HomotopicalAlgebra.ModelCategory.cofibrantMapFactorizationOfCofibrationsEq
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := OrthogonalOperatorIndex.{u, v}) (B := B))
    (constructedStableModel (B := B)) (level_cofibrations_eq_stable (B := B))
    (originalInitialUnitArrow) (originalLevelUnitFactor (B := B))

/-- The original middle object and both complete factor arrows retain their exact values. -/
theorem originalStableUnitFactor_original_fields :
    (originalStableUnitFactor (B := B)).Z = (originalLevelUnitFactor (B := B)).Z ∧
      (originalStableUnitFactor (B := B)).i = (originalLevelUnitFactor (B := B)).i ∧
      (originalStableUnitFactor (B := B)).p = (originalLevelUnitFactor (B := B)).p :=
  ⟨rfl, rfl, rfl⟩

/-- The witness type selects the actual stable model before reading any original unit fields. -/
def stableUnitAxiomWitness :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      constructedStableModel (B := B)
    MonoidalUnitAxiomWitness (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
  HomotopicalAlgebra.ModelCategory.unitAxiomWitnessOfCofibrationsEqUnitFactor
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := OrthogonalOperatorIndex.{u, v}) (B := B))
    (constructedStableModel (B := B)) (level_cofibrations_eq_stable (B := B))
    (stablePushoutProductAxiom (B := B)) (levelTensorUnit_isCofibrant (B := B))
    (originalLevelUnitFactor (B := B))

/-- The actual stable witness source is the original same-cardinal middle functor value. -/
theorem stableUnitAxiomWitness_Q :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      constructedStableModel (B := B)
    (stableUnitAxiomWitness (B := B)).Q =
      (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
        (A := OrthogonalOperatorIndex.{u, v}) (B := B)).Z.obj
          (CategoryTheory.Arrow.mk (originalInitialUnitArrow)) :=
  (HomotopicalAlgebra.ModelCategory.unitAxiomWitnessOfCofibrationsEqUnitFactor_Q
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := OrthogonalOperatorIndex.{u, v}) (B := B))
    (constructedStableModel (B := B)) (level_cofibrations_eq_stable (B := B))
    (stablePushoutProductAxiom (B := B)) (levelTensorUnit_isCofibrant (B := B))
    (originalLevelUnitFactor (B := B))).trans (originalUnitFactorSource_eq_functor (B := B))

/-- The stable witness map is the original same-bottom right factor at that same original Arrow. -/
theorem stableUnitAxiomWitness_q :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      constructedStableModel (B := B)
    (stableUnitAxiomWitness (B := B)).q =
      (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
        (A := OrthogonalOperatorIndex.{u, v}) (B := B)).p.app
          (CategoryTheory.Arrow.mk (originalInitialUnitArrow)) :=
  (HomotopicalAlgebra.ModelCategory.unitAxiomWitnessOfCofibrationsEqUnitFactor_q
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := OrthogonalOperatorIndex.{u, v}) (B := B))
    (constructedStableModel (B := B)) (level_cofibrations_eq_stable (B := B))
    (stablePushoutProductAxiom (B := B)) (levelTensorUnit_isCofibrant (B := B))
    (originalLevelUnitFactor (B := B))).trans (originalUnitFactorRight_eq_functor (B := B))

/-- Both original factor legs retain their entire original factor equation. -/
theorem stableUnitAxiomWitness_fac :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      constructedStableModel (B := B)
    (originalLevelUnitFactor (B := B)).i ≫ (stableUnitAxiomWitness (B := B)).q =
      originalInitialUnitArrow :=
  (originalLevelUnitFactor (B := B)).fac

/-- The complete left replacement family is fixed before reading the actual native unit map. -/
private theorem stableUnitReplacement_leftFamily :
    OrthogonalUnitTransport.LeftReplacementFamily (C := (EnrichedFunctorCat PointedCGWH.{u, v}
      OrthogonalOperatorIndex.{u, v}))
      (constructedStableModel.{u, v} (B := B))
      (stableUnitAxiomWitness.{u, v} (B := B)) :=
  OrthogonalUnitTransport.unitWitness_leftFamily (C := (EnrichedFunctorCat PointedCGWH.{u, v}
    OrthogonalOperatorIndex.{u, v}))
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := OrthogonalOperatorIndex.{u, v}) (B := B))
    (constructedStableModel.{u, v} (B := B)) (level_cofibrations_eq_stable (B := B))
    (stablePushoutProductAxiom (B := B)) (levelTensorUnit_isCofibrant (B := B))
    (originalLevelUnitFactor (B := B))

/-- The complete right family keeps the same original factor, stable model and every input. -/
private theorem stableUnitReplacement_rightFamily :
    OrthogonalUnitTransport.RightReplacementFamily (C := (EnrichedFunctorCat PointedCGWH.{u, v}
      OrthogonalOperatorIndex.{u, v}))
      (constructedStableModel.{u, v} (B := B))
      (stableUnitAxiomWitness.{u, v} (B := B)) :=
  OrthogonalUnitTransport.unitWitness_rightFamily (C := (EnrichedFunctorCat PointedCGWH.{u, v}
    OrthogonalOperatorIndex.{u, v}))
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := OrthogonalOperatorIndex.{u, v}) (B := B))
    (constructedStableModel.{u, v} (B := B)) (level_cofibrations_eq_stable (B := B))
    (stablePushoutProductAxiom (B := B)) (levelTensorUnit_isCofibrant (B := B))
    (originalLevelUnitFactor (B := B))

/-- The original complete left unit replacement uses the actual original q and left unitor. -/
theorem stableUnitReplacement_left (X : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
    (hX : letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      constructedStableModel (B := B); IsCofibrant X) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      constructedStableModel (B := B)
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
      ((leftUnitReplacementMap (stableUnitAxiomWitness (B := B)).q).app X) :=
  stableUnitReplacement_leftFamily (B := B) X hX

/-- The original complete right unit replacement retains the actual original q and right unitor. -/
theorem stableUnitReplacement_right (X : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}))
    (hX : letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      constructedStableModel (B := B); IsCofibrant X) :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      constructedStableModel (B := B)
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
      ((rightUnitReplacementMap (stableUnitAxiomWitness (B := B)).q).app X) :=
  stableUnitReplacement_rightFamily (B := B) X hX

/-- The full actual constructed stable model uses the same original unit factor and all four model laws. -/
theorem stableSmashMonoidalModel :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
      constructedStableModel (B := B)
    IsClosedSymmetricMonoidalModelCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}) :=
  HomotopicalAlgebra.ModelCategory.TypedUnitModelChange.monoidalModel
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := OrthogonalOperatorIndex.{u, v}) (B := B))
    (constructedStableModel (B := B)) (level_cofibrations_eq_stable (B := B))
    (stablePushoutProductAxiom (B := B)) (levelTensorUnit_isCofibrant (B := B))
    (originalLevelUnitFactor (B := B))

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSmash
