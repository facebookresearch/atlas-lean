/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKMonoidal
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductGeneratorCriterion
import MathlibExt.CategoryTheory.Monoidal.FreePairTransport
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CofibrantFree
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKAllSourceLocality

/-!
# Stabilization tests for smash products

Right tensoring with a cofibrant object preserves Omega tests when its internal Hom
sends Omega objects to Omega objects. Under the pushout-product axiom, these tests
propagate to products with free coefficient arrows and stabilization generators,
retaining the stated cofibrancy and generator-test hypotheses. The explicit
generator-class equations then assemble the stable pushout-product laws.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.SmashReduction

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] Native.modelCategory


variable [MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)] [SymmetricCategory (EnrichedFunctorCat
      PointedCGWH.{u, v} I)] [MonoidalClosed (EnrichedFunctorCat PointedCGWH.{u, v} I)]

/-- All original test arrows between cofibrant endpoints are preserved by the chosen whole right tensor. -/
def RightTensorTests (K : (EnrichedFunctorCat PointedCGWH.{u, v} I)) : Prop :=
  ∀ {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)}, IsCofibrant X → IsCofibrant Y →
    ∀ (f : X ⟶ Y), omegaTests s f → omegaTests s (f ▷ K)

/-- The actual closed tensor adjunction and right-adjoint Omega law prove the full original right-tensor tests. -/
theorem rightTensorTests (hPP : MonoidalPushoutProductAxiom (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (K : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hK : IsCofibrant K)
    (hOmega : ∀ E : (EnrichedFunctorCat PointedCGWH.{u, v} I), IsOmega s E → IsOmega s ((ihom K).obj E)) :
    RightTensorTests s K := by
  let _ : IsCofibrant K := hK
  let _ : (tensorRightIhomAdjunction K).IsQuillenAdjunction :=
    hPP.tensorRightIhomAdjunction_isQuillenAdjunction K
  intro X Y hX hY f hf
  let _ : IsCofibrant X := hX
  let _ : IsCofibrant Y := hY
  exact adjointMap_omegaTests_of_cofibrant s (tensorRightIhomAdjunction K) hOmega f hf

/-- The complete chosen tensor pushout and its original two legs prove every original test for the PP arrow. -/
theorem pushoutProductTests (hPP : MonoidalPushoutProductAxiom (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (K T : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hK : IsCofibrant K) (hT : IsCofibrant T)
    (hTestsK : RightTensorTests s K) (hTestsT : RightTensorTests s T)
    {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} (hX : IsCofibrant X) (hY : IsCofibrant Y)
    (i : X ⟶ Y) (hiC : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) i) (hiW : omegaTests s i) (j : K ⟶ T) :
    omegaTests s (Arrow.mk i □ Arrow.mk j).hom := by
  let _ : IsCofibrant K := hK
  let _ : IsCofibrant T := hT
  let _ : IsCofibrant X := hX
  let _ : IsCofibrant Y := hY
  let _ : IsCofibrant (X ⊗ K) := hPP.isCofibrant_tensorObj X K
  let _ : IsCofibrant (Y ⊗ K) := hPP.isCofibrant_tensorObj Y K
  let _ : IsCofibrant (X ⊗ T) := hPP.isCofibrant_tensorObj X T
  have hiK := hPP.whiskerRight_mem_cofibrations i K hiC
  have hiKW := hTestsK hX hY i hiW
  have hLeg := (pushout_cofibration_omegaTests s
    (i ▷ K) (X ◁ j) (pushout.inl (i ▷ K) (X ◁ j)) (pushout.inr (i ▷ K) (X ◁ j))
    (IsPushout.of_hasPushout (i ▷ K) (X ◁ j)) hiK hiKW).2
  have hFac : pushout.inr (i ▷ K) (X ◁ j) ≫ (Arrow.mk i □ Arrow.mk j).hom = i ▷ T := by
    change pushout.inr (i ▷ K) (X ◁ j) ≫
      pushout.desc (Y ◁ j) (i ▷ T) ((whisker_exchange i j).symm) = i ▷ T
    exact pushout.inr_desc _ _ _
  exact (omegaTests s).of_precomp (pushout.inr (i ▷ K) (X ◁ j))
    (Arrow.mk i □ Arrow.mk j).hom hLeg (by rw [hFac]; exact hTestsT hX hY i hiW)

/-- All original coefficient free functors have their whole PP-test family typed before native values. -/
def FreeCoefficientTests {A : Type} (F : A → PointedCGWH.{u, v} ⥤ (EnrichedFunctorCat PointedCGWH.{u, v} I)) : Prop :=
  ∀ {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)}, IsCofibrant X → IsCofibrant Y →
    ∀ (i : X ⟶ Y), cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) i → omegaTests s i →
      ∀ (a : A) {M N : PointedCGWH.{u, v}}, IsCofibrant M → IsCofibrant N →
        ∀ (j : M ⟶ N), omegaTests s (Arrow.mk i □ Arrow.mk ((F a).map j)).hom

/-- The actual free coefficient objects and right-tensor laws supply every full original coefficient PP test. -/
theorem freeCoefficientTests (hPP : MonoidalPushoutProductAxiom (EnrichedFunctorCat PointedCGWH.{u, v} I))
    {A : Type} (F : A → PointedCGWH.{u, v} ⥤ (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hCof : ∀ a M, IsCofibrant M → IsCofibrant ((F a).obj M))
    (hRight : ∀ a M, IsCofibrant M → RightTensorTests s ((F a).obj M)) :
    FreeCoefficientTests s F := by
  intro X Y hX hY i hiC hiW a M N hM hN j
  exact pushoutProductTests s hPP ((F a).obj M) ((F a).obj N)
    (hCof a M hM) (hCof a N hN) (hRight a M hM) (hRight a N hN) hX hY i hiC hiW ((F a).map j)

/-- The full right-tensor test family retains the original implicit cofibrant endpoint calling convention. -/
def RightTensorTestsClass (K : (EnrichedFunctorCat PointedCGWH.{u, v} I)) : Prop :=
  ∀ {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} [IsCofibrant X] [IsCofibrant Y],
    ∀ (f : X ⟶ Y), omegaTests s f → omegaTests s (f ▷ K)

/-- The actual chosen adjunction proves the full class-bound family before a native coefficient is supplied. -/
theorem rightTensorTestsClass (hPP : MonoidalPushoutProductAxiom (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (K : (EnrichedFunctorCat PointedCGWH.{u, v} I)) (hK : IsCofibrant K)
    (hOmega : ∀ E : (EnrichedFunctorCat PointedCGWH.{u, v} I), IsOmega s E → IsOmega s ((ihom K).obj E)) :
    RightTensorTestsClass s K := by
  intro X Y hX hY f hf
  exact rightTensorTests s hPP K hK hOmega hX hY f hf

/-- Every original coefficient PP test is stated as a whole class-bound family before actual free map getters. -/
def FreeCoefficientTestsClass {A : Type} (F : A → PointedCGWH.{u, v} ⥤ (EnrichedFunctorCat PointedCGWH.{u, v}
      I)) : Prop :=
  ∀ {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} I)} [IsCofibrant X] [IsCofibrant Y],
    ∀ (i : X ⟶ Y), cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) i → omegaTests s i →
      ∀ (a : A) {M N : PointedCGWH.{u, v}} [IsCofibrant M] [IsCofibrant N],
        ∀ (j : M ⟶ N), omegaTests s (Arrow.mk i □ Arrow.mk ((F a).map j)).hom

/-- Actual free object cofibrancy and actual right-tensor tests prove the full original coefficient PP family. -/
theorem freeCoefficientTestsClass (hPP : MonoidalPushoutProductAxiom (EnrichedFunctorCat PointedCGWH.{u, v} I))
    {A : Type} (F : A → PointedCGWH.{u, v} ⥤ (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hCof : ∀ a M, IsCofibrant M → IsCofibrant ((F a).obj M))
    (hRight : ∀ a M, IsCofibrant M → RightTensorTests s ((F a).obj M)) :
    FreeCoefficientTestsClass s F := by
  intro X Y hX hY i hiC hiW a M N hM hN j
  exact freeCoefficientTests s hPP F hCof hRight hX hY i hiC hiW a hM hN j

omit [SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)]
  [MonoidalClosed (EnrichedFunctorCat PointedCGWH.{u, v} I)] in
/-- The full original K-by-free-generator test is typed on its whole coefficient functor family. -/
theorem generatorRightTests {A : Type} (F : A → PointedCGWH.{u, v} ⥤ (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (P : MorphismProperty PointedCGWH.{u, v})
    (hP : ∀ {M N : PointedCGWH.{u, v}} (j : M ⟶ N), P j → IsCofibrant M ∧ IsCofibrant N)
    (hFree : FreeCoefficientTestsClass s F)
    (hGeneratorTests : generators s ≤ omegaTests s) :
    MorphismProperty.PushoutProductLe (generators s)
      (MorphismProperty.adjointFamilyGenerators F P) (omegaTests s) := by
  intro X Y K T i j hi hj
  obtain ⟨a, ha⟩ := (MorphismProperty.adjointFamilyGenerators_iff F P j).mp hj
  have hScalar := hP a.2.1.hom a.2.2
  let _ : IsCofibrant a.2.1.left := hScalar.1
  let _ : IsCofibrant a.2.1.right := hScalar.2
  have hEnds := generatorEndpoints s i hi
  let _ : IsCofibrant X := hEnds.1
  let _ : IsCofibrant Y := hEnds.2
  exact CategoryTheory.FreePairTransport.pushoutProduct_mem_of_pairArrow_eq (omegaTests s)
    i j (Arrow.mk i) ((F a.1).mapArrow.obj a.2.1) rfl ha
    (hFree i (generators_le_cofibrations s i hi) (hGeneratorTests i hi) a.1 a.2.1.hom)

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.SmashReduction

section OriginalStableGeneratorAssembly
universe uC vC wC
namespace HomotopicalAlgebra.OriginalStableSmashAssembly
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]

/-- The complete original generating record is typed at its explicitly chosen model before native specialization. -/
abbrev GenerationDataType (M : ModelCategory C) (κ : Cardinal.{wC}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType] : Type _ :=
  letI : ModelCategory C := M
  CofibrantGenerationData C κ

/-- The original I/K products and original class equations give all stable PP laws for the same selected model. -/
theorem pushoutProductAxiom (M : ModelCategory C) (κ : Cardinal.{wC})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (G : GenerationDataType M κ) (I K W : MorphismProperty C)
    (hI : G.I = I) (hK : G.J = K)
    (hCof : (letI : ModelCategory C := M; cofibrations C) = I.rlp.llp)
    (hTriv : (letI : ModelCategory C := M; trivialCofibrations C) = I.rlp.llp ⊓ W)
    (hII : MorphismProperty.PushoutProductLe I I I.rlp.llp)
    (hKI : MorphismProperty.PushoutProductLe K I (I.rlp.llp ⊓ W)) :
    letI : ModelCategory C := M
    MonoidalPushoutProductAxiom C := by
  let : ModelCategory C := M
  apply G.pushoutProductAxiom_of_generatorProducts
  · rw [hI, hCof]
    exact hII
  · rw [hK, hI, hTriv]
    exact hKI

end HomotopicalAlgebra.OriginalStableSmashAssembly
end OriginalStableGeneratorAssembly

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.SmashReduction
variable {I L A : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] Native.modelCategory
variable [MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)]
  [SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)]
  [MonoidalClosed (EnrichedFunctorCat PointedCGWH.{u, v} I)]

/-- The entire original free-family function condition is stated before concrete index values. -/
def OriginalFreeFunctionOmega (a : A → I) : Prop :=
  ∀ (r : A) (M : PointedCGWH.{u, v}), IsCofibrant M →
    ∀ E : EnrichedFunctorCat PointedCGWH.{u, v} I,
      IsOmega s E → IsOmega s ((ihom (Free.object (a r) M)).obj E)

/-- All original free-object coefficient products satisfy every original Omega test. -/
theorem originalFreeCoefficientTests (a : A → I)
    (hPP : MonoidalPushoutProductAxiom (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hOmega : OriginalFreeFunctionOmega s a) :
    FreeCoefficientTestsClass s (fun r : A => Free.functor (V := PointedCGWH.{u, v}) (a r)) := by
  apply freeCoefficientTestsClass s hPP (fun r : A => Free.functor (V := PointedCGWH.{u, v}) (a r))
  · intro r M hM
    let _ : IsCofibrant M := hM
    exact Native.freeAt_obj_isCofibrant (a r) M
  · intro r M hM
    exact rightTensorTests s hPP (Free.object (a r) M) (by
      let _ : IsCofibrant M := hM
      exact Native.freeAt_obj_isCofibrant (a r) M) (hOmega r M hM)
omit [MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)]
  [SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)]
  [MonoidalClosed (EnrichedFunctorCat PointedCGWH.{u, v} I)] in
/-- All original native K generators lie in the unchanged original I-left class. -/
theorem originalGenerators_le_ILeft : generators s ≤ (levelI (I := I)).rlp.llp := by
  rw [← Native.cofibrations_eq]
  exact generators_le_cofibrations s

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.SmashReduction
section FullGeneratorIntersection
universe uC vC
namespace HomotopicalAlgebra.OriginalStableSmashAssembly
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [HasPushouts C]
/-- The original cofibration product and whole generator test give both full class memberships. -/
theorem generatorProducts_intersection (I K W : MorphismProperty C)
    (hK : K ≤ I.rlp.llp)
    (hII : MorphismProperty.PushoutProductLe I.rlp.llp I.rlp.llp I.rlp.llp)
    (hKW : MorphismProperty.PushoutProductLe K I W) :
    MorphismProperty.PushoutProductLe K I (I.rlp.llp ⊓ W) := by
  intro X Y A Z i j hi hj
  exact ⟨hII i j (hK i hi) (I.le_llp_rlp j hj), hKW i j hi hj⟩
end HomotopicalAlgebra.OriginalStableSmashAssembly
end FullGeneratorIntersection


namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.SmashReduction
variable {I L A : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] Native.modelCategory
variable [MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)]
  [SymmetricCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)]
  [MonoidalClosed (EnrichedFunctorCat PointedCGWH.{u, v} I)]

/-- Every original K generator retains the full coefficient product Omega tests before concrete index values. -/
def OriginalGeneratorCoefficientTests (a : A → I) : Prop :=
  ∀ {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (i : X ⟶ Y), generators s i →
    ∀ (r : A) {M N : PointedCGWH.{u, v}} [IsCofibrant M] [IsCofibrant N] (j : M ⟶ N),
      omegaTests s (Arrow.mk i □ Arrow.mk (Free.coefficientMap (a r) j)).hom

/-- The original all-source K-locality and actual free function law supply every full generator coefficient test. -/
theorem originalGeneratorCoefficientTests (a : A → I)
    (hPP : MonoidalPushoutProductAxiom (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hOmega : OriginalFreeFunctionOmega s a)
    (hHom : ∀ x y : I, IsCofibrant (x ⟶[PointedCGWH.{u, v}] y)) :
    OriginalGeneratorCoefficientTests s a := by
  intro X Y i hi r M N hM hN j
  have hEnds := generatorEndpoints s i hi
  let _ : IsCofibrant X := hEnds.1
  let _ : IsCofibrant Y := hEnds.2
  have hiW : omegaTests s i := by
    exact (originalKGenerators_le_localTests s hHom) i hi
  exact originalFreeCoefficientTests s a hPP hOmega i (generators_le_cofibrations s i hi) hiW r j

/-- The same original K locality and literal target-indexed free boundary family give the whole K-by-I product. -/
theorem originalGeneratorProducts
    (hPP : MonoidalPushoutProductAxiom (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hOmega : OriginalFreeFunctionOmega s (fun x : I => x))
    (hHom : ∀ x y : I, IsCofibrant (x ⟶[PointedCGWH.{u, v}] y)) :
    MorphismProperty.PushoutProductLe (generators s) (levelI (I := I)) (omegaTests s) := by
  change MorphismProperty.PushoutProductLe (generators s)
    (MorphismProperty.adjointFamilyGenerators
      (fun x : I => Free.functor (V := PointedCGWH.{u, v}) x)
      PointedCGWH.realizedBoundaryInclusions) (omegaTests s)
  exact generatorRightTests s
    (fun x : I => Free.functor (V := PointedCGWH.{u, v}) x)
    PointedCGWH.realizedBoundaryInclusions
    (fun j hj => pointedBoundary_endpoints j hj)
    (originalFreeCoefficientTests s (fun x : I => x) hPP hOmega)
    (originalKGenerators_le_localTests s hHom)
end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.SmashReduction

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.SmashReduction

variable {I L A : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L) (a : A → I)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] Native.modelCategory
variable [MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)]
  [HasPushouts (EnrichedFunctorCat PointedCGWH.{u, v} I)]

/-- The complete original coefficient test at the caller's existing pushout proof. -/
def CallerGeneratorCoefficientTests : Prop :=
  ∀ {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (i : X ⟶ Y), generators s i →
    ∀ (r : A) {M N : PointedCGWH.{u, v}} [IsCofibrant M] [IsCofibrant N] (j : M ⟶ N),
      omegaTests s (Arrow.mk i □ Arrow.mk (Free.coefficientMap (a r) j)).hom

/-- Preserve the whole proved original family before a native generator or coefficient is chosen. -/
theorem callerGeneratorCoefficientTests (h : OriginalGeneratorCoefficientTests s a) :
    CallerGeneratorCoefficientTests s a := by
  intro X Y i hi r M N hM hN j
  exact h i hi r j

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.SmashReduction
