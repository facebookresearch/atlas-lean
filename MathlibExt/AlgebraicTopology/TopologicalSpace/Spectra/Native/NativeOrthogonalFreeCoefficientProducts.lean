/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceFreeSmash
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeOrthogonalFreePairBifunctor
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceSmashClosed
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableGeneratorClasses
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKIsoTransport
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductGeneratorCriterion
import MathlibExt.CategoryTheory.Monoidal.FreePairTransport

/-!
# Free coefficient products on the native source tensor

The original evaluation and Day comparisons are assembled while the source context is symbolic.
Their complete pair is then read at the selected target tensor before either coefficient map is
chosen. The stock output free adjunction retains both legs of every coefficient pushout product.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalOpposite HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open scoped MonoidalClosed CategoryTheory.MonObj CGWH.modelCategory CGWH.limits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalPairTransport

universe uC vC uD vD uR uS
variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [HasPushouts D]
  {R : Type uR} {S : Type uS}

/-- The original two mapped PP legs, before selecting either functor or target tensor. -/
def MappedPairMembershipType (F : R → C ⥤ D) (G : S → C ⥤ D)
    (W : MorphismProperty D) (r : R) (s : S)
    {M M' N N' : C} (i : M ⟶ M') (j : N ⟶ N') : Prop :=
  W (CategoryTheory.Arrow.mk ((F r).map i) □ CategoryTheory.Arrow.mk ((G s).map j)).hom

/-- All original indices, coefficients, maps and preservation premises on the complete mapped pair. -/
def MappedPairMembershipFamilyType (F : R → C ⥤ D) (G : S → C ⥤ D)
    (P Q : MorphismProperty C) (W : MorphismProperty D) : Prop :=
  ∀ (r : R) (s : S) {M M' N N' : C} (i : M ⟶ M') (j : N ⟶ N'),
    P i → Q j → MappedPairMembershipType F G W r s i j

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalPairTransport

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.ModuleStage.CoefficientProducts

universe uV vV uI uJ
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  [SymmetricCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {J : Type uJ} [EnrichedCategory V J]
  [HasPushouts V] [HasPushouts (EnrichedFunctorCat V J)]
  (E : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
  (a : I → J)


/-- The complete original component type with the native public degree and coefficient names. -/
def ComponentFamilyType (t : I → I → I) : Type _ :=
  ∀ (r s : I) (X Y : V),
    Orthogonal.CanonicalSourceFreeSmash.ModuleStage.PairIsoType S E a r s (t r s) X Y

/-- Every original coefficient product on the transported source tensor, before choosing source data. -/
def FamilyType (t : I → I → I) : Type _ :=
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  ∀ (r s : I) {M M' N N' : V} (i : M ⟶ M') (j : N ⟶ N'),
    (Free.functor (a (t r s))).mapArrow.obj
        (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j) ≅
      CategoryTheory.Arrow.mk (Free.coefficientMap (a r) i) □
        CategoryTheory.Arrow.mk (Free.coefficientMap (a s) j)

/-- A whole original pair family and the stock output Free adjunction transport both coefficient legs. -/
def ofPairFamily (t : I → I → I)
    (pair : FullFunctorFamily.FamilyType S E a t) : FamilyType S E a t := by
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  intro r s A B K T i j
  letI : (Free.functor (V := V) (a (t r s))).IsLeftAdjoint :=
    (Free.adjunction (V := V) (a (t r s))).isLeftAdjoint
  exact CategoryTheory.FreePairTransport.pairPushoutProductIso
    (Free.functor (V := V) (a r)) (Free.functor (V := V) (a s))
    (Free.functor (V := V) (a (t r s))) (pair r s) i j

variable (h : ∀ n, E.functor ⋙ evaluation (a n) ≅
  CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)

/-- The complete genuine source reconstruction supplies the independently stated coefficient family. -/
def originalFamily (t : I → I → I)
    (comparison : ∀ (r s : I) (X Y : V),
      Free.object r X ⊗ Free.object s Y ≅ Free.object (t r s) (X ⊗ Y))
    (naturality : ∀ (r s : I) ⦃X X' Y Y' : V⦄ (f : X ⟶ X') (g : Y ⟶ Y'),
      Orthogonal.SphereSmashFree.Primitive.Compatible
        (Free.coefficientMap r f) (Free.coefficientMap s g)
        (Free.coefficientMap (t r s) (f ⊗ₘ g))
        (comparison r s X Y) (comparison r s X' Y')) : FamilyType S E a t :=
  ofPairFamily S E a t (FullFunctorFamily.originalFamily S E a h t comparison naturality)

/-- The complete original pair-membership result is fixed before any coefficient maps are supplied. -/
def MembershipType (W : MorphismProperty (EnrichedFunctorCat V J)) (r s : I)
    {M M' N N' : V} (i : M ⟶ M') (j : N ⟶ N') : Prop :=
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  OrthogonalPairTransport.MappedPairMembershipType
    (fun r : I => Free.functor (V := V) (a r))
    (fun s : I => Free.functor (V := V) (a s)) W r s i j

/-- The whole coefficient-preservation formula, with both original input maps. -/
def MembershipFamilyType (P Q : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) : Prop :=
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  OrthogonalPairTransport.MappedPairMembershipFamilyType
    (fun r : I => Free.functor (V := V) (a r))
    (fun s : I => Free.functor (V := V) (a s)) P Q W

/-- Scalar products and genuine output-Free preservation give the complete native pair formula. -/
theorem membership (t : I → I → I) (e : FamilyType S E a t) (P Q R : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) [W.RespectsIso]
    (hBase : MorphismProperty.PushoutProductLe P Q R)
    (hFree : ∀ (a : J) {A B : V} (f : A ⟶ B), R f →
      W ((Free.functor (V := V) a).map f)) :
    MembershipFamilyType S E a P Q W := by
  let := RightModuleFree.tensorMonoidal S
  let := Monoidal.transport E
  intro r s A B K T i j hi hj
  exact (W.arrow_mk_iso_iff (e r s i j)).mp
    (hFree (a (t r s))
      (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom (hBase i j hi hj))

/-- Every original target degree remains in both literal free-generator classes. -/
def GeneratorProductType (P Q : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) : Prop :=
  letI := RightModuleFree.tensorMonoidal S
  letI := Monoidal.transport E
  MorphismProperty.PushoutProductLe
    (MorphismProperty.adjointFamilyGenerators (fun a : J => Free.functor (V := V) a) P)
    (MorphismProperty.adjointFamilyGenerators (fun a : J => Free.functor (V := V) a) Q) W

/-- Reindexing both genuine coefficient maps retains the full original generator products. -/
theorem generatorProducts (t : I → I → I) (e : FamilyType S E a t)
    (d : J → I) (hd : ∀ j, a (d j) = j)
    (P Q R : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) [W.RespectsIso]
    (hBase : MorphismProperty.PushoutProductLe P Q R)
    (hFree : ∀ (a : J) {A B : V} (f : A ⟶ B), R f →
      W ((Free.functor (V := V) a).map f)) :
    GeneratorProductType S E P Q W := by
  let := RightModuleFree.tensorMonoidal S
  let := Monoidal.transport E
  apply CategoryTheory.FreePairTransport.generatorPair_pushoutProductLe
    (fun a : J => Free.functor (V := V) a)
    (fun a : J => Free.functor (V := V) a) P Q W
  intro a' b' A B K T i j hi hj
  change W (CategoryTheory.Arrow.mk (Free.coefficientMap a' i) □
    CategoryTheory.Arrow.mk (Free.coefficientMap b' j)).hom
  rw [← hd a', ← hd b']
  exact membership S E a t e P Q R W hBase hFree (d a') (d b') i j hi hj

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.ModuleStage.CoefficientProducts


namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.SelectedCoefficientProducts

universe uV vV uI vI uJ
open PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]
  {q : Enriched.ModuleMappingR.SelectedSource V I}
  {J : Type uJ} [EnrichedCategory V J] [HasPushouts V]
  [HasPushouts (EnrichedFunctorCat V J)] (c : SelectedPair.Context q J)

/-- The entire original native pair component family, with its public binder names. -/
def ComponentFamilyType : Type _ :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  ModuleStage.CoefficientProducts.ComponentFamilyType q.coefficient
    c.sourceEquivalence c.indexMap c.tensorIndex

/-- The same original selected pair supplies all components and both maps. -/
def componentFamily : ComponentFamilyType c := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact SelectedPair.pairIso c

/-- The complete two-map coefficient product at the original selected source context. -/
def FamilyType : Type _ :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  ModuleStage.CoefficientProducts.FamilyType q.coefficient
    c.sourceEquivalence c.indexMap c.tensorIndex

/-- Both original coefficient legs are transported by the stock output Free adjunction
and the complete original source bifunctor, before selecting a native source. -/
def coefficientProducts : FamilyType c := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact ModuleStage.CoefficientProducts.originalFamily q.coefficient
    c.sourceEquivalence c.indexMap c.evaluationComparison c.tensorIndex
    c.diagramPair c.diagramPairCoefficient


/-- The original complete equivalence regarded at the canonical source-context boundary. -/
def targetContext :
    Enriched.ModuleMappingR.SourceContext q (EnrichedFunctorCat V J) where
  equivalence := c.sourceEquivalence

/-- The selected membership result uses the whole named original source tensor. -/
def MembershipType (W : MorphismProperty (EnrichedFunctorCat V J)) (r s : I)
    {M M' N N' : V} (i : M ⟶ M') (j : N ⟶ N') : Prop :=
  letI := (targetContext c).monoidalCategory
  OrthogonalPairTransport.MappedPairMembershipType
    (fun r : I => Free.functor (V := V) (c.indexMap r))
    (fun s : I => Free.functor (V := V) (c.indexMap s)) W r s i j

/-- Both complete input families retain the named canonical source tensor and both PP legs. -/
def MembershipFamilyType (P Q : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) : Prop :=
  letI := (targetContext c).monoidalCategory
  OrthogonalPairTransport.MappedPairMembershipFamilyType
    (fun r : I => Free.functor (V := V) (c.indexMap r))
    (fun s : I => Free.functor (V := V) (c.indexMap s)) P Q W

/-- The scalar product and genuine output free maps supply the complete selected coefficient formula. -/
theorem membership (P Q R : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) [W.RespectsIso]
    (hBase : MorphismProperty.PushoutProductLe P Q R)
    (hFree : ∀ (a : J) {A B : V} (f : A ⟶ B), R f →
      W ((Free.functor (V := V) a).map f)) : MembershipFamilyType c P Q W := by
  unfold MembershipFamilyType targetContext
    Enriched.ModuleMappingR.SourceContext.monoidalCategory
  rw [q.moduleMonoidal_eq_primitive]
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact ModuleStage.CoefficientProducts.membership q.coefficient
    c.sourceEquivalence c.indexMap c.tensorIndex (coefficientProducts c) P Q R W hBase hFree

/-- The complete two original target-indexed free-generator classes. -/
def GeneratorProductType (P Q : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) : Prop :=
  letI := (targetContext c).monoidalCategory
  MorphismProperty.PushoutProductLe
    (MorphismProperty.adjointFamilyGenerators (fun a : J => Free.functor (V := V) a) P)
    (MorphismProperty.adjointFamilyGenerators (fun a : J => Free.functor (V := V) a) Q) W

/-- Both original coefficient reindexings preserve every target degree and literal generator product. -/
theorem generatorProducts (d : J → I) (hd : ∀ a, c.indexMap (d a) = a)
    (P Q R : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) [W.RespectsIso]
    (hBase : MorphismProperty.PushoutProductLe P Q R)
    (hFree : ∀ (a : J) {A B : V} (f : A ⟶ B), R f →
      W ((Free.functor (V := V) a).map f)) : GeneratorProductType c P Q W := by
  unfold GeneratorProductType targetContext
    Enriched.ModuleMappingR.SourceContext.monoidalCategory
  rw [q.moduleMonoidal_eq_primitive]
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  let : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact ModuleStage.CoefficientProducts.generatorProducts q.coefficient
    c.sourceEquivalence c.indexMap c.tensorIndex (coefficientProducts c) d hd
    P Q R W hBase hFree

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.SelectedCoefficientProducts


namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.CoefficientTargetStage

universe uV vV uI uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} {J : Type uJ} [EnrichedCategory V J]
  [MonoidalCategory (EnrichedFunctorCat V J)]
  [HasPushouts V] [HasPushouts (EnrichedFunctorCat V J)] (a : I → J)

/-- Both complete original free functors and their genuine output free functor at an abstract target tensor. -/
def BifunctorFamilyType (t : I → I → I) : Type _ :=
  ∀ (r s : I),
    (Free.functor (a r)).prod (Free.functor (a s)) ⋙ tensor (EnrichedFunctorCat V J) ≅
      tensor V ⋙ Free.functor (a (t r s))

/-- Every original coefficient PP Iso, before selecting a concrete target tensor dictionary. -/
def FamilyType (t : I → I → I) : Type _ :=
  ∀ (r s : I) {M M' N N' : V} (i : M ⟶ M') (j : N ⟶ N'),
    (Free.functor (a (t r s))).mapArrow.obj
        (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j) ≅
      CategoryTheory.Arrow.mk (Free.coefficientMap (a r) i) □
        CategoryTheory.Arrow.mk (Free.coefficientMap (a s) j)

/-- The full free-pair comparison and stock output adjunction transport both literal coefficient maps. -/
def ofPairFamily (t : I → I → I) (pair : BifunctorFamilyType (V := V) a t) : FamilyType (V := V) a t := by
  intro r s M M' N N' i j
  letI : (Free.functor (V := V) (a (t r s))).IsLeftAdjoint :=
    (Free.adjunction (V := V) (a (t r s))).isLeftAdjoint
  exact CategoryTheory.FreePairTransport.pairPushoutProductIso
    (Free.functor (V := V) (a r)) (Free.functor (V := V) (a s))
    (Free.functor (V := V) (a (t r s))) (pair r s) i j

/-- The literal original PP result at the abstract target tensor, with both full coefficient maps. -/
def MembershipType (W : MorphismProperty (EnrichedFunctorCat V J)) (r s : I)
    {M M' N N' : V} (i : M ⟶ M') (j : N ⟶ N') : Prop :=
  W (CategoryTheory.Arrow.mk (Free.coefficientMap (a r) i) □
    CategoryTheory.Arrow.mk (Free.coefficientMap (a s) j)).hom

/-- The full original coefficient preservation family at that same abstract tensor. -/
def MembershipFamilyType (P Q : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) : Prop :=
  ∀ (r s : I) {M M' N N' : V} (i : M ⟶ M') (j : N ⟶ N'),
    P i → Q j → MembershipType (V := V) a W r s i j

/-- The complete PP Iso family and original scalar/output-Free laws give every literal membership. -/
theorem membership (t : I → I → I) (e : FamilyType (V := V) a t) (P Q R : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) [W.RespectsIso]
    (hBase : MorphismProperty.PushoutProductLe P Q R)
    (hFree : ∀ (a : J) {M N : V} (f : M ⟶ N), R f →
      W ((Free.functor (V := V) a).map f)) : MembershipFamilyType (V := V) a P Q W := by
  intro r s M M' N N' i j hi hj
  exact (W.arrow_mk_iso_iff (e r s i j)).mp
    (hFree (a (t r s))
      (CategoryTheory.Arrow.mk i □ CategoryTheory.Arrow.mk j).hom (hBase i j hi hj))

/-- Both whole original target-indexed free-generator classes at the same tensor. -/
def GeneratorProductType (P Q : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) : Prop :=
  MorphismProperty.PushoutProductLe
    (MorphismProperty.adjointFamilyGenerators (fun a : J => Free.functor (V := V) a) P)
    (MorphismProperty.adjointFamilyGenerators (fun a : J => Free.functor (V := V) a) Q) W

/-- Reindex both full original coefficient legs before a concrete target tensor is chosen. -/
theorem generatorProducts (t : I → I → I) (e : FamilyType (V := V) a t)
    (d : J → I) (hd : ∀ j, a (d j) = j)
    (P Q R : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) [W.RespectsIso]
    (hBase : MorphismProperty.PushoutProductLe P Q R)
    (hFree : ∀ (a : J) {M N : V} (f : M ⟶ N), R f →
      W ((Free.functor (V := V) a).map f)) : GeneratorProductType (V := V) P Q W := by
  apply CategoryTheory.FreePairTransport.generatorPair_pushoutProductLe
    (fun a : J => Free.functor (V := V) a)
    (fun a : J => Free.functor (V := V) a) P Q W
  intro a' b' M M' N N' i j hi hj
  change W (CategoryTheory.Arrow.mk (Free.coefficientMap a' i) □
    CategoryTheory.Arrow.mk (Free.coefficientMap b' j)).hom
  rw [← hd a', ← hd b']
  exact membership a t e P Q R W hBase hFree (d a') (d b') i j hi hj

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.CoefficientTargetStage

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.CanonicalCoefficientProducts

universe uV vV uI vI uJ
open PointedCGWH.Spectra.Orthogonal
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V]
  {q : Enriched.ModuleMappingR.SelectedSource V I}
  {J : Type uJ} [EnrichedCategory V J] [HasPushouts V]
  [HasPushouts (EnrichedFunctorCat V J)]
  (source : Enriched.ModuleMappingR.SourceContext q (EnrichedFunctorCat V J)) (a : I → J)

/-- The literal two-coefficient formula uses the original named source context. -/
def MembershipType (W : MorphismProperty (EnrichedFunctorCat V J)) (r s : I)
    {M M' N N' : V} (i : M ⟶ M') (j : N ⟶ N') : Prop :=
  letI := source.monoidalCategory
  CoefficientTargetStage.MembershipType (V := V) a W r s i j

/-- Both complete original coefficient families share that same source tensor. -/
def MembershipFamilyType (P Q : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) : Prop :=
  letI := source.monoidalCategory
  CoefficientTargetStage.MembershipFamilyType (V := V) a P Q W

/-- Every original component Iso uses the complete named source tensor before native degrees. -/
def ComponentFamilyType (t : I → I → I) : Type _ :=
  letI := source.monoidalCategory
  ∀ (r s : I) (X Y : V),
    Free.object (a r) X ⊗ Free.object (a s) Y ≅ Free.object (a (t r s)) (X ⊗ Y)

/-- Both entire original coefficient functors use the same named source tensor. -/
def BifunctorFamilyType (t : I → I → I) : Type _ :=
  letI := source.monoidalCategory
  ∀ (r s : I),
    (Free.functor (a r)).prod (Free.functor (a s)) ⋙ tensor (EnrichedFunctorCat V J) ≅
      tensor V ⋙ Free.functor (a (t r s))

/-- The complete coefficient PP Iso family retains both original legs and output free functor. -/
def FamilyType (t : I → I → I) : Type _ :=
  letI := source.monoidalCategory
  CoefficientTargetStage.FamilyType (V := V) a t

variable
  (h : letI := q.dayMonoidal
    let := q.coefficientMonObj
    ∀ n, source.equivalence.functor ⋙ evaluation (a n) ≅
      CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation q.coefficient n)
  (t : I → I → I)
  (comparison : letI := q.dayMonoidal
    ∀ (r s : I) (X Y : V),
      Free.object r X ⊗ Free.object s Y ≅ Free.object (t r s) (X ⊗ Y))
  (naturality : letI := q.dayMonoidal
    ∀ (r s : I) ⦃X X' Y Y' : V⦄ (f : X ⟶ X') (g : Y ⟶ Y'),
      SphereSmashFree.Primitive.Compatible
        (Free.coefficientMap r f) (Free.coefficientMap s g)
        (Free.coefficientMap (t r s) (f ⊗ₘ g))
        (comparison r s X Y) (comparison r s X' Y'))

include h t comparison in
/-- The actual original component supplier has the canonical source-context type while symbolic. -/
def componentFamily : ComponentFamilyType source a t := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact CanonicalSourceFreeSmash.ModuleStage.SymbolicPair.pair q.coefficient
    source.equivalence a h t comparison

include h t comparison naturality in
/-- The full original bifunctor reconstruction has the same actual source-context type while symbolic. -/
def bifunctorFamily : BifunctorFamilyType source a t := by
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI : HasCoequalizers (EnrichedFunctorCat V I) := q.dayCoequalizers
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) := q.dayTensorLeftPreserves
  letI : ∀ X : EnrichedFunctorCat V I,
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := q.dayTensorRightPreserves
  exact ModuleStage.FullFunctorFamily.originalFamily q.coefficient
    source.equivalence a h t comparison naturality

include h t comparison naturality in
/-- The stock output Free adjunction and original whole pair retain that exact source-context PP type. -/
def coefficientProducts : FamilyType source a t := by
  letI := source.monoidalCategory
  exact CoefficientTargetStage.ofPairFamily (V := V) a t
    (bifunctorFamily source a h t comparison naturality)

include h t comparison naturality in
/-- The original full evaluation and Day records prove the source-context coefficient family. -/
theorem membership (P Q R : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) [W.RespectsIso]
    (hBase : MorphismProperty.PushoutProductLe P Q R)
    (hFree : ∀ (a : J) {M N : V} (f : M ⟶ N), R f →
      W ((Free.functor (V := V) a).map f)) : MembershipFamilyType source a P Q W := by
  let := source.monoidalCategory
  exact CoefficientTargetStage.membership (V := V) a t
    (coefficientProducts source a h t comparison naturality) P Q R W hBase hFree

/-- Both original target-indexed generator classes use the same complete native source tensor. -/
def GeneratorProductType (P Q : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) : Prop :=
  letI := source.monoidalCategory
  CoefficientTargetStage.GeneratorProductType (V := V) P Q W

include h t comparison naturality in
/-- All original target degrees and both original generator classes survive the source reconstruction. -/
theorem generatorProducts (d : J → I) (hd : ∀ j, a (d j) = j)
    (P Q R : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) [W.RespectsIso]
    (hBase : MorphismProperty.PushoutProductLe P Q R)
    (hFree : ∀ (a : J) {M N : V} (f : M ⟶ N), R f →
      W ((Free.functor (V := V) a).map f)) : GeneratorProductType source P Q W := by
  let := source.monoidalCategory
  exact CoefficientTargetStage.generatorProducts (V := V) a t
    (coefficientProducts source a h t comparison naturality) d hd P Q R W hBase hFree

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.CanonicalCoefficientProducts


namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.CoefficientTargetStage
universe uV vV uI uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} {J : Type uJ} [EnrichedCategory V J]
  [MonoidalCategory (EnrichedFunctorCat V J)]
  (a : I → J)

/-- Every original free component at the same full tensor as the genuine pair bifunctor. -/
def ComponentFamilyType (t : I → I → I) : Type _ :=
  ∀ (r s : I) (X Y : V),
    Free.object (a r) X ⊗ Free.object (a s) Y ≅ Free.object (a (t r s)) (X ⊗ Y)

/-- Project every original component from the full original bifunctor before concrete source data. -/
def componentsOfPairFamily (t : I → I → I)
    (pair : BifunctorFamilyType (V := V) a t) : ComponentFamilyType (V := V) a t :=
  fun r s X Y => (pair r s).app (X, Y)

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.CoefficientTargetStage

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.CoefficientTargetStage

universe uV vV uI uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} {J : Type uJ} [EnrichedCategory V J]
  [MonoidalCategory (EnrichedFunctorCat V J)]
  [HasPushouts V] [HasPushouts (EnrichedFunctorCat V J)]

/-- Preserve the entire literal two-map coefficient family before choosing a native model or coefficient. -/
theorem literalMembershipFamily (a : I → J) (t : I → I → I)
    (e : FamilyType (V := V) a t) (P Q R : MorphismProperty V)
    (W : MorphismProperty (EnrichedFunctorCat V J)) [W.RespectsIso]
    (hBase : MorphismProperty.PushoutProductLe P Q R)
    (hFree : ∀ (a : J) {M N : V} (f : M ⟶ N), R f →
      W ((Free.functor (V := V) a).map f)) :
    ∀ (r s : I) {M M' N N' : V} (i : M ⟶ M') (j : N ⟶ N'), P i → Q j →
      W (CategoryTheory.Arrow.mk (Free.coefficientMap (a r) i) □
        CategoryTheory.Arrow.mk (Free.coefficientMap (a s) j)).hom := by
  intro r s M M' N N' i j hi hj
  exact membership a t e P Q R W hBase hFree r s i j hi hj

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalSourcePair.CoefficientTargetStage
