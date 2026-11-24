/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.BGTIndKappaModels
public import MathlibExt.AlgebraicTopology.NativeDiagramFamilies
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The actual countable coproduct functor and its swindle source

The functor is the colimit of the entire constant countable family.
Its coherent cocone retains every original injection and all parameter
arrows. The binary sum is the actual native pushout of the zero object,
identity functor and countable sum. The swindle equivalence and K-theory
vanishing are Wanted conclusions, not inputs to the cone construction.

Source: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Lemma 9.4,
page 57, with the actual source F-kappa of Definition 9.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.BGTCountableSwindleModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityMappingSpaces
open StableInfinityFiniteDiagrams StableInfinityCategoryModels
open StableInfinityFilteredColimits StableInfinityMappingSpaceMaps
open NativeDiagramFamilies BGTIndKappaModels
open scoped Simplicial

/-- The actual countable discrete indexing category. -/
abbrev CountableIndex := Discrete ℕ

/-- The actual index of the singleton summand followed by the countable tail. -/
abbrev OnePlusIndex := Discrete (PUnit ⊕ ℕ)

/-- The source vertex of the actual augmented countable index. -/
def countableApexVertex : (indexNerve (WithTerminal CountableIndex)) _⦋0⦌ :=
  ULift.up (ComposableArrows.mk₀ WithTerminal.star)

/-- The countable sum is the native colimit of the entire coherent constant family. -/
structure CountableSumSource (C : StableInfinityCategory.{0}) where
  functor : ExactFunctor C C
  family : C.toSSet ⟶ mapping (indexNerve (WithTerminal CountableIndex)) C.toSSet
  restriction : family ≫
    precomposition (indexMap (WithTerminal.incl (C := CountableIndex))) C.toSSet =
      constantFamily (indexNerve CountableIndex) C.toSSet
  apex : family ≫ evaluateAt (indexNerve (WithTerminal CountableIndex))
    C.toSSet countableApexVertex = functor.map
  cocone : ∀ x : C.toSSet _⦋0⦌,
    (rightCones C.toSSet (SSet.const x : indexNerve CountableIndex ⟶ C.toSSet)) _⦋0⦌
  coherent : ∀ x : C.toSSet _⦋0⦌,
    family.app (op ⦋0⦌) x =
      mappingZero _ _ (coconeDiagram C.toSSet (SSet.const x) (cocone x))
  universal : ∀ x : C.toSSet _⦋0⦌,
    IsInitialObject (rightCones C.toSSet (SSet.const x)) (cocone x)

/-- Every original countable coproduct injection is the actual native index edge. -/
def CountableSumSource.injection {C : StableInfinityCategory.{0}}
    (Q : CountableSumSource C) (x : C.toSSet _⦋0⦌) (i : ℕ) : C.toSSet _⦋1⦌ :=
  (coconeDiagram C.toSSet (SSet.const x) (Q.cocone x)).app (op ⦋1⦌)
    (ULift.up (nerve.edgeMk (WithTerminal.homFrom (Discrete.mk i))).edge)

/-- Actual source corner evaluation on every coherent parameter simplex. -/
def squareEvaluation (C : SSet.{0}) (p : SquareCorner) :
    mapping (indexNerve SquareCorner) C ⟶ C :=
  evaluateAt _ _ (ULift.up (ComposableArrows.mk₀ p))

/-- Identity plus the countable sum is the actual native zero-corner pushout functor. -/
structure IdentityPlusSumSource {C : StableInfinityCategory.{0}}
    (Q : CountableSumSource C) where
  functor : ExactFunctor C C
  family : C.toSSet ⟶ mapping (indexNerve SquareCorner) C.toSSet
  origin : family ≫ squareEvaluation C.toSSet .origin = SSet.const C.zero
  horizontal : family ≫ squareEvaluation C.toSSet .horizontal = 𝟙 C.toSSet
  vertical : family ≫ squareEvaluation C.toSSet .vertical = Q.functor.map
  final : family ≫ squareEvaluation C.toSSet .final = functor.map
  universal : ∀ x : C.toSSet _⦋0⦌,
    IsPushoutSquare ((mappingZero _ _).symm (family.app (op ⦋0⦌) x))
  onePlusFamily : C.toSSet ⟶
    mapping (indexNerve (WithTerminal OnePlusIndex)) C.toSSet
  onePlusRestriction : onePlusFamily ≫
    precomposition (indexMap (WithTerminal.incl (C := OnePlusIndex))) C.toSSet =
      constantFamily (indexNerve OnePlusIndex) C.toSSet
  onePlusApex : onePlusFamily ≫
    evaluateAt (indexNerve (WithTerminal OnePlusIndex)) C.toSSet
      (ULift.up (ComposableArrows.mk₀ WithTerminal.star)) = functor.map
  onePlusUniversal : ∀ x : C.toSSet _⦋0⦌,
    ∃ c : (rightCones C.toSSet
      (SSet.const x : indexNerve OnePlusIndex ⟶ C.toSSet)) _⦋0⦌,
      IsInitialObject (rightCones C.toSSet (SSet.const x)) c ∧
        onePlusFamily.app (op ⦋0⦌) x =
          mappingZero _ _ (coconeDiagram C.toSSet (SSet.const x) c)

/-- The actual index reordering for identity plus the countable tail. -/
def onePlusCountableEquiv : PUnit ⊕ ℕ ≃ ℕ where
  toFun x :=
    match x with
    | .inl _ => 0
    | .inr n => n + 1
  invFun n :=
    match n with
    | 0 => .inl PUnit.unit
    | n + 1 => .inr n
  left_inv x := by cases x with
    | inl x => cases x; rfl
    | inr n => rfl
  right_inv n := by cases n <;> rfl

/-- Reindex the entire augmented countable family by the native singleton-tail bijection. -/
def reindexedCountableFamily {C : StableInfinityCategory.{0}}
    (Q : CountableSumSource C) : C.toSSet ⟶
      mapping (indexNerve (WithTerminal OnePlusIndex)) C.toSSet :=
  Q.family ≫ precomposition
    (indexMap (WithTerminal.map
      (Discrete.functor (fun i => Discrete.mk (onePlusCountableEquiv i))))) C.toSSet

/-- The entire cone equivalence is identity on every original summand and parameter simplex. -/
def IsRelativeSwindleConeEquivalence {C : StableInfinityCategory.{0}}
    (Q : CountableSumSource C) (B : IdentityPlusSumSource Q) : Prop :=
  ∃ e : (mapping C.toSSet
    (mapping (indexNerve (WithTerminal OnePlusIndex)) C.toSSet)) _⦋1⦌,
    IsEquivalenceEdge _ e ∧
      (mapping C.toSSet _).δ 1 e = mappingZero _ _ B.onePlusFamily ∧
      (mapping C.toSSet _).δ 0 e = mappingZero _ _ (reindexedCountableFamily Q) ∧
      (StableInfinitySFunctorMaps.postcomposition C.toSSet
        (precomposition (indexMap (WithTerminal.incl (C := OnePlusIndex))) C.toSSet)).app (op ⦋1⦌) e =
        (mapping C.toSSet (mapping (indexNerve OnePlusIndex) C.toSSet)).σ 0
          (mappingZero _ _ (constantFamily (indexNerve OnePlusIndex) C.toSSet))

/-- The swindle uses an actual full natural equivalence of these native exact functors. -/
def IsSwindleEquivalence {C : StableInfinityCategory.{0}}
    (Q : CountableSumSource C) (B : IdentityPlusSumSource Q) : Prop :=
  NaturallyEquivalentMaps B.functor.map Q.functor.map ∧
    IsRelativeSwindleConeEquivalence Q B

end MathlibExt.AlgebraicTopology.BGTCountableSwindleModels
