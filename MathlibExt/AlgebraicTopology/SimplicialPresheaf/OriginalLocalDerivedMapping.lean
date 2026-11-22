/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalSmithModel
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalWhitehead
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveMappingSupport
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveDerivedMappingComparison

/-!
# Derived mapping spaces for localized simplicial presheaves

On a working-small, locally small site, a working-small family of localizing arrows determines
replacement functors from the chosen localization factors and a Kan mapping-space bifunctor.
Its two variances preserve local weak equivalences, and natural weak comparison spans relate
it to the baseline derived mapping spaces at the same local fibrant replacements.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
    HomotopicalAlgebra Opposite
open SimplicialPresheaf SimplicialPresheaf.InjectiveKan
open scoped SSet.modelCategoryQuillen
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory
namespace SimplicialPresheaf.OriginalLocalDerived
variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]
private def initialArrow : (SimplicialPresheaf.{u} D) ⥤ Arrow (SimplicialPresheaf.{u} D) where
  obj X := Arrow.mk (initial.to X)
  map f := Arrow.homMk (𝟙 _) f (by simp)
  map_id X := by apply Arrow.hom_ext <;> simp
  map_comp f g := by apply Arrow.hom_ext <;> simp

private def terminalArrow : (SimplicialPresheaf.{u} D) ⥤ Arrow (SimplicialPresheaf.{u} D) where
  obj X := Arrow.mk (terminal.from X)
  map f := Arrow.homMk f (𝟙 _) (by simp)
  map_id X := by apply Arrow.hom_ext <;> simp
  map_comp f g := by apply Arrow.hom_ext <;> simp

/-- Q is computed from the SAME original localization package's first stored native factors. -/
def localQ (S : I → Arrow (SimplicialPresheaf.{u} D)) : (SimplicialPresheaf.{u} D) ⥤
    (SimplicialPresheaf.{u} D) :=
  initialArrow ⋙ (originalLocalSmithData S).cofibrationFactorization.Z

/-- R uses the SAME package's actual Smith J and its stored native second factors. -/
def localR (S : I → Arrow (SimplicialPresheaf.{u} D)) : (SimplicialPresheaf.{u} D) ⥤
    (SimplicialPresheaf.{u} D) :=
  terminalArrow ⋙ (originalLocalSmithData S).trivialCofibrationFactorization.Z

/-- The original second leg of the first factorization is the natural Q counit. -/
def localQCounit (S : I → Arrow (SimplicialPresheaf.{u} D)) : localQ S ⟶
    𝟭 (SimplicialPresheaf.{u} D) :=
  Functor.whiskerLeft initialArrow (originalLocalSmithData S).cofibrationFactorization.p

/-- The actual first leg of the Smith factorization is the natural R unit. -/
def localRUnit (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    𝟭 (SimplicialPresheaf.{u} D) ⟶ localR S :=
  Functor.whiskerLeft terminalArrow (originalLocalSmithData S).trivialCofibrationFactorization.i

/-- Original objects, actual factor legs and both naturality squares use precisely those same
values. -/
theorem localReplacement_nativeFields (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (∀ X : (SimplicialPresheaf.{u} D),
      (localQ S).obj X =
        ((originalLocalSmithData S).cofibrationFactorization.factorizationData (initial.to X)).Z ∧
      (localQCounit S).app X =
        ((originalLocalSmithData S).cofibrationFactorization.factorizationData (initial.to X)).p) ∧
    (∀ X : (SimplicialPresheaf.{u} D),
      (localR S).obj X =
        ((originalLocalSmithData S).trivialCofibrationFactorization.factorizationData
            (terminal.from X)).Z ∧
      (localRUnit S).app X =
        ((originalLocalSmithData S).trivialCofibrationFactorization.factorizationData
            (terminal.from X)).i) ∧
    (∀ {X Y : (SimplicialPresheaf.{u} D)} (f : X ⟶ Y),
      (localQ S).map f ≫ (localQCounit S).app Y = (localQCounit S).app X ≫ f ∧
      f ≫ (localRUnit S).app Y = (localRUnit S).app X ≫ (localR S).map f) := by
  refine ⟨fun X => ⟨rfl, rfl⟩, fun X => ⟨rfl, rfl⟩, ?_⟩
  intro X Y f
  exact ⟨(localQCounit S).naturality f, (localRUnit S).naturality f⟩

/-- The Q counit belongs to the original baseline trivial fibrations, with no fibrant-target
premise. -/
theorem localQCounit_baseTrivialFibration (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X : (SimplicialPresheaf.{u} D)) :
    trivialFibrations (SimplicialPresheaf.{u} D) ((localQCounit S).app X) := by
  rw [(data D).trivialFibrations_eq]
  exact (originalLocalSmithData S).cofibrationFactorization.hp (Arrow.mk (initial.to X))

/-- The R unit is the original monic local weak first leg of the same Smith construction. -/
theorem localRUnit_localTrivialCofibration (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X : (SimplicialPresheaf.{u} D)) :
    localTrivialMonomorphisms S ((localRUnit S).app X) :=
  (originalLocalSmithData S).trivialCofibrationFactorization.hi (Arrow.mk (terminal.from X))

/-- The actual global second-factor RLP makes every chosen R object original local fibrant. -/
theorem localR_isOriginalLocalFibrant (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X : (SimplicialPresheaf.{u} D)) :
    isOriginalLocalFibrant S ((localR S).obj X) := by
  let q := originalLocalSmithData S
  let p : (localR S).obj X ⟶ ⊤_ (SimplicialPresheaf.{u} D) :=
    q.trivialCofibrationFactorization.p.app (Arrow.mk (terminal.from X))
  have hp : (localTrivialMonomorphisms S).rlp p :=
    q.trivialCofibrationFactorization.hp (Arrow.mk (terminal.from X))
  apply (q.terminal_iff ((localR S).obj X)).mp
  have h : p = terminal.from ((localR S).obj X) := Subsingleton.elim _ _
  rwa [← h]

/-- The weak Q counit's original naturality square transports every localized weak source map. -/
theorem localQ_map_localWeak (S : I → Arrow (SimplicialPresheaf.{u} D))
    {X Y : (SimplicialPresheaf.{u} D)} (f : X ⟶ Y)
    (hf : originalLocalEquivalences S f) :
    originalLocalEquivalences S ((localQ S).map f) := by
  let : (originalLocalEquivalences S).HasTwoOutOfThreeProperty :=
    originalLocalEquivalences_hasTwoOutOfThreeProperty S
  have hX := weakEquivalences_le_originalLocalEquivalences S
    ((localQCounit S).app X) (localQCounit_baseTrivialFibration S X).2
  have hY := weakEquivalences_le_originalLocalEquivalences S
    ((localQCounit S).app Y) (localQCounit_baseTrivialFibration S Y).2
  apply (originalLocalEquivalences S).of_postcomp _ _ hY
  rw [((localReplacement_nativeFields S).2.2 f).1]
  exact (originalLocalEquivalences S).comp_mem _ _ hX hf

/-- The actual locally weak R unit gives preservation on the same original target map. -/
theorem localR_map_localWeak (S : I → Arrow (SimplicialPresheaf.{u} D))
    {X Y : (SimplicialPresheaf.{u} D)} (f : X ⟶ Y)
    (hf : originalLocalEquivalences S f) :
    originalLocalEquivalences S ((localR S).map f) := by
  let : (originalLocalEquivalences S).HasTwoOutOfThreeProperty :=
    originalLocalEquivalences_hasTwoOutOfThreeProperty S
  apply (originalLocalEquivalences S).of_precomp _ _
    (localRUnit_localTrivialCofibration S X).2
  rw [← ((localReplacement_nativeFields S).2.2 f).2]
  exact (originalLocalEquivalences S).comp_mem _ _ hf
    (localRUnit_localTrivialCofibration S Y).2

/-- The true end uses the SAME internally constructed Q and R from the original S model. -/
def localDerivedEnd (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (SimplicialPresheaf.{u} D)ᵒᵖ ⥤ (SimplicialPresheaf.{u} D) ⥤ SSet.{u} :=
  (localQ S).op ⋙ innerHomFunctor ⋙
    (CategoryTheory.Functor.whiskeringLeft (SimplicialPresheaf.{u} D)
        (SimplicialPresheaf.{u} D) SSet.{u}).obj (localR S)

/-- The original source arrow acts by the actual Q map and contravariant end action. -/
def localDerivedPrecomp (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B : (SimplicialPresheaf.{u} D)} (f : A ⟶ B) (Y : (SimplicialPresheaf.{u} D)) :
    ((localDerivedEnd S).obj (op B)).obj Y ⟶ ((localDerivedEnd S).obj (op A)).obj Y :=
  ((localDerivedEnd S).map f.op).app Y

/-- Target action is the end's actual covariant action on the same R map. -/
def localDerivedPostcomp (S : I → Arrow (SimplicialPresheaf.{u} D))
    (A : (SimplicialPresheaf.{u} D)) {X Y : (SimplicialPresheaf.{u} D)} (g : X ⟶ Y) :
    ((localDerivedEnd S).obj (op A)).obj X ⟶ ((localDerivedEnd S).obj (op A)).obj Y :=
  ((localDerivedEnd S).obj (op A)).map g

/-- Original global RLP, followed by baseline SM7, makes this end Kan at every pair of objects. -/
theorem localDerivedEnd_isKan (S : I → Arrow (SimplicialPresheaf.{u} D))
    (A Y : (SimplicialPresheaf.{u} D)) :
    SSet.KanComplex (((localDerivedEnd S).obj (op A)).obj Y) := by
  change IsFibrant (innerHom ((localQ S).obj A) ((localR S).obj Y))
  exact (rawMappingInvariance D).2.2.2.2.1 _ _ (localR_isOriginalLocalFibrant S Y).1

/-- Contravariance uses the original all-local-target weak test, applied to the genuine chosen R
target. -/
theorem localDerivedPrecomp_localWeak (S : I →
    Arrow (SimplicialPresheaf.{u} D)) {A B : (SimplicialPresheaf.{u} D)}
    (f : A ⟶ B) (hf : originalLocalEquivalences S f) (Y : (SimplicialPresheaf.{u} D)) :
    SSet.realizationWeakEquivalences (localDerivedPrecomp S f Y) := by
  change SSet.realizationWeakEquivalences
    (innerHomPre ((localQ S).map f) ((localR S).obj Y))
  exact localQ_map_localWeak S f hf _ (localR_isOriginalLocalFibrant S Y)

/-- Local Whitehead at BOTH actual R endpoints and baseline Brown give covariance on every local
weak map. -/
theorem localDerivedPostcomp_localWeak (S : I → Arrow (SimplicialPresheaf.{u} D))
    (A : (SimplicialPresheaf.{u} D)) {X Y : (SimplicialPresheaf.{u} D)}
    (g : X ⟶ Y) (hg : originalLocalEquivalences S g) :
    SSet.realizationWeakEquivalences (localDerivedPostcomp S A g) := by
  have hX := localR_isOriginalLocalFibrant S X
  have hY := localR_isOriginalLocalFibrant S Y
  have hbase : weakEquivalences (SimplicialPresheaf.{u} D) ((localR S).map g) :=
    (originalLocalEquivalence_iff_weakEquivalence_of_localFibrant S
      ((localR S).map g) hX hY).mp (localR_map_localWeak S g hg)
  change SSet.realizationWeakEquivalences
    (innerHomPost ((localQ S).obj A) ((localR S).map g))
  exact (rawMappingInvariance D).2.2.2.2.2.2 _ _ hbase hX.1 hY.1

/-- Identities, both composition orders, exchange and every inner operator use the true same-Q/R
bifunctor. -/
theorem localDerivedEnd_laws (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (∀ A Y : (SimplicialPresheaf.{u} D), localDerivedPrecomp S (𝟙 A) Y = 𝟙 _) ∧
    (∀ {A B E : (SimplicialPresheaf.{u} D)} (f : A ⟶ B) (g : B ⟶ E)
        (Y : (SimplicialPresheaf.{u} D)),
      localDerivedPrecomp S (f ≫ g) Y = localDerivedPrecomp S g Y ≫ localDerivedPrecomp S f Y) ∧
    (∀ A Y : (SimplicialPresheaf.{u} D), localDerivedPostcomp S A (𝟙 Y) = 𝟙 _) ∧
    (∀ (A : (SimplicialPresheaf.{u} D)) {X Y Z : (SimplicialPresheaf.{u} D)} (f : X ⟶ Y)
        (g : Y ⟶ Z),
      localDerivedPostcomp S A (f ≫ g) = localDerivedPostcomp S A f ≫ localDerivedPostcomp S A g) ∧
    (∀ {A B X Y : (SimplicialPresheaf.{u} D)} (f : A ⟶ B) (g : X ⟶ Y),
      localDerivedPrecomp S f X ≫ localDerivedPostcomp S A g =
        localDerivedPostcomp S B g ≫ localDerivedPrecomp S f Y) ∧
    (∀ {A B : (SimplicialPresheaf.{u} D)} (f : A ⟶ B)
        (Y : (SimplicialPresheaf.{u} D)) {n m : SimplexCategoryᵒᵖ} (theta : n ⟶ m),
      (((localDerivedEnd S).obj (op B)).obj Y).map theta ≫
        (localDerivedPrecomp S f Y).app m =
      (localDerivedPrecomp S f Y).app n ≫ (((localDerivedEnd S).obj (op A)).obj Y).map theta) ∧
    (∀ (A : (SimplicialPresheaf.{u} D)) {X Y : (SimplicialPresheaf.{u} D)}
        (g : X ⟶ Y) {n m : SimplexCategoryᵒᵖ} (theta : n ⟶ m),
      (((localDerivedEnd S).obj (op A)).obj X).map theta ≫
        (localDerivedPostcomp S A g).app m =
      (localDerivedPostcomp S A g).app n ≫ (((localDerivedEnd S).obj (op A)).obj Y).map theta) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A Y
    simp [localDerivedPrecomp]
  · intro A B E f g Y
    simp [localDerivedPrecomp, Functor.map_comp]
  · intro A Y
    exact ((localDerivedEnd S).obj (op A)).map_id Y
  · intro A X Y Z f g
    exact ((localDerivedEnd S).obj (op A)).map_comp f g
  · intro A B X Y f g
    exact (((localDerivedEnd S).map f.op).naturality g).symm
  · intro A B f Y n m theta
    exact (localDerivedPrecomp S f Y).naturality theta
  · intro A X Y g n m theta
    exact (localDerivedPostcomp S A g).naturality theta

/-- The common original raw end first uses precisely the stored localized R. -/
def rawAfterR (S : I → Arrow (SimplicialPresheaf.{u} D)) : (SimplicialPresheaf.{u} D)ᵒᵖ ⥤
    (SimplicialPresheaf.{u} D) ⥤ SSet.{u} :=
  innerHomFunctor ⋙
      (CategoryTheory.Functor.whiskeringLeft (SimplicialPresheaf.{u} D)
        (SimplicialPresheaf.{u} D) SSet.{u}).obj (localR S)

/-- The other span endpoint is the genuine baseline chosen-derived functor at that SAME R target. -/
def baselineAfterR (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (SimplicialPresheaf.{u} D)ᵒᵖ ⥤ (SimplicialPresheaf.{u} D) ⥤ SSet.{u} :=
  originalDerivedMappingObject D ⋙
    (CategoryTheory.Functor.whiskeringLeft (SimplicialPresheaf.{u} D)
        (SimplicialPresheaf.{u} D) SSet.{u}).obj (localR S)

/-- Precomposition by the original weak Q counit is the first natural weak span map. -/
def localEndSpan (S : I → Arrow (SimplicialPresheaf.{u} D)) : rawAfterR S ⟶ localDerivedEnd S :=
  Functor.whiskerRight (Functor.whiskerRight (NatTrans.op (localQCounit S)) innerHomFunctor)
    ((CategoryTheory.Functor.whiskeringLeft (SimplicialPresheaf.{u} D)
        (SimplicialPresheaf.{u} D) SSet.{u}).obj (localR S))

/-- The existing baseline comparison at R supplies the second actual natural weak span map. -/
def baselineEndSpan (S : I → Arrow (SimplicialPresheaf.{u} D)) : rawAfterR S ⟶ baselineAfterR S :=
  Functor.whiskerRight (originalMappingComparison D)
    ((CategoryTheory.Functor.whiskeringLeft (SimplicialPresheaf.{u} D)
        (SimplicialPresheaf.{u} D) SSet.{u}).obj (localR S))

/-- Both characteristic maps and all source/target/inner operators are the original span
naturalities. -/
theorem localEndSpans_laws (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (∀ X Y : (SimplicialPresheaf.{u} D), ((localEndSpan S).app (op X)).app Y =
      innerHomPre ((localQCounit S).app X) ((localR S).obj Y)) ∧
    (∀ X Y : (SimplicialPresheaf.{u} D), ((baselineEndSpan S).app (op X)).app Y =
      ((originalMappingComparison D).app (op X)).app ((localR S).obj Y)) ∧
    (∀ {A B : (SimplicialPresheaf.{u} D)} (f : A ⟶ B) (Y : (SimplicialPresheaf.{u} D)),
      ((rawAfterR S).map f.op).app Y ≫ ((localEndSpan S).app (op A)).app Y =
        ((localEndSpan S).app (op B)).app Y ≫ localDerivedPrecomp S f Y) ∧
    (∀ {A B : (SimplicialPresheaf.{u} D)} (f : A ⟶ B) (Y : (SimplicialPresheaf.{u} D)),
      ((rawAfterR S).map f.op).app Y ≫ ((baselineEndSpan S).app (op A)).app Y =
        ((baselineEndSpan S).app (op B)).app Y ≫ ((baselineAfterR S).map f.op).app Y) ∧
    (∀ (A : (SimplicialPresheaf.{u} D)) {X Y : (SimplicialPresheaf.{u} D)} (g : X ⟶ Y),
      ((rawAfterR S).obj (op A)).map g ≫ ((localEndSpan S).app (op A)).app Y =
        ((localEndSpan S).app (op A)).app X ≫ localDerivedPostcomp S A g) ∧
    (∀ (A : (SimplicialPresheaf.{u} D)) {X Y : (SimplicialPresheaf.{u} D)} (g : X ⟶ Y),
      ((rawAfterR S).obj (op A)).map g ≫ ((baselineEndSpan S).app (op A)).app Y =
        ((baselineEndSpan S).app (op A)).app X ≫ ((baselineAfterR S).obj (op A)).map g) ∧
    (∀ X Y : (SimplicialPresheaf.{u} D), ∀ {n m : SimplexCategoryᵒᵖ} (theta : n ⟶ m),
      (((rawAfterR S).obj (op X)).obj Y).map theta ≫
        (((localEndSpan S).app (op X)).app Y).app m =
      (((localEndSpan S).app (op X)).app Y).app n ≫
        (((localDerivedEnd S).obj (op X)).obj Y).map theta) ∧
    (∀ X Y : (SimplicialPresheaf.{u} D), ∀ {n m : SimplexCategoryᵒᵖ} (theta : n ⟶ m),
      (((rawAfterR S).obj (op X)).obj Y).map theta ≫
        (((baselineEndSpan S).app (op X)).app Y).app m =
      (((baselineEndSpan S).app (op X)).app Y).app n ≫
        (((baselineAfterR S).obj (op X)).obj Y).map theta) := by
  refine ⟨fun X Y => rfl, fun X Y => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B f Y
    exact NatTrans.congr_app ((localEndSpan S).naturality f.op) Y
  · intro A B f Y
    exact NatTrans.congr_app ((baselineEndSpan S).naturality f.op) Y
  · intro A X Y g
    exact ((localEndSpan S).app (op A)).naturality g
  · intro A X Y g
    exact ((baselineEndSpan S).app (op A)).naturality g
  · intro X Y n m theta
    exact (((localEndSpan S).app (op X)).app Y).naturality theta
  · intro X Y n m theta
    exact (((baselineEndSpan S).app (op X)).app Y).naturality theta

/-- At EVERY original source and target both actual span maps are weak, by the genuine R
fibrancy. -/
theorem localEndSpans_weak (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X Y : (SimplicialPresheaf.{u} D)) :
    SSet.realizationWeakEquivalences (((localEndSpan S).app (op X)).app Y) ∧
    SSet.realizationWeakEquivalences (((baselineEndSpan S).app (op X)).app Y) := by
  have hR := (localR_isOriginalLocalFibrant S Y).1
  exact ⟨(rawMappingInvariance D).2.2.2.2.2.1 ((localQCounit S).app X)
      ((localR S).obj Y) (localQCounit_baseTrivialFibration S X).2 hR,
    ((originalChosenDerivedMappingComparison D).2.2.2.2.1 X ((localR S).obj Y) hR).2.2⟩

end SimplicialPresheaf.OriginalLocalDerived
