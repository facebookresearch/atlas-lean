/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monad.AdjunctionBarRelativeResolutionComparison
public import MathlibExt.CategoryTheory.HomologicalComplex.FunctorRelativeResolutionComparison.Homology

/-!
# Homology comparisons from the adjunction Bar

Applying an additive functor to the free Bar comparisons gives homology maps in each degree where
the displayed homologies exist. Maps over the same augmentation induce the same homology map.
These maps preserve identity and composition, and comparisons with another split relative
resolution give homology isomorphisms. The counit augmentation and its degree-zero component are
retained.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
universe uC vC uD vD uE vE
namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasKernels D]
  {E : Type uE} [Category.{vE} E] [Preadditive E]
  {F : C ⥤ D} {U : D ⥤ C} [U.Additive]
  (T : D ⥤ E) [T.Additive]

/-- The T-image of the original D-valued Bar chain. -/
abbrev mappedFreeBarResolution (adj : F ⊣ U) (M : D) : ChainComplex E ℕ :=
  Functor.mappedResolution T (freeBarResolutionChain adj M)

/-- Apply T to the constructed original Bar comparison over the endpoint map. -/
def mappedFreeBarResolutionComparison (adj : F ⊣ U) (M Y : D) (P : ChainComplex D ℕ)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y) (σ : Functor.AugmentationSplit U P Y β)
    (f : M ⟶ Y) : mappedFreeBarResolution T adj M ⟶ Functor.mappedResolution T P :=
  (T.mapHomologicalComplex (ComplexShape.down ℕ)).map
    (freeBarResolutionComparison adj M Y P β σ f)

/-- The homology map is induced by the mapped original Bar comparison. -/
def freeBarResolutionComparisonHomologyMap (adj : F ⊣ U) (M Y : D) (P : ChainComplex D ℕ)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y) (σ : Functor.AugmentationSplit U P Y β)
    (f : M ⟶ Y) (n : ℕ) [(mappedFreeBarResolution T adj M).HasHomology n]
    [(Functor.mappedResolution T P).HasHomology n] :
    (mappedFreeBarResolution T adj M).homology n ⟶ (Functor.mappedResolution T P).homology n :=
  homologyMap (mappedFreeBarResolutionComparison T adj M Y P β σ f) n

omit [HasZeroObject C] in
/-- Any two original maps over the same counit augmentation induce equal mapped homology maps. -/
theorem freeBarResolution_mappedHomologyMap_independent (adj : F ⊣ U)
    (M Y : D) (P : ChainComplex D ℕ)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y) (σ : Functor.AugmentationSplit U P Y β)
    (f : M ⟶ Y) (g h : freeBarResolutionChain adj M ⟶ P)
    (hg : g ≫ β = freeBarResolutionAugmentation adj M ≫ (ChainComplex.single₀ D).map f)
    (hh : h ≫ β = freeBarResolutionAugmentation adj M ≫ (ChainComplex.single₀ D).map f)
    (n : ℕ) [(mappedFreeBarResolution T adj M).HasHomology n]
    [(Functor.mappedResolution T P).HasHomology n] :
    homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map g) n =
      homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map h) n :=
  (T.mapHomotopy
    (freeBarResolutionComparisonHomotopy adj M Y P β σ f g h hg hh)).homologyMap_eq n

omit [HasZeroObject C] in
/-- The computed Bar comparison agrees on homology with every original map over the endpoint. -/
theorem freeBarResolutionComparisonHomologyMap_eq_of_augmentation (adj : F ⊣ U)
    (M Y : D) (P : ChainComplex D ℕ)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y) (σ : Functor.AugmentationSplit U P Y β)
    (f : M ⟶ Y) (g : freeBarResolutionChain adj M ⟶ P)
    (hg : g ≫ β = freeBarResolutionAugmentation adj M ≫ (ChainComplex.single₀ D).map f)
    (n : ℕ) [(mappedFreeBarResolution T adj M).HasHomology n]
    [(Functor.mappedResolution T P).HasHomology n] :
    freeBarResolutionComparisonHomologyMap T adj M Y P β σ f n =
      homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map g) n :=
  freeBarResolution_mappedHomologyMap_independent T adj M Y P β σ f _ g
    (freeBarResolutionComparison_augmentation adj M Y P β σ f) hg n

omit [HasZeroObject C] in
/-- The literal original augmentations are retained after applying T to the Bar comparison. -/
theorem mappedFreeBarResolutionComparison_augmentation (adj : F ⊣ U)
    (M Y : D) (P : ChainComplex D ℕ)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y) (σ : Functor.AugmentationSplit U P Y β)
    (f : M ⟶ Y) :
    mappedFreeBarResolutionComparison T adj M Y P β σ f ≫
        (T.mapHomologicalComplex (ComplexShape.down ℕ)).map β =
      (T.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (freeBarResolutionAugmentation adj M) ≫
        (T.mapHomologicalComplex (ComplexShape.down ℕ)).map ((ChainComplex.single₀ D).map f) := by
  have h := congrArg ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map)
    (freeBarResolutionComparison_augmentation adj M Y P β σ f)
  dsimp only [mappedFreeBarResolutionComparison]
  simpa only [Functor.map_comp] using h

omit [HasZeroObject C] in
/-- The comparison square descends to homology wherever its displayed homologies exist. -/
theorem freeBarResolutionComparisonHomologyMap_augmentation (adj : F ⊣ U)
    (M Y : D) (P : ChainComplex D ℕ)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y) (σ : Functor.AugmentationSplit U P Y β)
    (f : M ⟶ Y) (n : ℕ) [(mappedFreeBarResolution T adj M).HasHomology n]
    [(Functor.mappedResolution T P).HasHomology n]
    [(Functor.mappedResolution T ((ChainComplex.single₀ D).obj M)).HasHomology n]
    [(Functor.mappedResolution T ((ChainComplex.single₀ D).obj Y)).HasHomology n] :
    freeBarResolutionComparisonHomologyMap T adj M Y P β σ f n ≫
        homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map β) n =
      homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (freeBarResolutionAugmentation adj M)) n ≫
        homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((ChainComplex.single₀ D).map f)) n := by
  have h := congrArg (fun z => homologyMap z n)
    (mappedFreeBarResolutionComparison_augmentation T adj M Y P β σ f)
  dsimp only [freeBarResolutionComparisonHomologyMap]
  simpa only [homologyMap_comp] using h

omit [Preadditive C] [HasZeroObject C] [HasKernels D] [U.Additive] in
/-- The degree-zero mapped augmentation is T applied to the literal original counit. -/
theorem mappedFreeBarResolutionAugmentation_zero (adj : F ⊣ U) (M : D) :
    ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (freeBarResolutionAugmentation adj M)).f 0 = T.map (adj.counit.app M) := by
  change T.map ((freeBarResolutionAugmentation adj M).f 0) = _
  rw [freeBarResolutionAugmentation_zero]
  rfl

/-- The Bar identity comparison induces the homology identity. -/
theorem freeBarResolutionComparisonHomologyMap_id (adj : F ⊣ U) (M : D) (n : ℕ)
    [(mappedFreeBarResolution T adj M).HasHomology n] :
    freeBarResolutionComparisonHomologyMap T adj M M (freeBarResolutionChain adj M)
      (freeBarResolutionAugmentation adj M) (freeBarResolutionSplit adj M) (𝟙 M) n = 𝟙 _ := by
  let : PreservesLimit (parallelPair ((freeBarResolutionAugmentation adj M).f 0) 0) U :=
    adj.freeBarResolution_preservesKernel ((freeBarResolutionAugmentation adj M).f 0)
  exact Functor.comparisonHomologyMap_id U T (freeBarResolutionChain adj M) M
    (freeBarResolutionAugmentation adj M) (freeBarResolutionSplit adj M)
    (freeBarResolution_term_relativeProjective adj M)
    (fun i => adj.freeBarResolution_preservesKernel ((freeBarResolutionChain adj M).d (i + 1) i)) n

/-- Endpoint composition agrees on homology with the two original Bar comparisons. -/
theorem freeBarResolutionComparisonHomologyMap_comp (adj : F ⊣ U)
    (M N Z : D) (f : M ⟶ N) (g : N ⟶ Z) (n : ℕ)
    [(mappedFreeBarResolution T adj M).HasHomology n]
    [(mappedFreeBarResolution T adj N).HasHomology n]
    [(mappedFreeBarResolution T adj Z).HasHomology n] :
    freeBarResolutionComparisonHomologyMap T adj M Z (freeBarResolutionChain adj Z)
        (freeBarResolutionAugmentation adj Z) (freeBarResolutionSplit adj Z) (f ≫ g) n =
      freeBarResolutionComparisonHomologyMap T adj M N (freeBarResolutionChain adj N)
          (freeBarResolutionAugmentation adj N) (freeBarResolutionSplit adj N) f n ≫
        freeBarResolutionComparisonHomologyMap T adj N Z (freeBarResolutionChain adj Z)
          (freeBarResolutionAugmentation adj Z) (freeBarResolutionSplit adj Z) g n := by
  let : PreservesLimit (parallelPair ((freeBarResolutionAugmentation adj N).f 0) 0) U :=
    adj.freeBarResolution_preservesKernel ((freeBarResolutionAugmentation adj N).f 0)
  let : PreservesLimit (parallelPair ((freeBarResolutionAugmentation adj Z).f 0) 0) U :=
    adj.freeBarResolution_preservesKernel ((freeBarResolutionAugmentation adj Z).f 0)
  exact Functor.comparisonHomologyMap_comp U T
    (freeBarResolutionChain adj M) (freeBarResolutionChain adj N) (freeBarResolutionChain adj Z)
    M N Z (freeBarResolutionAugmentation adj M) (freeBarResolutionAugmentation adj N)
    (freeBarResolutionAugmentation adj Z) (freeBarResolutionSplit adj N) (freeBarResolutionSplit adj Z)
    (freeBarResolution_term_relativeProjective adj M) (freeBarResolution_term_relativeProjective adj N)
    (fun i => adj.freeBarResolution_preservesKernel ((freeBarResolutionChain adj N).d (i + 1) i))
    (fun i => adj.freeBarResolution_preservesKernel ((freeBarResolutionChain adj Z).d (i + 1) i)) f g n

/-- Inverse comparisons identify mapped Bar homology with any split relative resolution. -/
def freeBarResolutionComparisonHomologyIso (adj : F ⊣ U) (M : D) (P : ChainComplex D ℕ)
    (β : P ⟶ (ChainComplex.single₀ D).obj M) (σ : Functor.AugmentationSplit U P M β)
    (hP : ∀ n, U.IsRelativeProjective (P.X n)) (n : ℕ)
    [(mappedFreeBarResolution T adj M).HasHomology n]
    [(Functor.mappedResolution T P).HasHomology n] :
    (mappedFreeBarResolution T adj M).homology n ≅ (Functor.mappedResolution T P).homology n := by
  let : PreservesLimit (parallelPair ((freeBarResolutionAugmentation adj M).f 0) 0) U :=
    adj.freeBarResolution_preservesKernel ((freeBarResolutionAugmentation adj M).f 0)
  let : PreservesLimit (parallelPair (β.f 0) 0) U := adj.freeBarResolution_preservesKernel (β.f 0)
  exact Functor.comparisonHomologyIso U T (freeBarResolutionChain adj M) P M
    (freeBarResolutionAugmentation adj M) β (freeBarResolutionSplit adj M) σ
    (freeBarResolution_term_relativeProjective adj M) hP
    (fun i => adj.freeBarResolution_preservesKernel ((freeBarResolutionChain adj M).d (i + 1) i))
    (fun i => adj.freeBarResolution_preservesKernel (P.d (i + 1) i)) n

/-- The constructed isomorphism has precisely the mapped original Bar identity comparison as its hom. -/
theorem freeBarResolutionComparisonHomologyIso_hom (adj : F ⊣ U) (M : D)
    (P : ChainComplex D ℕ) (β : P ⟶ (ChainComplex.single₀ D).obj M)
    (σ : Functor.AugmentationSplit U P M β) (hP : ∀ n, U.IsRelativeProjective (P.X n)) (n : ℕ)
    [(mappedFreeBarResolution T adj M).HasHomology n]
    [(Functor.mappedResolution T P).HasHomology n] :
    (freeBarResolutionComparisonHomologyIso T adj M P β σ hP n).hom =
      freeBarResolutionComparisonHomologyMap T adj M M P β σ (𝟙 M) n := rfl

end CategoryTheory.Adjunction
