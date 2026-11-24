/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.HomologicalComplex.FunctorRelativeResolutionComparison.Coherence
public import MathlibExt.CategoryTheory.Monad.AdjunctionBarRelativeResolution
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Comparison maps from the adjunction Bar

The restricted Bar contraction gives augmentation-splitting data for the free Bar complex. Its
terms are relatively projective, and right-adjoint kernel preservation supplies the comparison
hypotheses. Every coefficient morphism lifts to a comparison into a split relative resolution, and
any two comparisons over that morphism are chain homotopic.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
universe uC vC uD vD
namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasKernels D]
  {F : C ⥤ D} {U : D ⥤ C} [U.Additive]

/-- The original D-valued alternating Bar complex. -/
abbrev freeBarResolutionChain (adj : F ⊣ U) (M : D) : ChainComplex D ℕ :=
  (alternatingFaceMapComplex D).obj (adj.freeBar M)

/-- The D-valued augmentation, with the original counit at degree zero. -/
def freeBarResolutionAugmentation (adj : F ⊣ U) (M : D) :
    freeBarResolutionChain adj M ⟶ (ChainComplex.single₀ D).obj M :=
  AlternatingFaceMapComplex.ε.app (adj.freeBarAugmented M)

omit [Preadditive C] [HasZeroObject C] [HasKernels D] [U.Additive] in
/-- Degree zero of this original augmentation is precisely the original counit. -/
theorem freeBarResolutionAugmentation_zero (adj : F ⊣ U) (M : D) :
    (adj.freeBarResolutionAugmentation M).f 0 = adj.counit.app M := by
  rw [freeBarResolutionAugmentation, AlternatingFaceMapComplex.ε_app_f_zero,
    freeBarAugmented_hom_zero]

/-- The already-constructed positive extra operator on the mapped original chain terms. -/
abbrev freeBarResolutionSplitOperator (adj : F ⊣ U) (M : D) (n : ℕ) :
    U.obj ((freeBarResolutionChain adj M).X n) ⟶
      U.obj ((freeBarResolutionChain adj M).X (n + 1)) :=
  adj.restrictedFreeBarSplitOperator M n

omit [HasZeroObject C] [HasZeroObject D] [HasKernels D] in
/-- Additive whiskering's identity components preserve the original differential exactly. -/
theorem freeBarResolution_mapped_d (adj : F ⊣ U) (M : D) (n : ℕ) :
    U.map ((freeBarResolutionChain adj M).d (n + 1) n) =
      (restrictedFreeBarChain adj M).d (n + 1) n := by
  have h := (adj.restrictedFreeBarChainIso M).hom.comm (n + 1) n
  rw [restrictedFreeBarChainIso_hom_f, restrictedFreeBarChainIso_hom_f] at h
  change (𝟙 _) ≫ (restrictedFreeBarChain adj M).d (n + 1) n =
    U.map ((freeBarResolutionChain adj M).d (n + 1) n) ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h.symm

/-- The restricted Bar contraction gives original-chain augmentation split data. -/
def freeBarResolutionSplit (adj : F ⊣ U) (M : D) :
    Functor.AugmentationSplit U (freeBarResolutionChain adj M) M
      (freeBarResolutionAugmentation adj M) where
  section_ := adj.unit.app (U.obj M)
  s := freeBarResolutionSplitOperator adj M
  section_comp := by
    rw [freeBarResolutionAugmentation_zero]
    exact adj.right_triangle_components M
  zero := by
    rw [freeBarResolutionAugmentation_zero, freeBarResolution_mapped_d]
    exact adj.restrictedFreeBar_split_zero M
  succ n := by
    rw [freeBarResolution_mapped_d, freeBarResolution_mapped_d]
    exact adj.restrictedFreeBar_split_succ M n

omit [Preadditive C] [HasZeroObject C] [HasZeroObject D] [HasKernels D] [U.Additive] in
/-- Every original Bar chain term has the canonical relative projective property. -/
theorem freeBarResolution_term_relativeProjective (adj : F ⊣ U) (M : D) (n : ℕ) :
    U.IsRelativeProjective ((freeBarResolutionChain adj M).X n) :=
  adj.freeBar_isRelativeProjective M n

omit [Preadditive C] [HasZeroObject C] [HasZeroObject D] [HasKernels D] [U.Additive] in
/-- Right-adjoint structure preserves the displayed original kernel, with no input universal property. -/
theorem freeBarResolution_preservesKernel (adj : F ⊣ U) {A B : D} (g : A ⟶ B) :
    PreservesLimit (parallelPair g 0) U := by
  let : U.IsRightAdjoint := adj.isRightAdjoint
  infer_instance

/-- The Bar lifts an original endpoint map into any target split augmentation. -/
def freeBarResolutionComparison (adj : F ⊣ U) (M Y : D) (P : ChainComplex D ℕ)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y) (σ : Functor.AugmentationSplit U P Y β)
    (f : M ⟶ Y) : freeBarResolutionChain adj M ⟶ P := by
  let : PreservesLimit (parallelPair (β.f 0) 0) U := adj.freeBarResolution_preservesKernel (β.f 0)
  exact Functor.comparison U (freeBarResolutionChain adj M) P M Y
    (freeBarResolutionAugmentation adj M) β σ (freeBarResolution_term_relativeProjective adj M)
    (fun n => adj.freeBarResolution_preservesKernel (P.d (n + 1) n)) f

omit [HasZeroObject C] in
/-- The Bar comparison retains both original augmentations and the original endpoint map. -/
@[reassoc]
theorem freeBarResolutionComparison_augmentation (adj : F ⊣ U) (M Y : D) (P : ChainComplex D ℕ)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y) (σ : Functor.AugmentationSplit U P Y β)
    (f : M ⟶ Y) :
    freeBarResolutionComparison adj M Y P β σ f ≫ β =
      freeBarResolutionAugmentation adj M ≫ (ChainComplex.single₀ D).map f := by
  let : PreservesLimit (parallelPair (β.f 0) 0) U := adj.freeBarResolution_preservesKernel (β.f 0)
  exact Functor.comparison_augmentation U (freeBarResolutionChain adj M) P M Y
    (freeBarResolutionAugmentation adj M) β σ (freeBarResolution_term_relativeProjective adj M)
    (fun n => adj.freeBarResolution_preservesKernel (P.d (n + 1) n)) f

/-- Every two original Bar comparisons over the same endpoint map have a constructed homotopy. -/
def freeBarResolutionComparisonHomotopy (adj : F ⊣ U) (M Y : D) (P : ChainComplex D ℕ)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y) (σ : Functor.AugmentationSplit U P Y β)
    (f : M ⟶ Y) (g h : freeBarResolutionChain adj M ⟶ P)
    (hg : g ≫ β = freeBarResolutionAugmentation adj M ≫ (ChainComplex.single₀ D).map f)
    (hh : h ≫ β = freeBarResolutionAugmentation adj M ≫ (ChainComplex.single₀ D).map f) :
    Homotopy g h := by
  let : PreservesLimit (parallelPair (β.f 0) 0) U := adj.freeBarResolution_preservesKernel (β.f 0)
  exact Functor.comparisonHomotopy U (freeBarResolutionChain adj M) P M Y
    (freeBarResolutionAugmentation adj M) β σ (freeBarResolution_term_relativeProjective adj M)
    (fun n => adj.freeBarResolution_preservesKernel (P.d (n + 1) n)) f g h hg hh

end CategoryTheory.Adjunction
