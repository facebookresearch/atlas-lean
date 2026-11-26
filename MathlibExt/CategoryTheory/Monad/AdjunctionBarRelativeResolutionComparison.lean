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
# Relative comparisons from an adjunction bar complex

Let `C,D` be preadditive with zero objects, `D` have kernels, and
`F : C → D` be left adjoint to additive `U : D → C`.
The alternating-face bar chain complex of `F ∘ U` is augmented by
the counit and becomes contractingly split after `U`. Its terms are
`U`-relative-projective, and the right adjoint preserves the displayed
kernels. Any map `M → Y` therefore lifts from the bar of `M` into a
`U`-split augmented complex over `Y`; all such lifts are chain homotopic.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
universe uC vC uD vD
namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasKernels D]
  {F : C ⥤ D} {U : D ⥤ C} [U.Additive]

/-- Let `C,D` be preadditive with zero objects, let `D` have kernels,
and let `F : C → D` be left adjoint to additive `U : D → C`. The free bar is the nonnegative alternating-face chain
complex in `D` of the adjunction comonad, with degree-`n` object
`(F ∘ U)^(n+1)(M)`. -/
abbrev freeBarResolutionChain (adj : F ⊣ U) (M : D) : ChainComplex D ℕ :=
  (alternatingFaceMapComplex D).obj (adj.freeBar M)

/-- Let `C,D` be preadditive with zero objects, let `D` have kernels,
and let `F : C → D` be left adjoint to additive `U : D → C`. The counit gives the chain augmentation
`Bar(M) → M[0]` of the free bar complex. -/
def freeBarResolutionAugmentation (adj : F ⊣ U) (M : D) :
    freeBarResolutionChain adj M ⟶ (ChainComplex.single₀ D).obj M :=
  AlternatingFaceMapComplex.ε.app (adj.freeBarAugmented M)

omit [Preadditive C] [HasZeroObject C] [HasKernels D] [U.Additive] in
/-- Let `C,D` be preadditive with zero objects, let `D` have kernels,
and let `F : C → D` be left adjoint to additive `U : D → C`. The degree-zero component of `Bar(M) → M[0]` is the
counit `F(U(M)) → M`. -/
theorem freeBarResolutionAugmentation_zero (adj : F ⊣ U) (M : D) :
    (adj.freeBarResolutionAugmentation M).f 0 = adj.counit.app M := by
  rw [freeBarResolutionAugmentation, AlternatingFaceMapComplex.ε_app_f_zero,
    freeBarAugmented_hom_zero]

/-- Let `C,D` be preadditive with zero objects, let `D` have kernels,
and let `F : C → D` be left adjoint to additive `U : D → C`. The restricted extra-degeneracy gives operators
`U(Bar_n(M)) → U(Bar_(n+1)(M))` for the contracting splitting
of the augmented restricted bar complex. -/
abbrev freeBarResolutionSplitOperator (adj : F ⊣ U) (M : D) (n : ℕ) :
    U.obj ((freeBarResolutionChain adj M).X n) ⟶
      U.obj ((freeBarResolutionChain adj M).X (n + 1)) :=
  adj.restrictedFreeBarSplitOperator M n

omit [HasZeroObject C] [HasZeroObject D] [HasKernels D] in
/-- Let `C,D` be preadditive with zero objects, let `D` have kernels,
and let `F : C → D` be left adjoint to additive `U : D → C`. Applying `U` to the degree-`n+1` to degree-`n` differential
of the `D`-valued bar gives exactly the differential of its
restricted alternating-face chain complex in `C`. -/
theorem freeBarResolution_mapped_d (adj : F ⊣ U) (M : D) (n : ℕ) :
    U.map ((freeBarResolutionChain adj M).d (n + 1) n) =
      (restrictedFreeBarChain adj M).d (n + 1) n := by
  have h := (adj.restrictedFreeBarChainIso M).hom.comm (n + 1) n
  rw [restrictedFreeBarChainIso_hom_f, restrictedFreeBarChainIso_hom_f] at h
  change (𝟙 _) ≫ (restrictedFreeBarChain adj M).d (n + 1) n =
    U.map ((freeBarResolutionChain adj M).d (n + 1) n) ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h.symm

/-- Let `C,D` be preadditive with zero objects, let `D` have kernels,
and let `F : C → D` be left adjoint to additive `U : D → C`. The adjunction unit and restricted extra-degeneracy operators
give a contracting splitting of the augmentation `U(Bar(M)) → U(M)[0]`. -/
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
/-- Let `C,D` be preadditive with zero objects, let `D` have kernels,
and let `F : C → D` be left adjoint to additive `U : D → C`. Every chain term of `Bar(M)` is `U`-relative-projective,
since each is in the image of the left adjoint `F`. -/
theorem freeBarResolution_term_relativeProjective (adj : F ⊣ U) (M : D) (n : ℕ) :
    U.IsRelativeProjective ((freeBarResolutionChain adj M).X n) :=
  adj.freeBar_isRelativeProjective M n

omit [Preadditive C] [HasZeroObject C] [HasZeroObject D] [HasKernels D] [U.Additive] in
/-- Let `C,D` be preadditive with zero objects, let `D` have kernels,
and let `F : C → D` be left adjoint to additive `U : D → C`. The right adjoint `U` preserves the kernel of every map
`g : A → B` in `D`, equivalently the limit of the parallel pair
`g,0`. -/
theorem freeBarResolution_preservesKernel (adj : F ⊣ U) {A B : D} (g : A ⟶ B) :
    PreservesLimit (parallelPair g 0) U := by
  let : U.IsRightAdjoint := adj.isRightAdjoint
  infer_instance

/-- Let `C,D` be preadditive with zero objects, let `D` have kernels,
and let `F : C → D` be left adjoint to additive `U : D → C`. For an augmentation `P → Y[0]` contractingly split after
`U` and `f : M → Y`, there is a comparison chain map `Bar(M) → P`
lifting `f`. -/
def freeBarResolutionComparison (adj : F ⊣ U) (M Y : D) (P : ChainComplex D ℕ)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y) (σ : Functor.AugmentationSplit U P Y β)
    (f : M ⟶ Y) : freeBarResolutionChain adj M ⟶ P := by
  let : PreservesLimit (parallelPair (β.f 0) 0) U := adj.freeBarResolution_preservesKernel (β.f 0)
  exact Functor.comparison U (freeBarResolutionChain adj M) P M Y
    (freeBarResolutionAugmentation adj M) β σ (freeBarResolution_term_relativeProjective adj M)
    (fun n => adj.freeBarResolution_preservesKernel (P.d (n + 1) n)) f

omit [HasZeroObject C] in
/-- Let `C,D` be preadditive with zero objects, let `D` have kernels,
and let `F : C → D` be left adjoint to additive `U : D → C`. For a `U`-split augmentation `β : P → Y[0]` and `f : M → Y`,
the comparison satisfies `comparison_f ≫ β = ε_M ≫ f[0]`
for the full bar counit augmentation `ε_M`. -/
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

/-- Let `C,D` be preadditive with zero objects, let `D` have kernels,
and let `F : C → D` be left adjoint to additive `U : D → C`. For a `U`-split augmentation `P → Y[0]`, any two chain maps
`Bar(M) → P` over the same `f : M → Y` are chain homotopic. -/
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
