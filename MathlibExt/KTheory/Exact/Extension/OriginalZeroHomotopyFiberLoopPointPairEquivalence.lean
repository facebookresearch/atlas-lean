/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberLoopEquivalence
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoopPointPairEquivalence

/-!
# Original Q full-fiber and raw-loop singleton point pairs

The original localized-extension nerve and its actual zero/unit vertex
specialize the canonical full-fiber and raw-loop point-pair equivalence.
The original projection, selected point and both relative inverse laws remain.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory TopCat
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject Simplicial

universe u v

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The original selected singleton point pairs specialize the canonical
full-fiber and raw-loop equivalence with both relative inverse homotopies. -/
def zeroOriginalHomotopyFiberLoopPointPairEquiv :
    TopPair.HomotopyEquiv
      (TopPair.ofSubset
        (X := TopCat.homotopyFiber
          (SSet.toTop.map
            (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
          (zeroQVertex (C := C)))
        {TopCat.homotopyFiberSelectedPointMap
          (SSet.toTop.map
            (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
          (zeroTotalVertex (C := C)) (zeroQVertex (C := C))
          (zeroTotalVertex_map (C := C)) PUnit.unit})
      (TopPair.ofSubset
        (X := TopCat.of (LoopSpace
          (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v})) (zeroQVertex (C := C))))
        {Path.refl (zeroQVertex (C := C))}) := by
  let K : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  exact TopCat.realizedConullHomotopyFiberLoopPointPairEquiv K
    (show K _⦋0⦌ from ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)
    (SSet.toTop.map
      (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
    (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C))
    (originalLocalizedTotalTerminalWeak (C := C))

/-- The whole ambient forward morphism is the same original Q return. -/
theorem zeroOriginalHomotopyFiberLoopPointPairEquiv_hom_fst :
    TopPair.Hom.fst (zeroOriginalHomotopyFiberLoopPointPairEquiv (C := C)).hom =
      zeroOriginalHomotopyFiberToLoops (C := C) := by
  let K : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  let x : K _⦋0⦌ := ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val
  let B : TopCat.{max u v} := SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v})
  let p : SSet.toTop.obj K ⟶ B := SSet.toTop.map
    (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C)))
  let b : B := zeroQVertex (C := C)
  have he : p (SSet.realizedVertex x) = b := zeroTotalVertex_map (C := C)
  have hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)) :=
    originalLocalizedTotalTerminalWeak (C := C)
  let contraction := SSet.basedContractionAtRealizedVertex K x hK
  apply TopCat.hom_ext
  have hPair :
      (TopPair.Hom.fst (zeroOriginalHomotopyFiberLoopPointPairEquiv (C := C)).hom).hom =
        (TopCat.homotopyFiberLoopEquivOfBasedContraction
          p (SSet.realizedVertex x) b he contraction).toFun :=
    TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction_hom_fst
      p (SSet.realizedVertex x) b he contraction
  have hMaps :
      (TopCat.homotopyFiberToLoopsOfBasedContraction
        p (SSet.realizedVertex x) b he contraction).hom =
      (TopCat.homotopyFiberToLoopsOfRealizedConull K x p b he hK).hom := by
    apply ContinuousMap.ext
    intro z
    ext t
    exact (TopCat.homotopyFiberToLoopsOfBasedContraction_apply
      p (SSet.realizedVertex x) b he contraction z t).trans
        (TopCat.homotopyFiberToLoopsOfRealizedConull_apply K x p b he hK z t).symm
  have hOriginal :
      TopCat.homotopyFiberToLoopsOfRealizedConull K x p b he hK =
        zeroOriginalHomotopyFiberToLoops (C := C) :=
    (zeroOriginalHomotopyFiberToLoops_eq_realizedConull (C := C)).symm
  exact hPair.trans
    ((TopCat.homotopyFiberLoopEquivOfBasedContraction_toFun
      p (SSet.realizedVertex x) b he contraction).trans
        (hMaps.trans (congrArg TopCat.Hom.hom hOriginal)))

/-- The whole ambient inverse morphism is the original full selected-loop map. -/
theorem zeroOriginalHomotopyFiberLoopPointPairEquiv_inv_fst :
    TopPair.Hom.fst (zeroOriginalHomotopyFiberLoopPointPairEquiv (C := C)).inv =
      zeroLoopToOriginalHomotopyFiber (C := C) := by
  let K : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  let x : K _⦋0⦌ := ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val
  let B : TopCat.{max u v} := SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v})
  let p : SSet.toTop.obj K ⟶ B := SSet.toTop.map
    (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C)))
  let b : B := zeroQVertex (C := C)
  have he : p (SSet.realizedVertex x) = b := zeroTotalVertex_map (C := C)
  have hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)) :=
    originalLocalizedTotalTerminalWeak (C := C)
  let contraction := SSet.basedContractionAtRealizedVertex K x hK
  apply TopCat.hom_ext
  exact TopCat.homotopyFiberLoopPointPairEquivOfBasedContraction_inv_fst
    p (SSet.realizedVertex x) b he contraction

end AlgebraicKTheory.OriginalQZeroComparison

end
