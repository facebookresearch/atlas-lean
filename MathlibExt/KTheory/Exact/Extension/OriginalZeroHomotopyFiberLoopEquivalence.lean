/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoopsRealizedConull
public import MathlibExt.KTheory.Exact.Extension.OriginalZeroLoopHomotopyFiber
public import MathlibExt.Topology.Homotopy.Contractible
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# The original zero/unit homotopy fiber and its full loop space

The total space and projection are the original localized extension category
and localized target. The original completed-unit vertex maps to the actual
Q zero vertex. The derived based contraction identifies the entire compact-open
homotopy fiber with the existing loop space, with its exact full selected-loop
map as inverse. The ring specialization keeps all components and both universes.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject Simplicial

universe u v uRing vModule

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction


/-- The actual original zero/unit fiber is equivalent to the full Q loop space. -/
def zeroOriginalHomotopyFiberLoopEquiv :
    ContinuousMap.HomotopyEquiv
      (TopCat.homotopyFiber
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (zeroQVertex (C := C)))
      (LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v}))
        (zeroQVertex (C := C))) := by
  let K : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  have hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)) :=
    originalLocalizedTotalTerminalWeak (C := C)
  exact TopCat.realizedConullHomotopyFiberLoopEquiv K
    (show K _⦋0⦌ from ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)
    (SSet.toTop.map
      (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
    (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C)) hK

/-- The inverse remains exactly the previous full selected-loop map at the original unit. -/
theorem zeroOriginalHomotopyFiberLoopEquiv_invFun :
    (zeroOriginalHomotopyFiberLoopEquiv (C := C)).invFun =
      (zeroLoopToOriginalHomotopyFiber (C := C)).hom := by
  let K : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  have hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)) :=
    originalLocalizedTotalTerminalWeak (C := C)
  exact TopCat.realizedConullHomotopyFiberLoopEquiv_invFun K
    (show K _⦋0⦌ from ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)
    (SSet.toTop.map
      (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
    (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C)) hK

/-- The forward map is the genuine full-path return into the existing Q loop space. -/
def zeroOriginalHomotopyFiberToLoops :
    TopCat.homotopyFiber
      (SSet.toTop.map
        (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
      (zeroQVertex (C := C)) ⟶
        TopCat.of (LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v}))
          (zeroQVertex (C := C))) :=
  TopCat.ofHom (zeroOriginalHomotopyFiberLoopEquiv (C := C)).toFun


/-- The public forward-map characteristic retains the original return map
without exposing the private actual inverse-homotopy families. -/
theorem zeroOriginalHomotopyFiberLoopEquiv_toFun :
    (zeroOriginalHomotopyFiberLoopEquiv (C := C)).toFun =
      (zeroOriginalHomotopyFiberToLoops (C := C)).hom := (rfl)

/-- The original return is the actual realized-conull return as a whole map.
This characteristic is usable without exposing the ordinary equivalence. -/
theorem zeroOriginalHomotopyFiberToLoops_eq_realizedConull :
    zeroOriginalHomotopyFiberToLoops (C := C) =
      TopCat.homotopyFiberToLoopsOfRealizedConull
        (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v})
        (ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C))
        (originalLocalizedTotalTerminalWeak (C := C)) := by
  let K : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  have hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)) :=
    originalLocalizedTotalTerminalWeak (C := C)
  apply TopCat.hom_ext
  exact TopCat.realizedConullHomotopyFiberLoopEquiv_toFun K
    (show K _⦋0⦌ from ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)
    (SSet.toTop.map
      (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
    (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C)) hK

/-- Its weakness is derived from the two actual inverse homotopies. -/
theorem zeroOriginalHomotopyFiberToLoops_mem :
    TopCat.weakHomotopyEquivalences (zeroOriginalHomotopyFiberToLoops (C := C)) :=
  TopCat.homotopyEquiv_toFun_mem (zeroOriginalHomotopyFiberLoopEquiv (C := C))

/-- The actual selected total unit and constant path are sent to the original constant Q loop. -/
theorem zeroOriginalHomotopyFiberToLoops_selectedPoint :
    TopCat.homotopyFiberSelectedPointMap
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (zeroTotalVertex (C := C)) (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C)) ≫
        zeroOriginalHomotopyFiberToLoops (C := C) =
      (TopCat.const (Path.refl (zeroQVertex (C := C))) : TopCat.of PUnit.{(max u v) + 1} ⟶
        TopCat.of (LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v}))
          (zeroQVertex (C := C)))) := by
  let K : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  have hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)) :=
    originalLocalizedTotalTerminalWeak (C := C)
  have hForward := TopCat.realizedConullHomotopyFiberLoopEquiv_toFun K
    (show K _⦋0⦌ from ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)
    (SSet.toTop.map
      (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
    (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C)) hK
  have h := TopCat.homotopyFiberToLoopsOfRealizedConull_selectedPoint K
    (show K _⦋0⦌ from ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)
    (SSet.toTop.map
      (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
    (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C)) hK
  have hMap : zeroOriginalHomotopyFiberToLoops (C := C) =
      TopCat.homotopyFiberToLoopsOfRealizedConull K
        (show K _⦋0⦌ from ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C)) hK := by
    apply TopCat.hom_ext
    exact hForward
  exact hMap.symm ▸ h

/-- Every associative unital ring retains the same full homotopy-fiber loop equivalence. -/
def projectiveOriginalHomotopyFiberLoopEquiv {R : Type uRing} [Ring R] :=
  zeroOriginalHomotopyFiberLoopEquiv (C := FGProjectiveCat.{vModule} R)

/-- The all-ring forward map retains the original universe profile and every component. -/
theorem projectiveOriginalHomotopyFiberToLoops_mem {R : Type uRing} [Ring R] :
    TopCat.weakHomotopyEquivalences
      (zeroOriginalHomotopyFiberToLoops (C := FGProjectiveCat.{vModule} R)) :=
  zeroOriginalHomotopyFiberToLoops_mem (C := FGProjectiveCat.{vModule} R)

/-- Specialize the actual fiber-side relative inverse to the original unit point. -/
@[nolint defsWithUnderscore] -- component name of the equivalence; used downstream
def zeroOriginalHomotopyFiberLoopEquiv_leftHomotopyRel :
    ContinuousMap.HomotopyRel
      ((zeroOriginalHomotopyFiberLoopEquiv (C := C)).invFun.comp
        (zeroOriginalHomotopyFiberLoopEquiv (C := C)).toFun)
      (ContinuousMap.id (TopCat.homotopyFiber
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (zeroQVertex (C := C))))
      {TopCat.homotopyFiberSelectedPointMap
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (zeroTotalVertex (C := C)) (zeroQVertex (C := C))
        (zeroTotalVertex_map (C := C)) PUnit.unit} := by
  let K : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  have hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)) :=
    originalLocalizedTotalTerminalWeak (C := C)
  exact TopCat.realizedConullHomotopyFiberLoopEquiv_leftHomotopyRel K
    (show K _⦋0⦌ from ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)
    (SSet.toTop.map
      (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
    (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C)) hK

/-- The original loop-side inverse homotopy fixes the literal constant loop at
the actual Q zero vertex, retaining every component and the original u/v. -/
@[nolint defsWithUnderscore] -- component name of the equivalence; used downstream
def zeroOriginalHomotopyFiberLoopEquiv_rightHomotopyRel :
    ContinuousMap.HomotopyRel
      ((zeroOriginalHomotopyFiberLoopEquiv (C := C)).toFun.comp
        (zeroOriginalHomotopyFiberLoopEquiv (C := C)).invFun)
      (ContinuousMap.id
        (LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v}))
          (zeroQVertex (C := C)))) {Path.refl (zeroQVertex (C := C))} := by
  let K : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  have hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)) :=
    originalLocalizedTotalTerminalWeak (C := C)
  exact TopCat.realizedConullHomotopyFiberLoopEquiv_rightHomotopyRel K
    (show K _⦋0⦌ from ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)
    (SSet.toTop.map
      (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
    (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C)) hK

end AlgebraicKTheory.OriginalQZeroComparison

end
