/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoops
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.KTheory.Exact.Extension.ZeroFiberLocalization
public import MathlibExt.KTheory.Exact.Extension.LocalizedTotal
public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic
public import MathlibExt.Topology.Homotopy.Contractible
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# The actual zero and completed-unit points of the original Q homotopy fiber

The completed-core tensor unit is carried by the original zero-row functor and the
actual strict-fiber inclusion. Its total vertex maps to the original Q zero vertex.
The selected-loop map keeps this point and every entire loop, and its weakness follows
from the proved contractibility of the original localized total. All categories and
object/Hom levels are retained.
-/

universe u v uRing vModule

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject Simplicial

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The literal completed-core unit, followed by the actual zero-row and strict-fiber functors. -/
def zeroFiberUnit : FixedTargetExtension.localizedFiber (C := C) (0 : C) :=
  (FixedTargetExtension.localizedFiberFunctor (0 : C)).obj
    ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj
      ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))

/-- The fiber property gives the original Q zero object as the actual target. -/
theorem zeroFiberUnit_target :
    (ExtensionCategory.localizedTarget (C := C)).obj (zeroFiberUnit (C := C)).val =
      (⟨0⟩ : QuillenQ C) :=
  (zeroFiberUnit (C := C)).property

/-- The total point is the ordinary realized vertex of that same zero/unit fiber object. -/
def zeroTotalVertex :
    SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}) :=
  SSet.realizedVertex (ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)

/-- The actual Q zero vertex agrees with the vertex used by the native Quillen-B comparison. -/
def zeroQVertex : SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v}) :=
  SSet.realizedVertex (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C))

/-- Native vertex naturality proves the exact selected-point equation, with no chosen path. -/
theorem zeroTotalVertex_map :
    SSet.toTop.map
        (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C)))
        (zeroTotalVertex (C := C)) = zeroQVertex (C := C) := by
  let p := ExtensionCategory.localizedTarget (C := C)
  have hVertex := SSet.realizedVertex_naturality
    (nerveMapCommonHom.{u, max u v, 0} p)
    (ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val)
  have hZero : (nerveMapCommonHom.{u, max u v, 0} p).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val) =
        ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C) := by
    apply ComposableArrows.ext₀
    change p.obj (zeroFiberUnit (C := C)).val = (⟨0⟩ : QuillenQ C)
    exact (zeroFiberUnit (C := C)).property
  exact hVertex.symm.trans (congrArg SSet.realizedVertex hZero)

/-- Every full original based loop is carried at the literal completed-unit/zero total point. -/
def zeroLoopToOriginalHomotopyFiber :
    TopCat.of (LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v}))
      (zeroQVertex (C := C))) ⟶
    TopCat.homotopyFiber
      (SSet.toTop.map
        (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
      (zeroQVertex (C := C)) :=
  TopCat.loopToHomotopyFiber
    (SSet.toTop.map
      (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
    (zeroTotalVertex (C := C)) (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C))

/-- The total coordinate is exactly the actual selected zero/unit total vertex. -/
theorem zeroLoopToOriginalHomotopyFiber_toTotal :
    zeroLoopToOriginalHomotopyFiber (C := C) ≫
        TopCat.homotopyFiberToTotal
          (SSet.toTop.map
            (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
          (zeroQVertex (C := C)) = TopCat.const (zeroTotalVertex (C := C)) := by
  unfold zeroLoopToOriginalHomotopyFiber
  exact TopCat.loopToHomotopyFiber_toTotal _ _ _ _

/-- The entire actual Q loop is retained in the compact-open path coordinate. -/
theorem zeroLoopToOriginalHomotopyFiber_path :
    zeroLoopToOriginalHomotopyFiber (C := C) ≫
        TopCat.homotopyFiberPath
          (SSet.toTop.map
            (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
          (zeroQVertex (C := C)) =
      TopCat.loopPathObjectMap (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v}))
        (zeroQVertex (C := C)) := by
  unfold zeroLoopToOriginalHomotopyFiber
  exact TopCat.loopToHomotopyFiber_path _ _ _ _

/-- The constant loop maps to the independently constructed full selected homotopy-fiber point. -/
theorem zeroLoopToOriginalHomotopyFiber_constant_point :
    (TopCat.const (Path.refl (zeroQVertex (C := C))) : TopCat.of PUnit.{(max u v) + 1} ⟶
      TopCat.of (LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v}))
        (zeroQVertex (C := C)))) ≫ zeroLoopToOriginalHomotopyFiber (C := C) =
      TopCat.homotopyFiberSelectedPointMap
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (zeroTotalVertex (C := C)) (zeroQVertex (C := C)) (zeroTotalVertex_map (C := C)) := by
  unfold zeroLoopToOriginalHomotopyFiber
  exact TopCat.loopToHomotopyFiber_constant_point _ _ _ _


/-- Contractibility of the same original localized total gives its terminal weakness. -/
theorem originalLocalizedTotalTerminalWeak :
    TopCat.weakHomotopyEquivalences (terminal.from
      (SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C)) :
        SSet.{max u v}))) := by
  let K : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  let _ : ContractibleSpace (SSet.toTop.obj K) :=
    LocalizedTotal.localizedTotal_contractible (C := C)
  let terminalHomeo : (⊤_ TopCat.{max u v}) ≃ₜ PUnit.{(max u v) + 1} :=
    TopCat.homeoOfIso (TopCat.terminalIsoPUnit.{max u v})
  let _ : ContractibleSpace (⊤_ TopCat.{max u v}) := terminalHomeo.contractibleSpace
  let f : SSet.toTop.obj K ⟶ ⊤_ TopCat.{max u v} := terminal.from (SSet.toTop.obj K)
  let equiv : ContinuousMap.HomotopyEquiv (SSet.toTop.obj K) (⊤_ TopCat.{max u v}) :=
    ContinuousMap.HomotopyEquiv.ofContractible
      (X := SSet.toTop.obj K) (Y := ⊤_ TopCat.{max u v}) f.hom
  exact TopCat.mem_of_eq_toFun
    (X := SSet.toTop.obj K) (Y := ⊤_ TopCat.{max u v}) (f := f) equiv
    (by rw [ContinuousMap.HomotopyEquiv.ofContractible_toFun]; rfl)

/-- Original localized-total contractibility supplies weakness of the actual selected loop map. -/
theorem zeroLoopToOriginalHomotopyFiber_mem :
    TopCat.weakHomotopyEquivalences (zeroLoopToOriginalHomotopyFiber (C := C)) := by
  unfold zeroLoopToOriginalHomotopyFiber
  exact TopCat.loopToHomotopyFiber_mem_of_total_conull _ _ _ _
    (originalLocalizedTotalTerminalWeak (C := C))

/-- The literal zero/unit comparison is weak over every associative unital ring. -/
theorem projectiveZeroLoopToOriginalHomotopyFiber_mem
    {R : Type uRing} [Ring R] :
    TopCat.weakHomotopyEquivalences
      (zeroLoopToOriginalHomotopyFiber (C := FGProjectiveCat.{vModule} R)) :=
  zeroLoopToOriginalHomotopyFiber_mem (C := FGProjectiveCat.{vModule} R)

end AlgebraicKTheory.OriginalQZeroComparison

end
