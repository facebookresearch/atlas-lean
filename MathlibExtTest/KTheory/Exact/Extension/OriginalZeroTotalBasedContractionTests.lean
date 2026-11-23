/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalZeroTotalBasedContraction

/-!
# The original total and its literal unit at every contraction time

The actual localized extension realization contracts at the original completed
unit/zero total vertex. All three equations, the literal vertex presentation
and the original Q-zero projection are retained in arbitrary category and
ring/module universes.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicKTheory AlgebraicKTheory.OriginalQZeroComparison
open scoped Simplicial

universe u v uRing vModule

namespace MathlibExtTest.KTheory.Exact.Extension.OriginalZeroTotalBasedContractionTests

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Every original total point and time satisfies the complete contraction
equations at the literal unit vertex, whose original projection stays Q-zero. -/
theorem originalTotal_allEquations :
    let K : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
    let H := originalConullContraction (E := C)
    (∀ e : SSet.toTop.obj K,
      H.homotopy (0, e) = e ∧ H.homotopy (1, e) = zeroTotalVertex (C := C)) ∧
    (∀ s : unitInterval, H.homotopy (s, zeroTotalVertex (C := C)) = zeroTotalVertex (C := C)) ∧
    (∀ s : unitInterval,
      SSet.toTop.map
        (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C)))
        (H.homotopy (s, zeroTotalVertex (C := C))) = zeroQVertex (C := C)) ∧
    zeroTotalVertex (C := C) =
      SSet.realizedVertex (ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val) := by
  let H := originalConullContraction (E := C)
  refine ⟨fun e => ⟨H.homotopy.apply_zero e, H.homotopy.apply_one e⟩, H.fixed, ?_, rfl⟩
  intro s
  exact (congrArg
    (SSet.toTop.map
      (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
    (H.fixed s)).trans (zeroTotalVertex_map (C := C))

/-- The same original construction retains all equations for every associative
unital ring and an independently chosen module universe. -/
theorem projectiveTotal_allEquations {R : Type uRing} [Ring R] :
    let C := FGProjectiveCat.{vModule} R
    let H := originalConullContraction (E := C)
    (∀ e : SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := C))),
      H.homotopy (0, e) = e ∧ H.homotopy (1, e) = zeroTotalVertex (C := C)) ∧
    (∀ s : unitInterval, H.homotopy (s, zeroTotalVertex (C := C)) = zeroTotalVertex (C := C)) ∧
    (∀ s : unitInterval,
      SSet.toTop.map (nerveMapCommonHom (ExtensionCategory.localizedTarget (C := C)))
        (H.homotopy (s, zeroTotalVertex (C := C))) = zeroQVertex (C := C)) ∧
    zeroTotalVertex (C := C) =
      SSet.realizedVertex (ComposableArrows.mk₀ (zeroFiberUnit (C := C)).val) :=
  originalTotal_allEquations (FGProjectiveCat.{vModule} R)

end MathlibExtTest.KTheory.Exact.Extension.OriginalZeroTotalBasedContractionTests

end
