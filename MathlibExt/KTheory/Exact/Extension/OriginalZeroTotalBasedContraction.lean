/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalZeroLoopHomotopyFiber
public import MathlibExt.Topology.Category.TopCat.RealizedVertexBasedContraction

/-!
# The original localized-total contraction at its literal unit vertex

The same original localized total is contractible. Its terminal map is weak,
and the actual realized-vertex construction gives a jointly continuous
contraction at the literal completed-unit/zero vertex, fixed at every time.
The existing original conull comparison uses this one canonical factory.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uE vE

namespace AlgebraicKTheory.OriginalQZeroComparison

/-- The actual original localized total contracts to its literal completed-unit
vertex, through its proved terminal weakness and actual vertex cofibration. -/
@[expose] def originalConullContraction
    {E : Type uE} [Category.{vE} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E] :
    TopCat.BasedContraction
      (SSet.toTop.obj (nerve (ExtensionCategory.localizedExtensions (C := E)) : SSet.{max uE vE}))
      (zeroTotalVertex (C := E)) :=
  SSet.basedContractionAtRealizedVertex
    (nerve (ExtensionCategory.localizedExtensions (C := E)) : SSet.{max uE vE})
    (ComposableArrows.mk₀ (zeroFiberUnit (C := E)).val)
    (originalLocalizedTotalTerminalWeak (C := E))

end AlgebraicKTheory.OriginalQZeroComparison

end
