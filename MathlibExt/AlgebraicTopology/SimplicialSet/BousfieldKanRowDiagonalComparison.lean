/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialObject.DataCurryPromotionIso
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanRowDiagonalIso

/-!
# The SAME Bousfield--Kan carrier is the diagonal of its canonical rows

Currying/promotion and the canonical diagonal transposition isomorphism
retain both original bisimplicial directions. The forward and inverse
maps are identities on every original weighted-bar coefficient. The
indexing category object and Hom universes are independent.
-/

noncomputable section

universe uJ vJ

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

variable {J : Type uJ} [Category.{vJ} J]

/-- Both original weighted-bar transpose and evaluated-row diagrams retain their entire
original operators. -/
def wbarRowTransposeIso (D : J ⥤ SSet.{max uJ vJ}) :
    (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).flip ≅ wbarRowFunctor D :=
  SimplicialObject.Data.curryPromotionIso (StrictOrdinaryWeightedBar.wbarData
    (CategoryBar.replUnit J) D)

end SSet
