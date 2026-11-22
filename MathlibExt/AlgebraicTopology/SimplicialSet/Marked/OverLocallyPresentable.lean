/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.LocallyPresentable
import MathlibExt.CategoryTheory.Presentable.OverStrongGenerator

/-!
# Original-universe local presentability of every marked slice

The actual marked simplex and interval generators retain every whole map
to the supplied marked base. Their proved source rank is unchanged, so the
native marked slice is locally presentable in its original universe. No
Kan, quasicategory, marking-size or presentability premise is imposed on
the original base.
-/

noncomputable section
universe u
open CategoryTheory

namespace SSet.Marked

local instance : Fact CellSmallness.cardinal.{u}.IsRegular := CellSmallness.cardinal_regular

/-- Every marked slice is locally presentable at the same genuine original cell-source rank. -/
theorem over_isCardinalLocallyPresentable (B : Marked.{u}) :
    IsCardinalLocallyPresentable (Over B) CellSmallness.cardinal.{u} :=
  over_isCardinalLocallyPresentable_of_generator strongGeneratorObj B CellSmallness.cardinal
    strongGenerator_isStrongGenerator
    (fun i => strongGenerator_presentable _ (ObjectProperty.ofObj.mk i))

/-- Every actual original marked slice is locally presentable without a bound on its base. -/
theorem over_isLocallyPresentable (B : Marked.{u}) : IsLocallyPresentable.{u} (Over B) where
  exists_cardinal := ⟨CellSmallness.cardinal, CellSmallness.cardinal_regular,
    over_isCardinalLocallyPresentable B⟩

end SSet.Marked
