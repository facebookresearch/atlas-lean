/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerTwoObjectGenerators
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectCodiscreteTerminal

/-! # The original two labels with their SAME full codiscrete unit-Hom groupoid -/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.OriginalTwoLabelUnitGroupoid

/-- The SAME original two-object label family, retaining every original object. -/
abbrev labels : Type u := BergnerTwoObject.object (𝟙_ SSet.{u})

/-- The actual original full unit-Hom groupoid on those SAME two original labels. -/
abbrev object : Carrier.{u} := (FixedObjects.CodiscreteTerminal.object labels.{u}).val

/-- The SAME original selected source label in the complete unit-Hom groupoid. -/
def source : object.{u} := BergnerTwoObject.source (𝟙_ SSet.{u})

/-- The SAME original selected target label in the complete unit-Hom groupoid. -/
def target : object.{u} := BergnerTwoObject.target (𝟙_ SSet.{u})

end CategoryTheory.SimplicialEnrichment.OriginalTwoLabelUnitGroupoid
