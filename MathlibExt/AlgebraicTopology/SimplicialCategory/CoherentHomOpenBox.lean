/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomBoxWords

/-!
# Actual open-box inclusions in original coherent Hom objects

The source is the genuine distinguished-coordinate scalar box. Its map
to the actual interval-subset Hom nerve is constructed through the proved
whole Hom cube isomorphism. The actual range inclusion is anodyne, and
an actual Kan target admits an extension retaining the whole original
box. All comparisons use explicit isomorphisms, not higher right properness.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomOpenBox
open MappingCube CubeBoxes CubeBoundary

variable {J : Type u} [LinearOrder J] {i j : J}

/-- Its actual subcomplex inclusion is an anodyne extension, without an enriched-model
hypothesis. -/
theorem subcomplex_anodyne (hij : i ≤ j) (k : IntervalHom.Interior i j) :
    SSet.anodyneExtensions (subcomplex hij k).ι := by
  rw [subcomplex_eq_hornPaths hij k]
  exact MathlibExt.CategoricalSource.anodyneExtensions_hornPaths_ι k.property.1 k.property.2

open SSet.modelCategoryQuillen in
/-- An actual map from the original coherent Hom box into a Kan target extends on the entire
original Hom nerve. -/
theorem exists_fill (hij : i ≤ j) (k : IntervalHom.Interior i j) {Y : SSet.{u}} [SSet.KanComplex Y]
    (f : (subcomplex hij k : SSet) ⟶ Y) :
    ∃ g : nerve (SimplicialThickening.Path i j) ⟶ Y, (subcomplex hij k).ι ≫ g = f := by
  let _ : HasLiftingProperty (subcomplex hij k).ι (terminal.from Y) :=
    subcomplex_anodyne hij k _ (by rwa [← HomotopicalAlgebra.fibration_iff])
  let sq : CommSq f (subcomplex hij k).ι (terminal.from Y) (terminal.from _) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end CategoryTheory.CoherentRealization.HomOpenBox
