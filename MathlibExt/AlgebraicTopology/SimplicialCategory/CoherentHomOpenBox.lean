/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomBoxWords

/-!
# Open-box inclusions in coherent Hom objects

The coherent Hom open box is the union of the positive faces and the
negative faces other than the distinguished negative face. Its inclusion
in the interval-subset Hom nerve is anodyne, so maps from the box to
a Kan complex extend to the Hom nerve.

## References

- Emily Riehl, *Homotopy coherent structures*, the open-box description
  in the proof of Theorem II.2.7,
  https://emilyriehl.github.io/files/coherent-structures.pdf.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomOpenBox
open MappingCube CubeBoxes CubeBoundary

variable {J : Type u} [LinearOrder J] {i j : J}

/-- The coherent Hom open-box inclusion is an anodyne extension. -/
theorem subcomplex_anodyne (hij : i ≤ j) (k : IntervalHom.Interior i j) :
    SSet.anodyneExtensions (subcomplex hij k).ι := by
  rw [subcomplex_eq_hornPaths hij k]
  exact MathlibExt.CategoricalSource.anodyneExtensions_hornPaths_ι k.property.1 k.property.2

open SSet.modelCategoryQuillen in
/-- A map from the coherent Hom box into a Kan target extends on the 
Hom nerve. -/
theorem exists_fill (hij : i ≤ j) (k : IntervalHom.Interior i j) {Y : SSet.{u}} [SSet.KanComplex Y]
    (f : (subcomplex hij k : SSet) ⟶ Y) :
    ∃ g : nerve (SimplicialThickening.Path i j) ⟶ Y, (subcomplex hij k).ι ≫ g = f := by
  let _ : HasLiftingProperty (subcomplex hij k).ι (terminal.from Y) :=
    subcomplex_anodyne hij k _ (by rwa [← HomotopicalAlgebra.fibration_iff])
  let sq : CommSq f (subcomplex hij k).ι (terminal.from Y) (terminal.from _) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end CategoryTheory.CoherentRealization.HomOpenBox
