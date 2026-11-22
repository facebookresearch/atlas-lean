/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange

/-!
# The selected-point map into a homotopy fiber of a conull total

The constant map from the selected point has a homotopy fiber containing
all based paths. Its canonical changing-source map into the original
homotopy fiber is weak when the original total has weak terminal map.
The point, its image and the complete path coordinate are retained.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat

/-- The actual selected-point square induces a weak full homotopy-fiber map
when the terminal map of the original total is weak. -/
theorem homotopyFiberPointMap_mem_of_total_conull {E B : TopCat.{u}}
    (p : E ⟶ B) (e : E) (b : B) (he : p e = b)
    (hE : weakHomotopyEquivalences (terminal.from E)) :
    weakHomotopyEquivalences
      (homotopyFiberMapOfSquare
        (p := (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B)) (q := p)
        (TopCat.const e : TopCat.of PUnit.{u + 1} ⟶ E) (𝟙 B)
        (by
          apply TopCat.ext
          exact fun _ => he.symm) b) := by
  let P : TopCat.{u} := TopCat.of PUnit.{u + 1}
  let point : P ⟶ E := TopCat.const e
  let t : E ⟶ P := terminal.from E ≫ TopCat.terminalIsoPUnit.hom
  have ht : weakHomotopyEquivalences t :=
    CategoryTheory.MorphismProperty.RespectsIso.postcomp weakHomotopyEquivalences
      TopCat.terminalIsoPUnit.hom (terminal.from E) hE
  have hpt : point ≫ t = 𝟙 P := TopCat.isTerminalPUnit.hom_ext _ _
  have hComposite : weakHomotopyEquivalences (point ≫ t) := by
    rw [hpt]
    exact weakHomotopyEquivalences.id_mem P
  have hPoint : weakHomotopyEquivalences point :=
    weakHomotopyEquivalences.of_postcomp point t ht hComposite
  exact homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences
    (p := (TopCat.const b : P ⟶ B)) (q := p) point (𝟙 B)
    (by
      apply TopCat.ext
      exact fun _ => he.symm) b hPoint (weakHomotopyEquivalences.id_mem B)

end TopCat

end
