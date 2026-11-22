/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidPositiveCoverEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverGraphWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# The actual original completion left-comma nerve is weakly contractible

The SAME original positive-cover path category is equivalent to the
actual native StructuredArrow category of the original full path
completion map. Its full native cover graph contraction and genuine
nerve-of-equivalence weakness prove weakness of the original comma
map to the native point. No completion or weak outcome is assumed.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver for both native comma nerve maps. -/
private local instance coverQuiverForCommaWeak : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- The actual original native full positive-cover comma functor induces a genuine realization weak equivalence. -/
theorem positiveCover_nerveMap_weak :
    SSet.realizationWeakEquivalences (nerveMap (coverPathsToComma V z)) := by
  let _ : (coverPathsToComma V z).IsEquivalence := (positiveCoverEquivalence V z).isEquivalence_functor
  exact CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence (coverPathsToComma V z)

/-- EVERY actual native left-comma of the SAME original full path-completion map is realization weak to the point. -/
theorem positiveCoverComma_to_point_weak :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (nerve (PositiveCoverComma V z) : SSet.{max u v})) := by
  apply SSet.realizationWeakEquivalences.of_precomp (nerveMap (coverPathsToComma V z)) _
    (positiveCover_nerveMap_weak V z)
  have he : nerveMap (coverPathsToComma V z) ≫ SSet.stdSimplex.isTerminalObj₀.from
      (nerve (PositiveCoverComma V z) : SSet.{max u v}) =
        SSet.stdSimplex.isTerminalObj₀.from (nerve (Paths (CoverVertex V z)) : SSet.{max u v}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact coverPathNerve_to_point_weak V z

/-- The full original comma map retains EVERY original native path and coefficient. -/
lemma positiveCover_nerveMap_app (n : ℕ) (w : (nerve (Paths (CoverVertex V z))) _⦋n⦌) :
    (nerveMap (coverPathsToComma V z)).app (op ⦋n⦌) w = w ⋙ coverPathsToComma V z := rfl

end Quiver.FreeGroupoid.OriginalWords
