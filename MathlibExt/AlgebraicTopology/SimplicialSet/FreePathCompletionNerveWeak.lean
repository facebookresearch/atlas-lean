/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidPositiveCommaWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.LeftCommaQuillenACommonUniverse
import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathGraphCompletionMap

/-!
# The SAME original free-path completion nerve map is genuinely weak

For every original quiver, the actual left comma of the full native
path-completion functor is its SAME original positive-cover category.
The proved entire original covering-graph contraction supplies genuine
all-comma weakness. Native common-universe Quillen A proves weakness
of the SAME original pathCompletionMap and native categorical unit.
No general category or cofibrant completion theorem is asserted here.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- The SAME full original native free-path completion map is a realization weak equivalence. -/
theorem pathCompletionMap_weak : SSet.realizationWeakEquivalences (pathCompletionMap V) := by
  let F : Paths V ⥤ Quiver.FreeGroupoid V := FreePathCompletion.pathToQuiverGroupoid V
  have h := SSet.nerveMapCommonHom_weak_of_leftComma.{u, max u v, 0} F
    (fun z => by
      cases z with
      | mk z => exact Quiver.FreeGroupoid.OriginalWords.positiveCoverComma_to_point_weak V z)
  exact h

/-- The SAME entire original generating graph maps weakly into its actual original native quiver free groupoid. -/
theorem graphCompletionMap_weak : SSet.realizationWeakEquivalences (graphCompletionMap V) :=
  SSet.realizationWeakEquivalences.comp_mem _ _ (generatingGraph_inclusion_weak V) (pathCompletionMap_weak V)

/-- The actual native full categorical groupoid unit on the SAME original free-path category is realization weak. -/
theorem original_path_unit_nerve_weak :
    SSet.realizationWeakEquivalences (nerveMap (FreeGroupoid.of (Paths V))) := by
  let _ : (FreePathCompletion.toQuiverGroupoid V).IsEquivalence := (FreePathCompletion.equivalence
    V).isEquivalence_functor
  have hcoord : SSet.realizationWeakEquivalences (nerveMap (FreePathCompletion.toQuiverGroupoid V)) :=
    CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence (FreePathCompletion.toQuiverGroupoid V)
  apply SSet.realizationWeakEquivalences.of_postcomp (nerveMap (FreeGroupoid.of (Paths V)))
    (nerveMap (FreePathCompletion.toQuiverGroupoid V)) hcoord
  rw [nativeUnit_pathCompletionMap]
  exact pathCompletionMap_weak V

end CategoryTheory.FreePathNerveCoordinates
