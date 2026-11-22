/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderCategoryDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint
import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence

/-!
# The actual full original scalar under-nerve diagonal is weakly contractible

Use the native nerve of each SAME canonical original scalar undercategory.
Both full original simplicial directions are retained by the actual
diagonal. Native original undercategory initiality contracts each full
nerve row. The genuine row-to-diagonal weak theorem proves weakness of
the SAME actual full diagonal projection to the point. No Hom-fibre or
group-completion unit weak outcome is assumed.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.ScalarUnderCategory

variable (C : Type v) [EnrichedCategory SSet.{u} C] (z : C)

/-- The entire actual original canonical scalar undercategory nerve diagram in both original directions. -/
def nerveDiagram : SimplicialObject SSet.{max u v} := diagram C z ⋙ nerveFunctor

/-- The SAME actual full original scalar under-nerve diagonal simplicial set. -/
def total : SSet.{max u v} := simplicialDiagonalFunctor.obj (nerveDiagram C z)

/-- Each SAME full original under-nerve row maps to the actual original simplicial point. -/
def rowPointMap : nerveDiagram C z ⟶ (SimplicialObject.const SSet.{max u v}).obj (Δ[0] : SSet.{max u v}) where
  app q := stdSimplex.isTerminalObj₀.from ((nerveDiagram C z).obj q)
  naturality q r f := by
    exact (stdSimplex.isTerminalObj₀.hom_ext _ _).trans (Category.comp_id _).symm

/-- The full actual original diagonal point map retains its SAME whole native original projection. -/
def pointMap : total C z ⟶ (Δ[0] : SSet.{max u v}) :=
  simplicialDiagonalFunctor.map (rowPointMap C z) ≫ (diagonalConstIso _).hom

/-- Every SAME original full scalar under-nerve row is weakly contractible by its genuine native initial object. -/
theorem rowPointMap_weak (q : SimplexCategoryᵒᵖ) : realizationWeakEquivalences ((rowPointMap C z).app q) :=
  NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_isInitial
    (Under.mkIdInitial (X := sourceObject C z q))

/-- The SAME actual complete original under-nerve diagonal is weakly contractible, through its literal whole point
map. -/
theorem pointMap_weak : realizationWeakEquivalences (pointMap C z) := by
  have h := simplicialDiagonal_map_mem_realizationWeakEquivalences (rowPointMap C z)
    (fun n => rowPointMap_weak C z (op ⦋n⦌))
  exact realizationWeakEquivalences.comp_mem _ _ h (realizationWeakEquivalences.of_isIso _)

/-- Every actual full original diagonal coefficient is the native whole undercategory chain in its SAME matching
scalar degree. -/
theorem total_obj (q : SimplexCategoryᵒᵖ) :
    (total C z).obj q = (nerve (category C z q)).obj q := rfl

end SSet.ScalarUnderCategory
