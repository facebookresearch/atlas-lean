/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingFactorizations
import MathlibExt.CategoryTheory.SmallObject.BoundaryOmegaIndex
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic

/-!
# The SAME full original boundary factorization as an actual sequential cell complex

The actual original boundary small-object factorization of any complete
fixed-object map is reindexed by the existing canonical omega order
isomorphism. Its SAME original source, target, all native occurrences
and full enriched maps are retained. No cofibrancy, countability or
weakness of the supplied source or target is required.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization
variable {O : Type u} {C D : FixedObjects O} (p : C ⟶ D)

/-- Reindex the SAME whole original boundary-factorization cell structure on its canonical omega stages. -/
def sequentialBoundaryCells :
    RelativeCellComplex.{u} (fun (_ : ℕ) => (boundaryFamily O).homFamily) (boundary p).i where
  toTransfiniteCompositionOfShape := (boundaryCells p).toTransfiniteCompositionOfShape.ofOrderIso
    SmallObject.aleph0StageOrderIso
  attachCells n _hn := by
    let j := SmallObject.aleph0Stage.{u} n
    let _ : NoMaxOrder Cardinal.aleph0.{u}.ord.ToType := Cardinal.noMaxOrder (le_refl _)
    let a := (boundaryCells p).attachCells j (not_isMax j)
    let e : (boundaryCells p).F.obj (Order.succ j) ≅
        (SmallObject.aleph0StageOrderIso.equivalence.functor ⋙ (boundaryCells p).F).obj (n+1) :=
      (boundaryCells p).F.mapIso (eqToIso (SmallObject.aleph0Stage_succ n).symm)
    refine a.ofArrowIso (Arrow.isoMk (Iso.refl _) e ?_)
    change 𝟙 _ ≫ (boundaryCells p).F.map
      (SmallObject.aleph0StageOrderIso.equivalence.functor.map (homOfLE (n.le_add_right 1))) =
      (boundaryCells p).F.map (homOfLE (Order.le_succ j)) ≫
        (boundaryCells p).F.map (eqToHom (SmallObject.aleph0Stage_succ n).symm)
    rw [Category.id_comp, ← Functor.map_comp]
    apply congrArg (boundaryCells p).F.map
    exact Subsingleton.elim _ _

/-- Every original full reindexed stage is the SAME supplied native boundary stage. -/
theorem sequentialBoundaryCells_stage (n : ℕ) :
    (sequentialBoundaryCells p).F.obj n = (boundaryCells p).F.obj (SmallObject.aleph0Stage n) := rfl

/-- The full terminal cocone remains the SAME original boundary-factorization left map. -/
theorem sequentialBoundaryCells_fac :
    (sequentialBoundaryCells p).isoBot.inv ≫ (sequentialBoundaryCells p).incl.app 0 = (boundary p).i :=
  (sequentialBoundaryCells p).fac

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization
