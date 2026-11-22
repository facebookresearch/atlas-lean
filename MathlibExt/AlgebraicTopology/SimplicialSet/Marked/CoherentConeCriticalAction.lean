/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalRootMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAction

/-!
# Every original whole coherent path preserves the critical coefficient marking

The actual original union action leaves the original subset maximum
unchanged. It therefore preserves the SAME critical last-edge marking
after the original final degeneracy, with a maximally marked whole path
parameter. Every original path vertex and complete cone subset remains.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- Every complete original path acts on the SAME critical cone coefficients through its literal original whole
union map. -/
def coneCriticalAction (n : ℕ) (i j : Vertex.{u} (n + 2)) :
    prod (max (nerve (SimplicialThickening.Path i j))) (coneCriticalWeight n j) ⟶ coneCriticalWeight n i where
  hom := (coneAction i j).hom
  preserve {e} he := by
    change coneCriticalMaximumCollapse n ((e.2.obj 0).prepend (e.1.obj 0)).maximum =
      coneCriticalMaximumCollapse n ((e.2.obj 1).prepend (e.1.obj 1)).maximum
    exact (congrArg (coneCriticalMaximumCollapse n) (ConeSubset.prepend_maximum _ _)).trans
      (he.2.trans (congrArg (coneCriticalMaximumCollapse n) (ConeSubset.prepend_maximum _ _)).symm)

/-- Every whole original critical action retains the entire original path and cone subset at every scalar vertex. -/
theorem coneCriticalAction_vertices (n : ℕ) (i j : Vertex.{u} (n + 2)) (q : ℕ)
    (p : (nerve (SimplicialThickening.Path i j)) _⦋q⦌)
    (a : (nerve (ConeSubset j)) _⦋q⦌) (t : Fin (q + 1)) :
    (((coneCriticalAction n i j).hom.app (op ⦋q⦌) (p, a)).obj t).vertices =
      (p.obj t).I.toFinite.toFinset ∪ (a.obj t).vertices := rfl

end SSet.Marked.CoherentWeight
