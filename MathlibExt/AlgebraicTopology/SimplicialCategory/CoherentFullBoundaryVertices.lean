/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFullBoundaryFaces

/-!
# Literal vertices of the same full original coherent boundary

Every original horn restriction retains precisely the same individual
boundary vertex. Each supplied full face reads that vertex along its
same original ordinal inclusion. All original face labels are included.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.BoundaryFaces
open SimplicialEnrichment

variable {C : Carrier.{u}} {n : ℕ}
  (f : (∂Δ[n + 2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The same original full-boundary vertex, read from the canonical original inner-horn
restriction. -/
def object (t : Fin (n + 3)) : C := HornFaces.object (horn f (1 : Fin (n + 3))) t

/-- Every full original horn restriction retains the same literal individual boundary vertex. -/
theorem object_horn (i t : Fin (n + 3)) :
    HornFaces.object (horn f i) t = object f t := rfl

/-- The supplied whole original face reads every same original vertex under its actual
ordinal face map. -/
theorem faceFunctor_obj (j : Fin (n + 3)) (t : coherentSimplex.{u} ⦋n + 1⦌) :
    (faceFunctor f j).obj t = object f (j.succAbove t.as.down) := by
  classical
  let i : Fin (n + 3) := if j = 0 then 1 else 0
  have hi : j ≠ i := by
    dsimp [i]
    split_ifs with h
    · subst j
      intro h01
      have hval := congrArg Fin.val h01
      change 0 = 1 at hval
      omega
    · exact h
  exact (congrArg (fun F : coherentSimplex.{u} ⦋n + 1⦌ ⟶ C => F.obj t)
    (horn_face f i j hi).symm).trans
      ((HornFaces.faceFunctor_obj (horn f i) j hi t).trans (object_horn f i _))

end CategoryTheory.CoherentRealization.BoundaryFaces
