/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SelectedEdges
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.RightHornCriterion

/-!
# Actual marked critical right-horn cells

The source is the original right outer horn, marked by its critical final
edge and its original degeneracies. The target is the original standard
simplex with precisely that image edge and its original degeneracies
marked. The cell retains the complete original horn inclusion. Its lifting
condition detects the actual Cartesian condition on marked target edges.
No quasicategory, model structure, or equivalence certificate is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original right outer horn with its critical final edge marked. -/
def cartesianCriticalSource (n : ℕ) : Marked.{u} :=
  withEdges (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) {rightHornEdgeSimplex.{u} n}

/-- The original standard simplex with the same entire image critical edge marked. -/
def cartesianCriticalTarget (n : ℕ) : Marked.{u} :=
  withEdges (Δ[n + 2] : SSet.{u}) {((horn.{u} (n + 2) (Fin.last (n + 2))).ι.app (op ⦋1⦌)
    (rightHornEdgeSimplex.{u} n))}

/-- The actual marked critical cell retains the original right horn inclusion. -/
def cartesianCriticalCell (n : ℕ) : cartesianCriticalSource.{u} n ⟶ cartesianCriticalTarget.{u} n :=
  ofWithEdges (horn.{u} (n + 2) (Fin.last (n + 2))).ι (by
    intro e he
    obtain rfl : e = rightHornEdgeSimplex.{u} n := he
    exact Or.inr rfl)

/-- Every original simplex is mapped by the native horn inclusion. -/
@[simp]
theorem cartesianCriticalCell_hom (n : ℕ) :
    (cartesianCriticalCell.{u} n).hom = (horn.{u} (n + 2) (Fin.last (n + 2))).ι := rfl

/-- The actual marked critical cell is monic on its entire original simplicial carrier. -/
theorem cartesianCriticalCell_mono (n : ℕ) : Mono (cartesianCriticalCell.{u} n) := by
  let _ : Mono (cartesianCriticalCell.{u} n).hom :=
    inferInstanceAs (Mono (horn.{u} (n + 2) (Fin.last (n + 2))).ι)
  exact Hom.mono_of_underlying _

/-- The given critical edge condition makes the original horn map a map of the selected marked carriers. -/
def ofCartesianCriticalSource {Y : Marked.{u}} {n : ℕ}
    (f : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ Y.toSSet)
    (h : f.app (op ⦋1⦌) (rightHornEdgeSimplex.{u} n) ∈ Y.marking) :
    cartesianCriticalSource n ⟶ Y := ofWithEdges f (by
      intro e he
      obtain rfl : e = rightHornEdgeSimplex.{u} n := he
      exact h)

/-- An original full simplex with that marked critical image gives its actual marked target map. -/
def ofCartesianCriticalTarget {Y : Marked.{u}} {n : ℕ}
    (f : (Δ[n + 2] : SSet.{u}) ⟶ Y.toSSet)
    (h : f.app (op ⦋1⦌) ((horn.{u} (n + 2) (Fin.last (n + 2))).ι.app (op ⦋1⦌)
      (rightHornEdgeSimplex.{u} n)) ∈ Y.marking) :
    cartesianCriticalTarget n ⟶ Y := ofWithEdges f (by
      intro e he
      obtain rfl : e = (horn.{u} (n + 2) (Fin.last (n + 2))).ι.app (op ⦋1⦌)
        (rightHornEdgeSimplex.{u} n) := he
      exact h)

end SSet.Marked
