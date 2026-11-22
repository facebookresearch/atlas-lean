/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SelectedEdges
import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.LeftHornCriterion

/-!
# Actual marked critical left-horn cells

The source is the original left outer horn, marked by its critical initial
edge and its original degeneracies. The target is the original standard
simplex with precisely that image edge and its original degeneracies
marked. The cell retains the complete original horn inclusion. Its lifting
condition detects the actual Cocartesian condition on marked target edges.
No quasicategory, model structure, or equivalence certificate is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original left outer horn with its critical initial edge marked. -/
def cocartesianCriticalSource (n : ℕ) : Marked.{u} :=
  withEdges (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) {leftHornEdgeSimplex.{u} n}

/-- The original standard simplex with the same entire image critical edge marked. -/
def cocartesianCriticalTarget (n : ℕ) : Marked.{u} :=
  withEdges (Δ[n + 2] : SSet.{u}) {((horn.{u} (n + 2) ((0 : Fin (n + 3)))).ι.app (op ⦋1⦌)
    (leftHornEdgeSimplex.{u} n))}

/-- The actual marked critical cell retains the original left horn inclusion. -/
def cocartesianCriticalCell (n : ℕ) : cocartesianCriticalSource.{u} n ⟶ cocartesianCriticalTarget.{u} n :=
  ofWithEdges (horn.{u} (n + 2) ((0 : Fin (n + 3)))).ι (by
    intro e he
    obtain rfl : e = leftHornEdgeSimplex.{u} n := he
    exact Or.inr rfl)

/-- Every original simplex is mapped by the native horn inclusion. -/
@[simp]
theorem cocartesianCriticalCell_hom (n : ℕ) :
    (cocartesianCriticalCell.{u} n).hom = (horn.{u} (n + 2) ((0 : Fin (n + 3)))).ι := rfl

/-- The actual marked critical cell is monic on its entire original simplicial carrier. -/
theorem cocartesianCriticalCell_mono (n : ℕ) : Mono (cocartesianCriticalCell.{u} n) := by
  let _ : Mono (cocartesianCriticalCell.{u} n).hom :=
    inferInstanceAs (Mono (horn.{u} (n + 2) ((0 : Fin (n + 3)))).ι)
  exact Hom.mono_of_underlying _

/-- The given critical edge condition makes the original horn map a map of the selected marked carriers. -/
def ofCocartesianCriticalSource {Y : Marked.{u}} {n : ℕ}
    (f : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ Y.toSSet)
    (h : f.app (op ⦋1⦌) (leftHornEdgeSimplex.{u} n) ∈ Y.marking) :
    cocartesianCriticalSource n ⟶ Y := ofWithEdges f (by
      intro e he
      obtain rfl : e = leftHornEdgeSimplex.{u} n := he
      exact h)

/-- An original full simplex with that marked critical image gives its actual marked target map. -/
def ofCocartesianCriticalTarget {Y : Marked.{u}} {n : ℕ}
    (f : (Δ[n + 2] : SSet.{u}) ⟶ Y.toSSet)
    (h : f.app (op ⦋1⦌) ((horn.{u} (n + 2) ((0 : Fin (n + 3)))).ι.app (op ⦋1⦌)
      (leftHornEdgeSimplex.{u} n)) ∈ Y.marking) :
    cocartesianCriticalTarget n ⟶ Y := ofWithEdges f (by
      intro e he
      obtain rfl : e = (horn.{u} (n + 2) ((0 : Fin (n + 3)))).ι.app (op ⦋1⦌)
        (leftHornEdgeSimplex.{u} n) := he
      exact h)

end SSet.Marked
