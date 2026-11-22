/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterMarkingCoverage
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CocartesianCriticalCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InnerCells

/-!
# Original inner and critical cell parameter markings are inherited exactly

The original higher horns contain all original vertices. Their minimal
marks and their supplied whole critical edge therefore cover every mark
of the original target cell. The actual monic parameter pushout-product
has exactly the inherited target marking on its original underlying
simplicial corner. This is a whole-carrier comparison, with no base or
marked-model premise.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

private theorem horn_zero_surjective (n : ℕ) (i : Fin (n + 3)) :
    Function.Surjective ((horn.{u} (n + 2) i).ι.app (op ⦋0⦌)) := by
  intro d
  exact ⟨⟨d, by rw [horn_obj_zero]; trivial⟩, rfl⟩

/-- Every original minimally marked higher horn covers its target's entire original minimal marking. -/
theorem innerCell_markingSurjective (n : ℕ) (i : Fin (n + 3)) :
    MarkingSurjective (innerCell.{u} n i) :=
  markingSurjective_minimal _ (horn_zero_surjective n i)

/-- The original Cartesian critical cell covers exactly all target marks, retaining its prescribed whole
  critical edge. -/
theorem cartesianCriticalCell_markingSurjective (n : ℕ) :
    MarkingSurjective (cartesianCriticalCell.{u} n) := by
  apply markingSurjective_selected (cartesianCriticalCell.{u} n)
  · exact horn_zero_surjective n (Fin.last (n + 2))
  · intro e he
    exact ⟨rightHornEdgeSimplex.{u} n, rfl, he.symm⟩

/-- The original cocartesian critical cell has the same full target-mark coverage for its actual initial edge. -/
theorem cocartesianCriticalCell_markingSurjective (n : ℕ) :
    MarkingSurjective (cocartesianCriticalCell.{u} n) := by
  apply markingSurjective_selected (cocartesianCriticalCell.{u} n)
  · exact horn_zero_surjective n 0
  · intro e he
    exact ⟨leftHornEdgeSimplex.{u} n, rfl, he.symm⟩

/-- The original inner-cell parameter corner source is exactly the target-inherited marking on the same
  whole simplicial corner. -/
def innerCellParameterSourceComapIso {A D : SSet.{u}} (a : A ⟶ D) [Mono a]
    (n : ℕ) (i : Fin (n + 3)) :
    (parameterPushout a (innerCell.{u} n i)).pt ≅
      comap (prod (max D) (min (Δ[n + 2] : SSet.{u})))
        (parameterPushoutProduct a (innerCell.{u} n i)).hom := by
  let _ := innerCell_mono n i
  exact parameterPushoutProductSourceComapIso a _ (innerCell_markingSurjective n i)

/-- The actual Cartesian critical parameter corner keeps precisely the target-inherited original marking. -/
def cartesianCriticalParameterSourceComapIso {A D : SSet.{u}} (a : A ⟶ D) [Mono a] (n : ℕ) :
    (parameterPushout a (cartesianCriticalCell.{u} n)).pt ≅
      comap (prod (max D) (cartesianCriticalTarget.{u} n))
        (parameterPushoutProduct a (cartesianCriticalCell.{u} n)).hom := by
  let _ := cartesianCriticalCell_mono n
  exact parameterPushoutProductSourceComapIso a _ (cartesianCriticalCell_markingSurjective n)

/-- The exact original cocartesian critical parameter corner has the same full inherited-marking description. -/
def cocartesianCriticalParameterSourceComapIso {A D : SSet.{u}} (a : A ⟶ D) [Mono a] (n : ℕ) :
    (parameterPushout a (cocartesianCriticalCell.{u} n)).pt ≅
      comap (prod (max D) (cocartesianCriticalTarget.{u} n))
        (parameterPushoutProduct a (cocartesianCriticalCell.{u} n)).hom := by
  let _ := cocartesianCriticalCell_mono n
  exact parameterPushoutProductSourceComapIso a _ (cocartesianCriticalCell_markingSurjective n)

end SSet.Marked
