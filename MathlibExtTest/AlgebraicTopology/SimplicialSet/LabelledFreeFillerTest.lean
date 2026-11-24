/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: toskua, Avocado
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFiller

/-!
# Public clients of labelled one-step cell attachment

The clients retain the actual attaching equation and functor transport,
including two distinct labels specifying the same generator arrow.
-/

open CategoryTheory Limits HomotopicalAlgebra

universe u

namespace SSet.LabelledFreeFillerTest

variable {I : Type u} {K D : I → SSet.{u}} (j : ∀ s, K s ⟶ D s)

example (X : SSet.{u}) :
    (labelledFreeFiller.attachCells j X).ι = labelledFreeFiller.Index K X := rfl

example {X Y : SSet.{u}} (m : X ⟶ Y) (s : I) (a : K s ⟶ X) :
    j s ≫ labelledFreeFiller.cell j s a = a ≫ (labelledFreeFiller.unit j).app X ∧
    labelledFreeFiller.cell j s a ≫ (labelledFreeFiller j).map m =
      labelledFreeFiller.cell j s (a ≫ m) ∧
    (labelledFreeFiller.unit j).app X ≫ (labelledFreeFiller j).map m =
      m ≫ (labelledFreeFiller.unit j).app Y :=
  ⟨labelledFreeFiller.cell_boundary j s a, labelledFreeFiller.cell_naturality j m s a,
    ((labelledFreeFiller.unit j).naturality m).symm⟩

example (X : SSet.{u}) :
    (MorphismProperty.ofHoms j).rlp.llp ((labelledFreeFiller.unit j).app X) :=
  labelledFreeFiller.unit_mem j X

example {X Y Z : SSet.{u}} (m : X ⟶ Y) (n : Y ⟶ Z) :
    (labelledFreeFiller j).map (𝟙 X) = 𝟙 _ ∧
    (labelledFreeFiller j).map (m ≫ n) =
      (labelledFreeFiller j).map m ≫ (labelledFreeFiller j).map n :=
  ⟨(labelledFreeFiller j).map_id X, (labelledFreeFiller j).map_comp m n⟩

/-- Equal generator arrows with different labels still have different cell indices. -/
lemma duplicate_indices {A B X : SSet.{u}} (i : A ⟶ B) (a : A ⟶ X)
    (s t : I) (h : s ≠ t) :
    labelledFreeFiller.indexEquiv (fun _ : I ↦ i) X ⟨s, a⟩ ≠
      labelledFreeFiller.indexEquiv (fun _ : I ↦ i) X ⟨t, a⟩ := by
  intro he
  exact h (congrArg SmallObject.FunctorObjIndex.i he)

example {A B X : SSet.{u}} (i : A ⟶ B) (a : A ⟶ X) (s t : I) :
    i ≫ labelledFreeFiller.cell (fun _ : I ↦ i) s a =
      a ≫ (labelledFreeFiller.unit (fun _ : I ↦ i)).app X ∧
    i ≫ labelledFreeFiller.cell (fun _ : I ↦ i) t a =
      a ≫ (labelledFreeFiller.unit (fun _ : I ↦ i)).app X :=
  ⟨labelledFreeFiller.cell_boundary (fun _ : I ↦ i) s a,
    labelledFreeFiller.cell_boundary (fun _ : I ↦ i) t a⟩

end SSet.LabelledFreeFillerTest
