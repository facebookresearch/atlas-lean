/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalInitialEdgeTailRowComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectRowFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpComparison

/-!
# The actual leading-edge row comparison at one fixed original source

The leading-edge/tail comparison preserves the original source vertex.
Pulling it back along the same prescribed source therefore gives the
actual original fixed-object path row comparison. Its target retains
the original full tail simplex and the whole original source-edge fibre.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.InitialEdgeTailMapping

/-- The original source projection of the entire leading-edge and tail target. -/
def rowSource (W : SimplicialSpace.{u}) (n : ℕ) : rowTarget W n ⟶ W.diagram _⦋0⦌ :=
  pullback.snd _ _ ≫ W.diagram.δ (1 : Fin 2)

set_option backward.isDefEq.respectTransparency false in
/-- The entire row comparison retains the original first source vertex. -/
theorem rowComparison_source (W : SimplicialSpace.{u}) (n : ℕ) :
    rowComparison W n ≫ rowSource W n =
      (CategoryTheory.SimplicialObject.LeftDecalage.augmentation W.diagram).app
        (op (SimplexCategory.mk n)) := by
  rw [rowSource, ← Category.assoc, rowComparison_snd]
  change W.diagram.map (SimplexCategory.mkOfSucc (0 : Fin (n + 1))).op ≫
      W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op =
    W.diagram.map (CategoryTheory.SimplicialObject.LeftDecalage.firstVertex.app (SimplexCategory.mk n)).op
  rw [← W.diagram.map_comp, ← op_comp]
  apply congrArg W.diagram.map
  apply Quiver.Hom.unop_inj
  ext i
  fin_cases i
  rfl

/-- The exact original target of the leading-edge comparison at the same prescribed source. -/
abbrev sourceFibreTarget (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) : SSet.{u} :=
  pullback (rowSource W n) (SSet.yonedaEquiv.symm x)

set_option backward.isDefEq.respectTransparency false in
/-- The whole original row comparison at the same prescribed fixed source. -/
def sourceFibreComparison (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    pullback ((CategoryTheory.SimplicialObject.LeftDecalage.augmentation W.diagram).app
        (op (SimplexCategory.mk n))) (SSet.yonedaEquiv.symm x) ⟶ sourceFibreTarget W x n :=
  pullback.map _ _ _ _ (rowComparison W n) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using (rowComparison_source W n).symm)
    (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The original fixed-source comparison retains its entire original row comparison. -/
theorem sourceFibreComparison_fst (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    sourceFibreComparison W x n ≫ pullback.fst _ _ =
      pullback.fst ((CategoryTheory.SimplicialObject.LeftDecalage.augmentation W.diagram).app
        (op (SimplexCategory.mk n))) (SSet.yonedaEquiv.symm x) ≫ rowComparison W n :=
  pullback.lift_fst _ _ _

end SimplicialSpace.InitialEdgeTailMapping
