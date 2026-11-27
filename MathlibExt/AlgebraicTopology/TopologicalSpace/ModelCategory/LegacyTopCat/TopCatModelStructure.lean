/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexBoundaryRLPRecognition
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornCellWeakHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructureFromSSet

/-!
# Model structure on topological spaces

For every universe `u`, `TopCat.{u}` has the model structure whose weak equivalences are weak
homotopy equivalences, cofibrations form `realizedBoundaryInclusions.rlp.llp`, and fibrations
form `realizedHornInclusions.rlp`. The named value is `TopCat.modelCategory`, and the
corresponding typeclass instance is scoped to `TopCat.modelCategory`.
-/

@[expose] public section

open HomotopicalAlgebra

universe u

namespace TopCat

/-- For every universe `u`, the model-category structure `TopCat.modelCategory : ModelCategory
TopCat.{u}` has weak homotopy equivalences as weak equivalences, the boundary-generated class
`realizedBoundaryInclusions.{u}.rlp.llp` as cofibrations, and `realizedHornInclusions.{u}.rlp`
as fibrations. Its construction uses the horn-cell weak-equivalence theorem and the simplicial
Kan-restricted lifting and recognition theorems. -/
@[instance_reducible]
noncomputable def modelCategory : ModelCategory TopCat.{u} :=
  modelCategoryFromSSet
    horn_llp_le_weakHomotopyEquivalences
    SSet.KanComplex.I_rlp_to_W_kanRestricted
    SSet.modelCategoryQuillen.J_rlp_inf_W_le_I_rlp

namespace modelCategory

/-- The scoped instance in `TopCat.modelCategory` installs the value `TopCat.modelCategory :
ModelCategory TopCat.{u}` for every universe `u`. It has weak homotopy equivalences,
boundary-generated cofibrations, and horn-right-lifting fibrations; `open scoped
TopCat.modelCategory` selects this instance. -/
noncomputable scoped instance instModelCategory :
    ModelCategory TopCat.{u} :=
  TopCat.modelCategory

end modelCategory
end TopCat
