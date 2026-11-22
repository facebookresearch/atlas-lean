/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexBoundaryRLPRecognition
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornCellWeakHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructureFromSSet

/-!
# The model structure on `TopCat` in every universe

The named structure uses weak homotopy equivalences, boundary-generated
cofibrations, and horn-generated fibrations.  Its instance is opt-in through
`open scoped TopCat.modelCategory`.
-/

@[expose] public section

open HomotopicalAlgebra

universe u

namespace TopCat

/-- The model-category structure on `TopCat` with weak homotopy
equivalences, boundary-generated cofibrations, and horn-generated fibrations.
Use `open scoped TopCat.modelCategory` to install it as an instance. -/
@[instance_reducible]
noncomputable def modelCategory : ModelCategory TopCat.{u} :=
  modelCategoryFromSSet
    horn_llp_le_weakHomotopyEquivalences
    SSet.KanComplex.I_rlp_to_W_kanRestricted
    SSet.modelCategoryQuillen.J_rlp_inf_W_le_I_rlp

namespace modelCategory

/-- Opt-in model-category instance on `TopCat`. -/
noncomputable scoped instance instModelCategory :
    ModelCategory TopCat.{u} :=
  TopCat.modelCategory

end modelCategory
end TopCat
