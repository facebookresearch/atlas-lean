/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure
public import MathlibExt.AlgebraicTopology.ModelCategory.Proper

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# Right properness of the selected TopCat model structure

Every topological space is fibrant in the selected, horn-generated TopCat
model structure because its singular simplicial set is Kan.  This file
packages the resulting right properness as named data.  It deliberately does
not install a global or scoped right-properness instance.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen TopCat.modelCategory

universe u

namespace TopCat.modelCategory

set_option linter.defProp false in
/-- The selected TopCat model structure is right proper. This is named data,
not an instance; consumers install it only in the proof scope that needs it.
-/
@[instance_reducible]
noncomputable def rightProper :
    IsRightProper TopCat.{u} :=
  isRightProper_of_all_objects_fibrant (fun X => by
    rw [isFibrant_iff]
    rw [HomotopicalAlgebra.fibration_iff]
    change TopCat.realizedHornInclusions.{u}.rlp (terminal.from X)
    rw [TopCat.hornRLP_iff_toSSet_mem_J_rlp]
    rw [← SSet.modelCategoryQuillen.fibration_iff]
    rw [← isFibrant_iff_of_isTerminal _
      (IsTerminal.isTerminalObj TopCat.toSSet _ terminalIsTerminal)]
    exact TopCat.toSSet_obj_kanComplex X)

end TopCat.modelCategory
