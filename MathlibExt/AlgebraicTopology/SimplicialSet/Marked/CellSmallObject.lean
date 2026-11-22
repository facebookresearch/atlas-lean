/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CellSourcePresentability
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MonoFactorization
import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# The actual original-universe marked cell small-object argument

The genuine presentability bound on every original source proves the
required preservation of the actual transfinite cell colimits. The marked
carrier has the required original-universe colimits and local Hom bounds.
Thus the original Cartesian and cocartesian cell families permit the
native small-object argument, giving their actual functorial weak
factorization systems. No marked weak-equivalence class is assumed.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CellSmallness

local instance : Fact cardinal.{u}.IsRegular := cardinal_regular

/-- The actual source-rank ordinal is nonempty at the original value universe. -/
theorem ordinal_nonempty : Nonempty cardinal.{u}.ord.ToType := by
  apply Cardinal.mk_ne_zero_iff.mp
  rw [Cardinal.mk_toType, Cardinal.card_ord]
  exact (lt_of_lt_of_le Cardinal.aleph0_pos aleph0_le_cardinal).ne'

/-- The original well-founded source-rank ordinal has its native least stage. -/
def ordinalOrderBot : OrderBot cardinal.{u}.ord.ToType := by
  let _ : Nonempty cardinal.{u}.ord.ToType := ordinal_nonempty
  exact WellFoundedLT.toOrderBot _

/-- Use the actual native least source-rank stage in this small-object construction. -/
local instance : OrderBot cardinal.{u}.ord.ToType := ordinalOrderBot

/-- Genuine source presentability verifies the original Cartesian cell small-object hypotheses. -/
theorem cartesian_isCardinalForSmallObjectArgument :
    IsCardinalForSmallObjectArgument cartesianCells.{u} cardinal.{u} where
  isSmall := cartesianCells_isSmall
  preservesColimit {A B X Y} i hi f hf := by
    obtain ⟨s⟩ := hi
    let _ : IsCardinalPresentable (cartesianCell.{u} s).left cardinal.{u} :=
      cartesian_source_presentable s
    let _ : PreservesColimitsOfShape cardinal.{u}.ord.ToType
        (coyoneda.obj (op (cartesianCell.{u} s).left)) :=
      preservesColimitsOfShape_of_isCardinalPresentable _ cardinal.{u} _
    infer_instance

/-- The same actual source bound verifies every cocartesian transfinite-colimit hypothesis. -/
theorem cocartesian_isCardinalForSmallObjectArgument :
    IsCardinalForSmallObjectArgument cocartesianCells.{u} cardinal.{u} where
  isSmall := cocartesianCells_isSmall
  preservesColimit {A B X Y} i hi f hf := by
    obtain ⟨s⟩ := hi
    let _ : IsCardinalPresentable (cocartesianCell.{u} s).left cardinal.{u} :=
      cocartesian_source_presentable s
    let _ : PreservesColimitsOfShape cardinal.{u}.ord.ToType
        (coyoneda.obj (op (cocartesianCell.{u} s).left)) :=
      preservesColimitsOfShape_of_isCardinalPresentable _ cardinal.{u} _
    infer_instance

/-- The original Cartesian cell family genuinely permits the small-object argument in its value universe. -/
theorem cartesian_hasSmallObjectArgument : HasSmallObjectArgument.{u} cartesianCells.{u} :=
  ⟨cardinal.{u}, cardinal_regular, ordinalOrderBot, cartesian_isCardinalForSmallObjectArgument⟩

/-- The dual family permits the same original-universe construction. -/
theorem cocartesian_hasSmallObjectArgument : HasSmallObjectArgument.{u} cocartesianCells.{u} :=
  ⟨cardinal.{u}, cardinal_regular, ordinalOrderBot, cocartesian_isCardinalForSmallObjectArgument⟩

/-- The native original Cartesian cell small-object construction gives its actual functorial factorization data. -/
def cartesianFunctorialFactorizationData :
    FunctorialFactorizationData cartesianCells.{u}.rlp.llp cartesianCells.{u}.rlp := by
  let _ : HasSmallObjectArgument.{u} cartesianCells.{u} := cartesian_hasSmallObjectArgument
  exact functorialFactorizationData _ _

/-- The native dual small-object factorization keeps the same original marked carrier. -/
def cocartesianFunctorialFactorizationData :
    FunctorialFactorizationData cocartesianCells.{u}.rlp.llp cocartesianCells.{u}.rlp := by
  let _ : HasSmallObjectArgument.{u} cocartesianCells.{u} := cocartesian_hasSmallObjectArgument
  exact functorialFactorizationData _ _

/-- The actual Cartesian cells and their native lifting classes form a genuine weak factorization system. -/
theorem cartesian_isWeakFactorizationSystem :
    IsWeakFactorizationSystem cartesianCells.{u}.rlp.llp cartesianCells.{u}.rlp := by
  let _ : HasFunctorialFactorization cartesianCells.{u}.rlp.llp cartesianCells.{u}.rlp :=
    ⟨⟨cartesianFunctorialFactorizationData⟩⟩
  exact IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hi p hp)

/-- The original dual cell lifting pair is also a genuine native weak factorization system. -/
theorem cocartesian_isWeakFactorizationSystem :
    IsWeakFactorizationSystem cocartesianCells.{u}.rlp.llp cocartesianCells.{u}.rlp := by
  let _ : HasFunctorialFactorization cocartesianCells.{u}.rlp.llp cocartesianCells.{u}.rlp :=
    ⟨⟨cocartesianFunctorialFactorizationData⟩⟩
  exact IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hi p hp)

/-- The genuine Cartesian small-object left class consists of original marked monomorphisms. -/
theorem cartesian_left_le_monomorphisms : cartesianCells.{u}.rlp.llp ≤ monomorphisms Marked.{u} := by
  calc
    _ ≤ (monomorphisms Marked.{u}).rlp.llp := antitone_llp (antitone_rlp cartesianCells_le_monomorphisms)
    _ = _ := mono_isWeakFactorizationSystem.llp

/-- The same original monomorphism bound holds for the cocartesian small-object left class. -/
theorem cocartesian_left_le_monomorphisms : cocartesianCells.{u}.rlp.llp ≤ monomorphisms Marked.{u} := by
  calc
    _ ≤ (monomorphisms Marked.{u}).rlp.llp := antitone_llp (antitone_rlp cocartesianCells_le_monomorphisms)
    _ = _ := mono_isWeakFactorizationSystem.llp

end SSet.Marked.CellSmallness
