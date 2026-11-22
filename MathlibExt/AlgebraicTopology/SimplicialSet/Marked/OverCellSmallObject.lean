/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CellSmallObject
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCellSourcePresentability
import MathlibExt.CategoryTheory.MorphismProperty.OverFactorization

/-!
# Actual small-object weak factorization systems over every original base

The actual base-indexed cells have source presentability at the same
original value-universe rank. Their native transfinite cell colimits
therefore satisfy the small-object hypotheses in the marked slice.
This gives genuine functorial Cartesian and cocartesian cell weak
factorization systems for every original base. When the base is a
quasicategory, their actual terminal factors have exactly the original
intrinsic relative markings; no Kan-base hypothesis is added.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CellSmallness

local instance : Fact cardinal.{u}.IsRegular := cardinal_regular
/-- The slice construction uses the same native least stage of the original source-rank ordinal. -/
local instance : OrderBot cardinal.{u}.ord.ToType := ordinalOrderBot

/-- The actual Cartesian slice sources preserve the required original transfinite cell colimits. -/
theorem cartesian_over_isCardinalForSmallObjectArgument (B : SSet.{u}) :
    IsCardinalForSmallObjectArgument (cartesianCellsOver B) cardinal.{u} where
  isSmall := cartesianCellsOver_isSmall B
  preservesColimit {A D X Y} i hi f hf := by
    obtain ⟨s⟩ := hi
    let _ : IsCardinalPresentable (Over.mk ((cartesianCell.{u} s.1).hom ≫ s.2)) cardinal.{u} :=
      cartesian_over_source_presentable B s
    let _ : PreservesColimitsOfShape cardinal.{u}.ord.ToType
        (coyoneda.obj (op (Over.mk ((cartesianCell.{u} s.1).hom ≫ s.2)))) :=
      preservesColimitsOfShape_of_isCardinalPresentable _ cardinal.{u} _
    infer_instance

/-- The dual actual marked slice cell sources meet the same original-universe preservation requirement. -/
theorem cocartesian_over_isCardinalForSmallObjectArgument (B : SSet.{u}) :
    IsCardinalForSmallObjectArgument (cocartesianCellsOver B) cardinal.{u} where
  isSmall := cocartesianCellsOver_isSmall B
  preservesColimit {A D X Y} i hi f hf := by
    obtain ⟨s⟩ := hi
    let _ : IsCardinalPresentable (Over.mk ((cocartesianCell.{u} s.1).hom ≫ s.2)) cardinal.{u} :=
      cocartesian_over_source_presentable B s
    let _ : PreservesColimitsOfShape cardinal.{u}.ord.ToType
        (coyoneda.obj (op (Over.mk ((cocartesianCell.{u} s.1).hom ≫ s.2)))) :=
      preservesColimitsOfShape_of_isCardinalPresentable _ cardinal.{u} _
    infer_instance

/-- The genuine Cartesian slice family permits the small-object argument over every original base. -/
theorem cartesian_over_hasSmallObjectArgument (B : SSet.{u}) :
    HasSmallObjectArgument.{u} (cartesianCellsOver B) :=
  ⟨cardinal.{u}, cardinal_regular, ordinalOrderBot, cartesian_over_isCardinalForSmallObjectArgument B⟩

/-- The dual slice family permits its actual original-universe small-object construction. -/
theorem cocartesian_over_hasSmallObjectArgument (B : SSet.{u}) :
    HasSmallObjectArgument.{u} (cocartesianCellsOver B) :=
  ⟨cardinal.{u}, cardinal_regular, ordinalOrderBot, cocartesian_over_isCardinalForSmallObjectArgument B⟩

/-- The actual native functorial Cartesian cell factorization in the original marked slice. -/
def cartesianOverFunctorialFactorizationData (B : SSet.{u}) :
    FunctorialFactorizationData (cartesianCellsOver B).rlp.llp (cartesianCellsOver B).rlp := by
  let _ : HasSmallObjectArgument.{u} (cartesianCellsOver B) := cartesian_over_hasSmallObjectArgument B
  exact functorialFactorizationData _ _

/-- The original cocartesian slice gets its native functorial factorization from the proved source bound. -/
def cocartesianOverFunctorialFactorizationData (B : SSet.{u}) :
    FunctorialFactorizationData (cocartesianCellsOver B).rlp.llp (cocartesianCellsOver B).rlp := by
  let _ : HasSmallObjectArgument.{u} (cocartesianCellsOver B) := cocartesian_over_hasSmallObjectArgument B
  exact functorialFactorizationData _ _

/-- The original Cartesian slice lifting classes genuinely form a weak factorization system. -/
theorem cartesian_over_isWeakFactorizationSystem (B : SSet.{u}) :
    IsWeakFactorizationSystem (cartesianCellsOver B).rlp.llp (cartesianCellsOver B).rlp := by
  let _ : HasFunctorialFactorization (cartesianCellsOver B).rlp.llp (cartesianCellsOver B).rlp :=
    ⟨⟨cartesianOverFunctorialFactorizationData B⟩⟩
  exact IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hi p hp)

/-- The dual original slice lifting pair is an actual native weak factorization system. -/
theorem cocartesian_over_isWeakFactorizationSystem (B : SSet.{u}) :
    IsWeakFactorizationSystem (cocartesianCellsOver B).rlp.llp (cocartesianCellsOver B).rlp := by
  let _ : HasFunctorialFactorization (cocartesianCellsOver B).rlp.llp (cocartesianCellsOver B).rlp :=
    ⟨⟨cocartesianOverFunctorialFactorizationData B⟩⟩
  exact IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hi p hp)

/-- The native marked mono weak factorization system transfers to the original marked slice. -/
theorem over_mono_isWeakFactorizationSystem (B : SSet.{u}) :
    IsWeakFactorizationSystem (monomorphisms (Over (max B))) (monomorphisms (Over (max B))).rlp := by
  let _ : IsWeakFactorizationSystem (monomorphisms Marked.{u}) (monomorphisms Marked.{u}).rlp :=
    mono_isWeakFactorizationSystem
  have h := IsWeakFactorizationSystem.over (monomorphisms Marked.{u})
    (monomorphisms Marked.{u}).rlp (max B)
  have hm : (monomorphisms Marked.{u}).inverseImage (Over.forget (max B)) =
      monomorphisms (Over (max B)) := by
    ext X Y f
    constructor
    · intro hf
      let _ : Mono f.left := hf
      exact Over.mono_of_mono_left f
    · intro hf
      let _ : Mono f := hf
      exact Over.mono_left_of_mono f
  rw [hm] at h
  rw [h.rlp]
  exact h

/-- Every genuine Cartesian slice cell left factor is an original marked monomorphism. -/
theorem cartesian_over_left_le_monomorphisms (B : SSet.{u}) :
    (cartesianCellsOver B).rlp.llp ≤ monomorphisms (Over (max B)) := by
  calc
    _ ≤ (monomorphisms (Over (max B))).rlp.llp :=
      antitone_llp (antitone_rlp (cartesianCellsOver_le_monomorphisms B))
    _ = _ := (over_mono_isWeakFactorizationSystem B).llp

/-- The same original monomorphism assertion holds for the cocartesian slice left factors. -/
theorem cocartesian_over_left_le_monomorphisms (B : SSet.{u}) :
    (cocartesianCellsOver B).rlp.llp ≤ monomorphisms (Over (max B)) := by
  calc
    _ ≤ (monomorphisms (Over (max B))).rlp.llp :=
      antitone_llp (antitone_rlp (cocartesianCellsOver_le_monomorphisms B))
    _ = _ := (over_mono_isWeakFactorizationSystem B).llp

/-- The actual Cartesian small-object factorization of the original terminal map. -/
def cartesianReplacementData {B : SSet.{u}} (X : Over (max B)) :
    MapFactorizationData (cartesianCellsOver B).rlp.llp (cartesianCellsOver B).rlp
      (Over.mkIdTerminal.from X) :=
  (cartesianOverFunctorialFactorizationData B).factorizationData _

/-- The dual original terminal factorization has its native cocartesian cell lifting target. -/
def cocartesianReplacementData {B : SSet.{u}} (X : Over (max B)) :
    MapFactorizationData (cocartesianCellsOver B).rlp.llp (cocartesianCellsOver B).rlp
      (Over.mkIdTerminal.from X) :=
  (cocartesianOverFunctorialFactorizationData B).factorizationData _

/-- The actual Cartesian terminal factor is intrinsically marked over the original quasicategory base. -/
theorem cartesianReplacementData_intrinsic {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) : cartesianObjects B (cartesianReplacementData X).Z := by
  let r := cartesianReplacementData X
  apply (cartesianCellsOver_terminal_rlp_iff r.Z).mp
  have hp : r.p = Over.mkIdTerminal.from r.Z := Over.mkIdTerminal.hom_ext _ _
  exact hp ▸ r.hp

/-- The original dual terminal factor is a genuine intrinsically marked cocartesian fibration. -/
theorem cocartesianReplacementData_intrinsic {B : SSet.{u}} [Quasicategory B]
    (X : Over (max B)) : cocartesianObjects B (cocartesianReplacementData X).Z := by
  let r := cocartesianReplacementData X
  apply (cocartesianCellsOver_terminal_rlp_iff r.Z).mp
  have hp : r.p = Over.mkIdTerminal.from r.Z := Over.mkIdTerminal.hom_ext _ _
  exact hp ▸ r.hp

/-- The actual original Cartesian replacement unit is monic. -/
theorem cartesianReplacementData_mono {B : SSet.{u}} (X : Over (max B)) :
    Mono (cartesianReplacementData X).i :=
  cartesian_over_left_le_monomorphisms B _ (cartesianReplacementData X).hi

/-- The dual native replacement unit preserves the original source as a marked monomorphism. -/
theorem cocartesianReplacementData_mono {B : SSet.{u}} (X : Over (max B)) :
    Mono (cocartesianReplacementData X).i :=
  cocartesian_over_left_le_monomorphisms B _ (cocartesianReplacementData X).hi

end SSet.Marked.CellSmallness
