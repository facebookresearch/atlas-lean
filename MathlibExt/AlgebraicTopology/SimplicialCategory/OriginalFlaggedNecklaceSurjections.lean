/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceNormalPaths

/-!
# Actual surjections between whole original flanked necklaces

The complete last flag forces every original target vertex to have an
original source vertex. The complete first flags give the exact image
of the original joint set. These statements concern the SAME original
morphism and do not assume an outcome for its input map.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBead.TerminalFlag
open SSet.OriginalNecklace

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The whole original last flag forces the same actual ordinal map to be surjective. -/
theorem flanked_operator_surjective {T U : Object K x y q} (f : T ⟶ U)
    (hU : IsFlanked U) :
    Function.Surjective f.necklaceMap.operator.toOrderHom := by
  intro j
  have hflags : f.necklaceMap.operator.toOrderHom.uliftMap ''
      (T.coefficient.obj (Fin.last q.unop.len)).I =
        (U.coefficient.obj (Fin.last q.unop.len)).I := by
    have h := congrArg (fun p : (coefficientObject.{u} U.necklace.dimension).obj q =>
      (p.obj (Fin.last q.unop.len)).I) f.flags
    exact h
  have hj : ULift.up.{u} j ∈ f.necklaceMap.operator.toOrderHom.uliftMap ''
      (T.coefficient.obj (Fin.last q.unop.len)).I := by
    rw [hflags, hU.2]
    exact Set.mem_univ _
  obtain ⟨i, _hi, hij⟩ := hj
  exact ⟨i.down, congrArg ULift.down hij⟩

/-- The SAME whole original operator between flanked objects is genuinely epi. -/
theorem flanked_operator_epi {T U : Object K x y q} (f : T ⟶ U)
    (hU : IsFlanked U) : Epi f.necklaceMap.operator :=
  (SimplexCategory.epi_iff_surjective (f := f.necklaceMap.operator)).mpr
    (flanked_operator_surjective f hU)

/-- The entire original first flags give precisely the image of the SAME original joint set. -/
theorem flanked_joint_image {T U : Object K x y q} (f : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (j : Fin (U.necklace.dimension + 1)) :
    j ∈ U.necklace.joints ↔
      ∃ i ∈ T.necklace.joints, f.necklaceMap.operator.toOrderHom i = j := by
  have hflags : f.necklaceMap.operator.toOrderHom.uliftMap '' (T.coefficient.obj 0).I =
      (U.coefficient.obj 0).I := by
    have h := congrArg (fun p : (coefficientObject.{u} U.necklace.dimension).obj q =>
      (p.obj 0).I) f.flags
    exact h
  constructor
  · intro hj
    have hi : ULift.up.{u} j ∈ f.necklaceMap.operator.toOrderHom.uliftMap ''
        (T.coefficient.obj 0).I := by
      rw [hflags]
      exact (hU.1 j).mpr hj
    obtain ⟨i, hi, hij⟩ := hi
    exact ⟨i.down, (hT.1 i.down).mp hi, congrArg ULift.down hij⟩
  · rintro ⟨i, hi, hij⟩
    apply (hU.1 j).mp
    rw [← hflags]
    exact ⟨ULift.up.{u} i, (hT.1 i).mpr hi, ULift.ext hij⟩

/-- Every SAME original source joint maps to an actual original target joint. -/
theorem flanked_joint_maps {T U : Object K x y q} (f : T ⟶ U)
    (hT : IsFlanked T) (hU : IsFlanked U) (i : Fin (T.necklace.dimension + 1))
    (hi : i ∈ T.necklace.joints) :
    f.necklaceMap.operator.toOrderHom i ∈ U.necklace.joints :=
  (flanked_joint_image f hT hU _).mpr ⟨i, hi, rfl⟩

/-- Every original flag follows the same entire vertex surjection. -/
theorem flanked_flags {T U : Object K x y q} (f : T ⟶ U)
    (t : Fin (q.unop.len + 1)) :
    (U.coefficient.obj t).I =
      f.necklaceMap.operator.toOrderHom.uliftMap '' (T.coefficient.obj t).I :=
  (congrArg (fun p : (coefficientObject.{u} U.necklace.dimension).obj q =>
    (p.obj t).I) f.flags).symm

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
