/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCotensor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntrinsicOverMappingRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.LocalTestingClasses
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Full weak marked-mono tests are actual cotensor boundary lifts

Into each intrinsically marked target, every original marked mono has a
Kan mapping restriction. Its weakness is therefore exactly lifting every
original scalar boundary. The actual cotensor adjunction transposes those
whole squares to original slice maps. This detects all weak marked monos,
without restricting their source sizes or assuming a marked model.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- The original cotensor boundary restriction in the supplied marked slice. -/
def overCotensorBoundary (Z : Marked.{u}) (target : Over Z) (n : ℕ) :
    (overCotensor Z (Δ[n] : SSet.{u})).obj target ⟶
      (overCotensor Z (boundary.{u} n : SSet.{u})).obj target :=
  ((overCotensorLeft Z target).map (boundary.{u} n).ι).unop

/-- Whole original cotensor boundary lifting is precisely scalar boundary lifting of the same native marked
  mapping restriction. -/
theorem overCotensorBoundary_lifting_iff {Z : Marked.{u}} {X X' : Over Z}
    (i : X ⟶ X') (target : Over Z) (n : ℕ) :
    HasLiftingProperty i (overCotensorBoundary Z target n) ↔
      HasLiftingProperty (boundary.{u} n).ι ((overMappingFunctor .maximal Z target).map i.op) := by
  exact (HasLiftingProperty.iff_op).trans
    ((overCotensorMappingAdjunction Z target).hasLiftingProperty_iff _ i.op)

/-- The complete original Cartesian target-and-boundary testing class uses every actual intrinsic target. -/
def cartesianCotensorBoundaryTests (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  ⨆ target : CartesianOver B, ofHoms (overCotensorBoundary (max B) target.obj)

/-- The dual complete class uses the original cocartesian targets and the same scalar boundaries. -/
def cocartesianCotensorBoundaryTests (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  ⨆ target : CocartesianOver B, ofHoms (overCotensorBoundary (max B) target.obj)

/-- An original slice map lifts every Cartesian cotensor boundary precisely when all of its native target
  restrictions have scalar boundary RLP. -/
theorem cartesianCotensorBoundaryTests_llp_iff {B : SSet.{u}} {X X' : Over (max B)} (i : X ⟶ X') :
    (cartesianCotensorBoundaryTests B).llp i ↔ ∀ target : CartesianOver B,
      modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) target.obj).map i.op) := by
  constructor
  · intro h target A D a ha
    obtain ⟨n⟩ := ha
    exact (overCotensorBoundary_lifting_iff i target.obj n).mp
      (h _ (by simp only [cartesianCotensorBoundaryTests, iSup_iff]; exact ⟨target, ofHoms.mk n⟩))
  · intro h A D a ha
    simp only [cartesianCotensorBoundaryTests, iSup_iff] at ha
    obtain ⟨target, ⟨n⟩⟩ := ha
    exact (overCotensorBoundary_lifting_iff i target.obj n).mpr
      (h target _ (modelCategoryQuillen.boundary_ι_mem_I n))

/-- The same whole original cotensor lifting test has its native dual mapping-boundary interpretation. -/
theorem cocartesianCotensorBoundaryTests_llp_iff {B : SSet.{u}} {X X' : Over (max B)} (i : X ⟶ X') :
    (cocartesianCotensorBoundaryTests B).llp i ↔ ∀ target : CocartesianOver B,
      modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) target.obj).map i.op) := by
  constructor
  · intro h target A D a ha
    obtain ⟨n⟩ := ha
    exact (overCotensorBoundary_lifting_iff i target.obj n).mp
      (h _ (by simp only [cocartesianCotensorBoundaryTests, iSup_iff]; exact ⟨target, ofHoms.mk n⟩))
  · intro h A D a ha
    simp only [cocartesianCotensorBoundaryTests, iSup_iff] at ha
    obtain ⟨target, ⟨n⟩⟩ := ha
    exact (overCotensorBoundary_lifting_iff i target.obj n).mpr
      (h target _ (modelCategoryQuillen.boundary_ι_mem_I n))

/-- All original Cartesian weak marked monos are exactly the monic maps satisfying the genuine cotensor
  boundary lifts. -/
theorem cartesianTestingTrivialCofibrations_iff_cotensor {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X ⟶ X') :
    cartesianTestingTrivialCofibrations B i ↔
      Mono i ∧ (cartesianCotensorBoundaryTests B).llp i := by
  constructor
  · rintro ⟨hm, hw⟩
    let _ : Mono i := hm
    refine ⟨hm, (cartesianCotensorBoundaryTests_llp_iff i).mpr ?_⟩
    intro target
    let _ : Fibration ((overMappingFunctor .maximal (max B) target.obj).map i.op) :=
      overMappingFunctor_cartesian_map_fibration i target
    exact (modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration _).mpr
      ((cartesianWeakEquivalences_iff i).mp hw target)
  · rintro ⟨hm, h⟩
    refine ⟨hm, (cartesianWeakEquivalences_iff i).mpr ?_⟩
    intro target
    exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
      ((cartesianCotensorBoundaryTests_llp_iff i).mp h target)

/-- The same full weak-mono characterization holds for every original cocartesian target. -/
theorem cocartesianTestingTrivialCofibrations_iff_cotensor {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X ⟶ X') :
    cocartesianTestingTrivialCofibrations B i ↔
      Mono i ∧ (cocartesianCotensorBoundaryTests B).llp i := by
  constructor
  · rintro ⟨hm, hw⟩
    let _ : Mono i := hm
    refine ⟨hm, (cocartesianCotensorBoundaryTests_llp_iff i).mpr ?_⟩
    intro target
    let _ : Fibration ((overMappingFunctor .maximal (max B) target.obj).map i.op) :=
      overMappingFunctor_cocartesian_map_fibration i target
    exact (modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration _).mpr
      ((cocartesianWeakEquivalences_iff i).mp hw target)
  · rintro ⟨hm, h⟩
    refine ⟨hm, (cocartesianWeakEquivalences_iff i).mpr ?_⟩
    intro target
    exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
      ((cocartesianCotensorBoundaryTests_llp_iff i).mp h target)

end SSet.Marked
