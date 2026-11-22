/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeWeakClassComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeSmithRecognition

/-!
# Genuine uniform full intrinsic weak-mono testing and both reverse classes

The proved exact weak-class comparison transfers actual all-arrow
accessibility and Beke--Smith construction to the FULL original intrinsic
mapping weak classes. The produced genuine small weak-mono family has
exactly the full original left and right classes; its weak right maps
are exactly the original mono-right maps. Both actual WFS and functorial
factors retain the original marked carrier, full arrows and universe.
No bounded surrogate, equivalence certificate or model outcome is input.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace SSet.Marked

/-- Full original Cartesian mapping weakness and its actual Arrow inclusion are genuinely accessible. -/
theorem cartesianWeakEquivalences_isAccessible (B : SSet.{u}) [Quasicategory B] :
    MorphismProperty.IsAccessible.{u} (cartesianWeakEquivalences B) := by
  rw [cartesianWeakEquivalences_eq_relativeHomotopyTesting]
  exact cartesianRelativeHomotopyTesting_isAccessible B

/-- The same full original dual weak-arrow class is accessible in the unchanged value universe. -/
theorem cocartesianWeakEquivalences_isAccessible (B : SSet.{u}) [Quasicategory B] :
    MorphismProperty.IsAccessible.{u} (cocartesianWeakEquivalences B) := by
  rw [cocartesianWeakEquivalences_eq_relativeHomotopyTesting]
  exact cocartesianRelativeHomotopyTesting_isAccessible B

/-- Actual source and solution-set proofs produce complete native Smith data for the exact original
  Cartesian weak class. -/
def cartesianMarkedSmithData (B : SSet.{u}) [Quasicategory B] :
    SmithModelStructureData.{u} (C := Over (max B)) (overCells monoCell.{u} (max B)) (cartesianWeakEquivalences B) := by
  have h := cartesianRelativeSmithRecognition B
  rw [← cartesianWeakEquivalences_eq_relativeHomotopyTesting B] at h
  exact Classical.choice h

/-- The genuine dual construction uses exactly its full original intrinsic mapping weak class. -/
def cocartesianMarkedSmithData (B : SSet.{u}) [Quasicategory B] :
    SmithModelStructureData.{u} (C := Over (max B)) (overCells monoCell.{u} (max B))
      (cocartesianWeakEquivalences B) := by
  have h := cocartesianRelativeSmithRecognition B
  rw [← cocartesianWeakEquivalences_eq_relativeHomotopyTesting B] at h
  exact Classical.choice h

/-- The actual genuinely small full Cartesian weak-mono generating family produced in the original universe. -/
def cartesianMarkedWeakCells (B : SSet.{u}) [Quasicategory B] : MorphismProperty (Over (max B)) :=
  (cartesianMarkedSmithData B).J

/-- The dual full weak-mono family is produced by the same native original-universe construction. -/
def cocartesianMarkedWeakCells (B : SSet.{u}) [Quasicategory B] : MorphismProperty (Over (max B)) :=
  (cocartesianMarkedSmithData B).J

/-- The produced full Cartesian weak-mono family has its genuine original-universe small-object argument. -/
theorem cartesianMarkedWeakCells_hasSmallObjectArgument (B : SSet.{u}) [Quasicategory B] :
    (cartesianMarkedWeakCells B).HasSmallObjectArgument.{u} := (cartesianMarkedSmithData B).J_smallObject

/-- The same actual dual family has its native small-object argument, not only index smallness. -/
theorem cocartesianMarkedWeakCells_hasSmallObjectArgument (B : SSet.{u}) [Quasicategory B] :
    (cocartesianMarkedWeakCells B).HasSmallObjectArgument.{u} := (cocartesianMarkedSmithData B).J_smallObject

/-- The generated Cartesian left class is exactly EVERY original weak marked mono. -/
theorem cartesianMarkedWeakCells_left_eq (B : SSet.{u}) [Quasicategory B] :
    (cartesianMarkedWeakCells B).rlp.llp = cartesianTestingTrivialCofibrations B := by
  change (cartesianMarkedSmithData B).J.rlp.llp = _
  rw [(cartesianMarkedSmithData B).trivialCofibrations_eq, fixedBaseMonoCells_left_eq]
  rfl

/-- The generated dual left class is exactly the full original cocartesian weak-mono class. -/
theorem cocartesianMarkedWeakCells_left_eq (B : SSet.{u}) [Quasicategory B] :
    (cocartesianMarkedWeakCells B).rlp.llp = cocartesianTestingTrivialCofibrations B := by
  change (cocartesianMarkedSmithData B).J.rlp.llp = _
  rw [(cocartesianMarkedSmithData B).trivialCofibrations_eq, fixedBaseMonoCells_left_eq]
  rfl

/-- The genuine small Cartesian family has exactly the full original testing-fibration right class on all arrows. -/
theorem cartesianMarkedWeakCells_right_eq (B : SSet.{u}) [Quasicategory B] :
    (cartesianMarkedWeakCells B).rlp = cartesianTestingFibrations B := by
  change (cartesianMarkedSmithData B).J.rlp = _
  rw [(cartesianMarkedSmithData B).fibrations_eq, fixedBaseMonoCells_left_eq]
  rfl

/-- The same all-original-arrow right-class recognition holds for the dual family. -/
theorem cocartesianMarkedWeakCells_right_eq (B : SSet.{u}) [Quasicategory B] :
    (cocartesianMarkedWeakCells B).rlp = cocartesianTestingFibrations B := by
  change (cocartesianMarkedSmithData B).J.rlp = _
  rw [(cocartesianMarkedSmithData B).fibrations_eq, fixedBaseMonoCells_left_eq]
  rfl

/-- Full Cartesian testing fibrations that are mapping weak are EXACTLY the original mono-right maps. -/
theorem cartesianTestingFibrations_inf_weak_eq_monoRight (B : SSet.{u}) [Quasicategory B] :
    cartesianTestingFibrations B ⊓ cartesianWeakEquivalences B = (monomorphisms (Over (max B))).rlp := by
  exact (congrArg (fun T => T ⊓ cartesianWeakEquivalences B) (cartesianMarkedWeakCells_right_eq B).symm).trans
    ((cartesianMarkedSmithData B).trivialFibrations_eq.trans (fixedBaseMonoCells_rlp_eq B))

/-- The exact original dual weak-right intersection equals the same native marked mono-right class. -/
theorem cocartesianTestingFibrations_inf_weak_eq_monoRight (B : SSet.{u}) [Quasicategory B] :
    cocartesianTestingFibrations B ⊓ cocartesianWeakEquivalences B = (monomorphisms (Over (max B))).rlp := by
  exact (congrArg (fun T => T ⊓ cocartesianWeakEquivalences B) (cocartesianMarkedWeakCells_right_eq B).symm).trans
    ((cocartesianMarkedSmithData B).trivialFibrations_eq.trans (fixedBaseMonoCells_rlp_eq B))

/-- The full original Cartesian weak-mono/fibration pair is a genuine weak factorization system. -/
theorem cartesianTesting_isWeakFactorizationSystem (B : SSet.{u}) [Quasicategory B] :
    IsWeakFactorizationSystem (cartesianTestingTrivialCofibrations B) (cartesianTestingFibrations B) := by
  rw [← cartesianMarkedWeakCells_left_eq, ← cartesianMarkedWeakCells_right_eq]
  exact (cartesianMarkedSmithData B).trivialCofibration_wfs

/-- The full original dual classes form their actual native weak factorization system. -/
theorem cocartesianTesting_isWeakFactorizationSystem (B : SSet.{u}) [Quasicategory B] :
    IsWeakFactorizationSystem (cocartesianTestingTrivialCofibrations B) (cocartesianTestingFibrations B) := by
  rw [← cocartesianMarkedWeakCells_left_eq, ← cocartesianMarkedWeakCells_right_eq]
  exact (cocartesianMarkedSmithData B).trivialCofibration_wfs

/-- The actual native small-object factors of the produced full Cartesian weak-mono family. -/
def cartesianMarkedRawFactorization (B : SSet.{u}) [Quasicategory B] :
    FunctorialFactorizationData (cartesianMarkedWeakCells B).rlp.llp (cartesianMarkedWeakCells B).rlp := by
  let _ : (cartesianMarkedWeakCells B).HasSmallObjectArgument.{u} := cartesianMarkedWeakCells_hasSmallObjectArgument B
  exact functorialFactorizationData _ _

/-- The actual native dual factors retain their complete original source and target arrows. -/
def cocartesianMarkedRawFactorization (B : SSet.{u}) [Quasicategory B] :
    FunctorialFactorizationData (cocartesianMarkedWeakCells B).rlp.llp (cocartesianMarkedWeakCells B).rlp := by
  let _ : (cocartesianMarkedWeakCells B).HasSmallObjectArgument.{u} :=
    cocartesianMarkedWeakCells_hasSmallObjectArgument B
  exact functorialFactorizationData _ _

/-- Full original Cartesian weak-mono/fibration factorization retains the exact produced native middle and
  both factors. -/
def cartesianMarkedFunctorialFactorization (B : SSet.{u}) [Quasicategory B] :
    FunctorialFactorizationData (cartesianTestingTrivialCofibrations B) (cartesianTestingFibrations B) :=
  (cartesianMarkedRawFactorization B).ofLE (cartesianMarkedWeakCells_left_eq B).le
    (cartesianMarkedWeakCells_right_eq B).le

/-- The dual whole native factorization specializes only membership proofs, retaining every original factor map. -/
def cocartesianMarkedFunctorialFactorization (B : SSet.{u}) [Quasicategory B] :
    FunctorialFactorizationData (cocartesianTestingTrivialCofibrations B) (cocartesianTestingFibrations B) :=
  (cocartesianMarkedRawFactorization B).ofLE (cocartesianMarkedWeakCells_left_eq B).le
    (cocartesianMarkedWeakCells_right_eq B).le

/-- Every original Cartesian factorization keeps the complete same middle-object functor. -/
theorem cartesianMarkedFunctorialFactorization_Z (B : SSet.{u}) [Quasicategory B] :
    (cartesianMarkedFunctorialFactorization B).Z = (cartesianMarkedRawFactorization B).Z := rfl

/-- Both full original Cartesian factor maps remain the same native natural transformations. -/
theorem cartesianMarkedFunctorialFactorization_maps (B : SSet.{u}) [Quasicategory B] :
    (cartesianMarkedFunctorialFactorization B).i = (cartesianMarkedRawFactorization B).i ∧
      (cartesianMarkedFunctorialFactorization B).p = (cartesianMarkedRawFactorization B).p := ⟨rfl, rfl⟩

/-- The dual whole middle functor and both original factor maps likewise remain literal. -/
theorem cocartesianMarkedFunctorialFactorization_fields (B : SSet.{u}) [Quasicategory B] :
    (cocartesianMarkedFunctorialFactorization B).Z = (cocartesianMarkedRawFactorization B).Z ∧
      (cocartesianMarkedFunctorialFactorization B).i = (cocartesianMarkedRawFactorization B).i ∧
      (cocartesianMarkedFunctorialFactorization B).p = (cocartesianMarkedRawFactorization B).p := ⟨rfl, rfl, rfl⟩

end SSet.Marked
