/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.TestingBoundaryRecognition
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCellSmallObject
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Genuine saturation of all original weak marked monos

The full weak-mono class is a literal left lifting class: test the native
cotensor boundaries of every intrinsic target, together with the original
marked mono-right maps. This proves closure under original pushouts,
coproducts, retracts and all native transfinite compositions. The test
class here ranges over all targets; no uniform smallness or factorization
hypothesis is concealed in this saturation theorem.
-/

noncomputable section
universe u t
open CategoryTheory MorphismProperty

namespace SSet.Marked

/-- The full actual Cartesian cotensor tests include the original mono-right maps to enforce monicity. -/
def cartesianFullBoundaryTests (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  (monomorphisms (Over (max B))).rlp ⊔ cartesianCotensorBoundaryTests B

/-- The actual dual class retains the same original mono-right maps. -/
def cocartesianFullBoundaryTests (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  (monomorphisms (Over (max B))).rlp ⊔ cocartesianCotensorBoundaryTests B

/-- The complete Cartesian weak-mono class equals its actual native lifting class. -/
theorem cartesianTestingTrivialCofibrations_eq_llp (B : SSet.{u}) [Quasicategory B] :
    cartesianTestingTrivialCofibrations B = (cartesianFullBoundaryTests B).llp := by
  ext X Y i
  rw [cartesianTestingTrivialCofibrations_iff_cotensor]
  have hm := (congrArg (fun W => W i) (CellSmallness.over_mono_isWeakFactorizationSystem B).llp).to_iff
  constructor
  · rintro ⟨hi, hc⟩ A D f (hf | hf)
    · exact (hm.mpr hi) f hf
    · exact hc f hf
  · intro h
    exact ⟨hm.mp (fun {A D} f hf => h f (Or.inl hf)), fun {A D} f hf => h f (Or.inr hf)⟩

/-- The full cocartesian weak-mono class has the same exact native lifting characterization. -/
theorem cocartesianTestingTrivialCofibrations_eq_llp (B : SSet.{u}) [Quasicategory B] :
    cocartesianTestingTrivialCofibrations B = (cocartesianFullBoundaryTests B).llp := by
  ext X Y i
  rw [cocartesianTestingTrivialCofibrations_iff_cotensor]
  have hm := (congrArg (fun W => W i) (CellSmallness.over_mono_isWeakFactorizationSystem B).llp).to_iff
  constructor
  · rintro ⟨hi, hc⟩ A D f (hf | hf)
    · exact (hm.mpr hi) f hf
    · exact hc f hf
  · intro h
    exact ⟨hm.mp (fun {A D} f hf => h f (Or.inl hf)), fun {A D} f hf => h f (Or.inr hf)⟩

/-- Every original Cartesian testing fibration has exactly the whole weak-mono left class. -/
theorem cartesianTestingFibrations_llp (B : SSet.{u}) [Quasicategory B] :
    (cartesianTestingFibrations B).llp = cartesianTestingTrivialCofibrations B := by
  unfold cartesianTestingFibrations
  rw [cartesianTestingTrivialCofibrations_eq_llp, llp_rlp_llp]

/-- The original dual testing fibrations recover the full actual weak-mono left class. -/
theorem cocartesianTestingFibrations_llp (B : SSet.{u}) [Quasicategory B] :
    (cocartesianTestingFibrations B).llp = cocartesianTestingTrivialCofibrations B := by
  unfold cocartesianTestingFibrations
  rw [cocartesianTestingTrivialCofibrations_eq_llp, llp_rlp_llp]

/-- All original Cartesian weak marked monos are stable under actual native pushouts. -/
theorem cartesianTestingTrivialCofibrations_isStableUnderCobaseChange (B : SSet.{u}) [Quasicategory B] :
    (cartesianTestingTrivialCofibrations B).IsStableUnderCobaseChange := by
  rw [cartesianTestingTrivialCofibrations_eq_llp]
  infer_instance

/-- The whole original dual weak-mono class also survives its native pushouts. -/
theorem cocartesianTestingTrivialCofibrations_isStableUnderCobaseChange (B : SSet.{u}) [Quasicategory B] :
    (cocartesianTestingTrivialCofibrations B).IsStableUnderCobaseChange := by
  rw [cocartesianTestingTrivialCofibrations_eq_llp]
  infer_instance

/-- All native coproducts preserve the original full Cartesian weak-mono class. -/
theorem cartesianTestingTrivialCofibrations_isStableUnderCoproducts (B : SSet.{u}) [Quasicategory B] :
    (cartesianTestingTrivialCofibrations B).IsStableUnderCoproducts.{t} := by
  rw [cartesianTestingTrivialCofibrations_eq_llp]
  infer_instance

/-- Actual native coproducts preserve the full dual weak-mono class. -/
theorem cocartesianTestingTrivialCofibrations_isStableUnderCoproducts (B : SSet.{u}) [Quasicategory B] :
    (cocartesianTestingTrivialCofibrations B).IsStableUnderCoproducts.{t} := by
  rw [cocartesianTestingTrivialCofibrations_eq_llp]
  infer_instance

/-- Every original transfinite composition retains full Cartesian mapping weakness and monicity. -/
theorem cartesianTestingTrivialCofibrations_isStableUnderTransfiniteComposition (B : SSet.{u}) [Quasicategory B] :
    (cartesianTestingTrivialCofibrations B).IsStableUnderTransfiniteComposition.{t} := by
  exact IsStableUnderTransfiniteComposition.of_llp_eq _ _
    (cartesianTestingTrivialCofibrations_eq_llp B).symm

/-- The same complete original-universe dual class is stable under native transfinite composition. -/
theorem cocartesianTestingTrivialCofibrations_isStableUnderTransfiniteComposition (B : SSet.{u}) [Quasicategory B] :
    (cocartesianTestingTrivialCofibrations B).IsStableUnderTransfiniteComposition.{t} := by
  exact IsStableUnderTransfiniteComposition.of_llp_eq _ _
    (cocartesianTestingTrivialCofibrations_eq_llp B).symm

/-- Original arrow retracts retain every Cartesian weak-mono test. -/
theorem cartesianTestingTrivialCofibrations_isStableUnderRetracts (B : SSet.{u}) [Quasicategory B] :
    (cartesianTestingTrivialCofibrations B).IsStableUnderRetracts := by
  rw [cartesianTestingTrivialCofibrations_eq_llp]
  infer_instance

/-- The full original dual class retains native arrow retracts as well. -/
theorem cocartesianTestingTrivialCofibrations_isStableUnderRetracts (B : SSet.{u}) [Quasicategory B] :
    (cocartesianTestingTrivialCofibrations B).IsStableUnderRetracts := by
  rw [cocartesianTestingTrivialCofibrations_eq_llp]
  infer_instance

end SSet.Marked
