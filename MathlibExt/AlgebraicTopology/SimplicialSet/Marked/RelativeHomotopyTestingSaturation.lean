/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeFibrantCodomainRecognition
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingLeftClass
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingRetracts
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Genuine saturation of the full relative homotopy weak-mono classes

The proved native relative anodyne systems and actual factorization
identify all monic homotopy testing equivalences with the left lifting
class of original completed right maps whose codomains are intrinsic.
Thus full pushout, retract and arbitrary original transfinite closure
follow from actual lifting theory. No smallness of this full test class,
uniform generator or marked model conclusion is assumed.
-/

noncomputable section
universe u t
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace SSet.Marked

/-- The full original Cartesian relative homotopy weak marked-mono class. -/
def cartesianRelativeHomotopyWeakMonos (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  monomorphisms (Over (max B)) ⊓ cartesianRelativeHomotopyTesting B

/-- The same original dual relative homotopy weak marked-mono class. -/
def cocartesianRelativeHomotopyWeakMonos (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  monomorphisms (Over (max B)) ⊓ cocartesianRelativeHomotopyTesting B

/-- Every original Cartesian relative homotopy weak mono is exactly a left lift against the actual completed
  right maps with intrinsic original codomain. -/
theorem cartesianRelativeHomotopyWeakMonos_eq_llp (B : SSet.{u}) [Quasicategory B] :
    cartesianRelativeHomotopyWeakMonos B =
      ((cartesianRelativeBoundaryCells B).rlp ⊓ ofObjectProperty ⊤ (cartesianObjects B)).llp := by
  let J := cartesianRelativeBoundaryCells B
  let An := J.rlp.llp
  let P := relativeIntervalCylinder (max B)
  let _ : P.IsExact.{u} := relativeIntervalCylinder_isExact (max B)
  let _ : P.IsAnodyneSystem.{u} An := cartesianRelativeBoundary_isAnodyneSystem B
  let _ : InitialMonoClass (Over (max B)) := over_initialMonoClass (max B)
  let _ : J.HasSmallObjectArgument.{u} := RelativeBoundarySmallObject.cartesian_hasSmallObjectArgument B
  let _ : HasFactorization An An.rlp := by
    change HasFactorization J.rlp.llp J.rlp.llp.rlp
    rw [rlp_llp_rlp]
    infer_instance
  have hN : An.naiveFibrantObjects = cartesianObjects B := by
    funext Y
    exact propext (cartesianRelativeBoundary_naiveFibrant_iff Y)
  have h := Precylinder.IsAnodyneSystem.testingTrivialCofibrations_eq_llp_naiveFibrantCodomain P An
  change cartesianRelativeHomotopyWeakMonos B = (An.rlp ⊓ ofObjectProperty ⊤ An.naiveFibrantObjects).llp at h
  rw [hN] at h
  change cartesianRelativeHomotopyWeakMonos B = (J.rlp.llp.rlp ⊓ ofObjectProperty ⊤ (cartesianObjects B)).llp at h
  rwa [rlp_llp_rlp] at h

/-- Every original cocartesian relative homotopy weak mono is exactly a left lift against the actual
  completed right maps with intrinsic original codomain. -/
theorem cocartesianRelativeHomotopyWeakMonos_eq_llp (B : SSet.{u}) [Quasicategory B] :
    cocartesianRelativeHomotopyWeakMonos B =
      ((cocartesianRelativeBoundaryCells B).rlp ⊓ ofObjectProperty ⊤ (cocartesianObjects B)).llp := by
  let J := cocartesianRelativeBoundaryCells B
  let An := J.rlp.llp
  let P := relativeIntervalCylinder (max B)
  let _ : P.IsExact.{u} := relativeIntervalCylinder_isExact (max B)
  let _ : P.IsAnodyneSystem.{u} An := cocartesianRelativeBoundary_isAnodyneSystem B
  let _ : InitialMonoClass (Over (max B)) := over_initialMonoClass (max B)
  let _ : J.HasSmallObjectArgument.{u} := RelativeBoundarySmallObject.cocartesian_hasSmallObjectArgument B
  let _ : HasFactorization An An.rlp := by
    change HasFactorization J.rlp.llp J.rlp.llp.rlp
    rw [rlp_llp_rlp]
    infer_instance
  have hN : An.naiveFibrantObjects = cocartesianObjects B := by
    funext Y
    exact propext (cocartesianRelativeBoundary_naiveFibrant_iff Y)
  have h := Precylinder.IsAnodyneSystem.testingTrivialCofibrations_eq_llp_naiveFibrantCodomain P An
  change cocartesianRelativeHomotopyWeakMonos B = (An.rlp ⊓ ofObjectProperty ⊤ An.naiveFibrantObjects).llp at h
  rw [hN] at h
  change cocartesianRelativeHomotopyWeakMonos B = (J.rlp.llp.rlp ⊓ ofObjectProperty ⊤ (cocartesianObjects B)).llp at h
  rwa [rlp_llp_rlp] at h

/-- Full original Cartesian homotopy weak monos are closed under genuine native pushouts. -/
theorem cartesianRelativeHomotopyWeakMonos_cobase (B : SSet.{u}) [Quasicategory B] :
    (cartesianRelativeHomotopyWeakMonos B).IsStableUnderCobaseChange := by
  rw [cartesianRelativeHomotopyWeakMonos_eq_llp]
  infer_instance

/-- The entire dual class has the same original native pushout closure. -/
theorem cocartesianRelativeHomotopyWeakMonos_cobase (B : SSet.{u}) [Quasicategory B] :
    (cocartesianRelativeHomotopyWeakMonos B).IsStableUnderCobaseChange := by
  rw [cocartesianRelativeHomotopyWeakMonos_eq_llp]
  infer_instance

/-- Every original transfinite composition preserves the full Cartesian relative homotopy weak-mono property. -/
theorem cartesianRelativeHomotopyWeakMonos_transfinite (B : SSet.{u}) [Quasicategory B] :
    (cartesianRelativeHomotopyWeakMonos B).IsStableUnderTransfiniteComposition.{t} :=
  IsStableUnderTransfiniteComposition.of_llp_eq _ _ (cartesianRelativeHomotopyWeakMonos_eq_llp B).symm

/-- The dual full relative homotopy weak-mono class retains every original transfinite composite. -/
theorem cocartesianRelativeHomotopyWeakMonos_transfinite (B : SSet.{u}) [Quasicategory B] :
    (cocartesianRelativeHomotopyWeakMonos B).IsStableUnderTransfiniteComposition.{t} :=
  IsStableUnderTransfiniteComposition.of_llp_eq _ _ (cocartesianRelativeHomotopyWeakMonos_eq_llp B).symm

end SSet.Marked
