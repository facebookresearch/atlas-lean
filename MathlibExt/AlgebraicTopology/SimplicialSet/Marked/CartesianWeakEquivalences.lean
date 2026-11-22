/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverMappingFibrancy
import MathlibExt.CategoryTheory.MorphismProperty.InfClosure
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence

/-!
# Actual relative mapping-space weak equivalences

A map over the original marked base is a Cartesian mapping weak equivalence
when its native source-precomposition map is a realization weak equivalence
for every actual intrinsically marked Cartesian target. The dual uses
actual cocartesian targets. These are definitions in terms of the original
full marked relative mapping complexes, not supplied comparison outcomes.
Functoriality proves identities, two-out-of-three and retract stability.
Over a quasicategory base the mapping complexes are genuinely Kan, giving
the same native Kan weak-equivalence criterion. The remaining model lifting
and factorization compatibility is not asserted here.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty Opposite

namespace SSet.Marked

/-- Native precomposition tests into all actual intrinsic Cartesian targets define the relative weak class. -/
def cartesianWeakEquivalences (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  ⨅ Y : CartesianOver B,
    (realizationWeakEquivalences.inverseImage (overMappingFunctor .maximal (max B) Y.obj)).unop

/-- The dual relative weak class uses the original cocartesian target mapping complexes. -/
def cocartesianWeakEquivalences (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  ⨅ Y : CocartesianOver B,
    (realizationWeakEquivalences.inverseImage (overMappingFunctor .maximal (max B) Y.obj)).unop

/-- The Cartesian weak test uses precisely the actual whole source-precomposition map. -/
theorem cartesianWeakEquivalences_iff {B : SSet.{u}} {X X' : Over (max B)} (f : X ⟶ X') :
    cartesianWeakEquivalences B f ↔ ∀ Y : CartesianOver B,
      realizationWeakEquivalences ((overMappingFunctor .maximal (max B) Y.obj).map f.op) := by
  simp only [cartesianWeakEquivalences, MorphismProperty.iInf_iff, MorphismProperty.unop,
    MorphismProperty.inverseImage]

/-- The cocartesian weak test retains the same original precomposition operation. -/
theorem cocartesianWeakEquivalences_iff {B : SSet.{u}} {X X' : Over (max B)} (f : X ⟶ X') :
    cocartesianWeakEquivalences B f ↔ ∀ Y : CocartesianOver B,
      realizationWeakEquivalences ((overMappingFunctor .maximal (max B) Y.obj).map f.op) := by
  simp only [cocartesianWeakEquivalences, MorphismProperty.iInf_iff, MorphismProperty.unop,
    MorphismProperty.inverseImage]

/-- Identities satisfy every actual Cartesian mapping-space test. -/
theorem cartesianWeakEquivalences_containsIdentities (B : SSet.{u}) :
    (cartesianWeakEquivalences B).ContainsIdentities := by
  unfold cartesianWeakEquivalences
  infer_instance

/-- The actual Cartesian relative weak class has two-out-of-three. -/
theorem cartesianWeakEquivalences_hasTwoOutOfThreeProperty (B : SSet.{u}) :
    (cartesianWeakEquivalences B).HasTwoOutOfThreeProperty := by
  unfold cartesianWeakEquivalences
  exact MorphismProperty.hasTwoOutOfThreeProperty_iInf _

/-- The native Cartesian weak class is closed under original arrow retracts. -/
theorem cartesianWeakEquivalences_isStableUnderRetracts (B : SSet.{u}) :
    (cartesianWeakEquivalences B).IsStableUnderRetracts := by
  unfold cartesianWeakEquivalences
  exact MorphismProperty.isStableUnderRetracts_iInf _

/-- Original identity maps satisfy all dual mapping-space tests. -/
theorem cocartesianWeakEquivalences_containsIdentities (B : SSet.{u}) :
    (cocartesianWeakEquivalences B).ContainsIdentities := by
  unfold cocartesianWeakEquivalences
  infer_instance

/-- The actual dual mapping weak class also has two-out-of-three. -/
theorem cocartesianWeakEquivalences_hasTwoOutOfThreeProperty (B : SSet.{u}) :
    (cocartesianWeakEquivalences B).HasTwoOutOfThreeProperty := by
  unfold cocartesianWeakEquivalences
  exact MorphismProperty.hasTwoOutOfThreeProperty_iInf _

/-- Native cocartesian mapping weak equivalences retain retract stability. -/
theorem cocartesianWeakEquivalences_isStableUnderRetracts (B : SSet.{u}) :
    (cocartesianWeakEquivalences B).IsStableUnderRetracts := by
  unfold cocartesianWeakEquivalences
  exact MorphismProperty.isStableUnderRetracts_iInf _

/-- Over the original quasicategory base, Cartesian mapping weakness is precisely native Kan mapping weakness. -/
theorem cartesianWeakEquivalences_iff_kan {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (f : X ⟶ X') :
    cartesianWeakEquivalences B f ↔ ∀ Y : CartesianOver B,
      KanComplex.W ((overMappingFunctor .maximal (max B) Y.obj).map f.op) := by
  rw [cartesianWeakEquivalences_iff]
  apply forall_congr'
  intro Y
  let _ : KanComplex ((overMappingFunctor .maximal (max B) Y.obj).obj (op X)) :=
    overMappingFunctor_cartesian_kan X Y
  let _ : KanComplex ((overMappingFunctor .maximal (max B) Y.obj).obj (op X')) :=
    overMappingFunctor_cartesian_kan X' Y
  exact (KanComplex.W_iff_realizationWeakEquivalence _).symm

/-- The original cocartesian weak test has the same native Kan interpretation. -/
theorem cocartesianWeakEquivalences_iff_kan {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (f : X ⟶ X') :
    cocartesianWeakEquivalences B f ↔ ∀ Y : CocartesianOver B,
      KanComplex.W ((overMappingFunctor .maximal (max B) Y.obj).map f.op) := by
  rw [cocartesianWeakEquivalences_iff]
  apply forall_congr'
  intro Y
  let _ : KanComplex ((overMappingFunctor .maximal (max B) Y.obj).obj (op X)) :=
    overMappingFunctor_cocartesian_kan X Y
  let _ : KanComplex ((overMappingFunctor .maximal (max B) Y.obj).obj (op X')) :=
    overMappingFunctor_cocartesian_kan X' Y
  exact (KanComplex.W_iff_realizationWeakEquivalence _).symm

end SSet.Marked
