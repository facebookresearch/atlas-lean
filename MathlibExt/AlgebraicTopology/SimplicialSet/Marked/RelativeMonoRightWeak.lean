/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeStrongDeformation
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeIntervalEndpointComparison
import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseAnodyneCornersWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.TestingSaturation

/-!
# Original mono-right maps are genuinely full intrinsic mapping weak

A given section of the actual mono-right map has a whole native relative
strong deformation. Its original endpoint corner is a proved scalar
Kan-anodyne/marked-mono weak corner. Rectification lifts every full
intrinsic testing right map, so the section is a full weak marked mono.
The original strict section triangle and two-out-of-three then prove
weakness of the mono-right map itself. No replacement size bound,
Kan-base condition or supplied model result is used.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

/-- A whole native relative strong deformation is a full original Cartesian weak marked mono. -/
theorem relativeStrongDeformation_cartesian_weakMono {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} {i : X ⟶ Y} (D : (relativeIntervalCylinder (max B)).StrongDeformationData i) :
    cartesianTestingTrivialCofibrations B i := by
  let _ : Mono i := D.mono
  let a := relativeIntervalScalarEndpoint.{u} 1
  let _ : Mono a := by change Mono (stdSimplex.{u}.δ (0 : Fin 2)); infer_instance
  have hc : cartesianTestingTrivialCofibrations B (overParameterPushoutProduct a i) :=
    ⟨overParameterPushoutProduct_mono a i, cartesianAnodyneCorner_weak i a (relativeIntervalScalarEndpoint_anodyne 1)⟩
  rw [← cartesianTestingFibrations_llp B]
  intro E F p hp
  let _ : HasLiftingProperty ((relativeIntervalCylinder (max B)).endpointCorner i 1) p :=
    (HasLiftingProperty.iff_of_arrow_iso_left (relativeIntervalEndpointCornerIso i 1) p).mp (hp _ hc)
  exact D.hasLiftingProperty_of_endpointCorner p

/-- The same full original marked strong deformation is also dual intrinsic mapping weak and monic. -/
theorem relativeStrongDeformation_cocartesian_weakMono {B : SSet.{u}} [Quasicategory B]
    {X Y : Over (max B)} {i : X ⟶ Y} (D : (relativeIntervalCylinder (max B)).StrongDeformationData i) :
    cocartesianTestingTrivialCofibrations B i := by
  let _ : Mono i := D.mono
  let a := relativeIntervalScalarEndpoint.{u} 1
  let _ : Mono a := by change Mono (stdSimplex.{u}.δ (0 : Fin 2)); infer_instance
  have hc : cocartesianTestingTrivialCofibrations B (overParameterPushoutProduct a i) :=
    ⟨overParameterPushoutProduct_mono a i, cocartesianAnodyneCorner_weak i a (relativeIntervalScalarEndpoint_anodyne 1)⟩
  rw [← cocartesianTestingFibrations_llp B]
  intro E F p hp
  let _ : HasLiftingProperty ((relativeIntervalCylinder (max B)).endpointCorner i 1) p :=
    (HasLiftingProperty.iff_of_arrow_iso_left (relativeIntervalEndpointCornerIso i 1) p).mp (hp _ hc)
  exact D.hasLiftingProperty_of_endpointCorner p

/-- Every original marked mono-right map has genuine full Cartesian mapping weakness over an arbitrary
  original quasicategory base. -/
theorem monoRight_le_cartesianWeakEquivalences (B : SSet.{u}) [Quasicategory B] :
    (monomorphisms (Over (max B))).rlp ≤ cartesianWeakEquivalences B := by
  let _ : InitialMonoClass (Over (max B)) := over_initialMonoClass (max B)
  let _ : (cartesianWeakEquivalences B).ContainsIdentities := cartesianWeakEquivalences_containsIdentities B
  let _ : (cartesianWeakEquivalences B).HasTwoOutOfThreeProperty := cartesianWeakEquivalences_hasTwoOutOfThreeProperty B
  intro X Y p hp
  obtain ⟨S⟩ := exists_splitEpi_of_rlp_monomorphisms p hp
  obtain ⟨D, _, _⟩ := relativeIntervalStrongDeformation_of_section p hp S.section_ S.id
  have hs := (relativeStrongDeformation_cartesian_weakMono D).2
  exact (cartesianWeakEquivalences B).of_precomp S.section_ p hs
    (S.id.symm ▸ (cartesianWeakEquivalences B).id_mem Y)

/-- The exact same original mono-right map is weak for every full cocartesian relative mapping test as well. -/
theorem monoRight_le_cocartesianWeakEquivalences (B : SSet.{u}) [Quasicategory B] :
    (monomorphisms (Over (max B))).rlp ≤ cocartesianWeakEquivalences B := by
  let _ : InitialMonoClass (Over (max B)) := over_initialMonoClass (max B)
  let _ : (cocartesianWeakEquivalences B).ContainsIdentities := cocartesianWeakEquivalences_containsIdentities B
  let _ : (cocartesianWeakEquivalences B).HasTwoOutOfThreeProperty :=
    cocartesianWeakEquivalences_hasTwoOutOfThreeProperty B
  intro X Y p hp
  obtain ⟨S⟩ := exists_splitEpi_of_rlp_monomorphisms p hp
  obtain ⟨D, _, _⟩ := relativeIntervalStrongDeformation_of_section p hp S.section_ S.id
  have hs := (relativeStrongDeformation_cocartesian_weakMono D).2
  exact (cocartesianWeakEquivalences B).of_precomp S.section_ p hs
    (S.id.symm ▸ (cocartesianWeakEquivalences B).id_mem Y)

end SSet.Marked
