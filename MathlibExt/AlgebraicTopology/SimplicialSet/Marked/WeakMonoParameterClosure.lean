/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.TestingBoundaryRecognition
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterAssociativity
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterTerminalComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterMonomorphisms
import Mathlib.CategoryTheory.Adhesive.PushoutProduct

/-!
# All original weak marked monos are closed under scalar mono corners

A full weak marked-mono test has the genuine boundary-right mapping
restriction. It therefore lifts all scalar monomorphisms. The actual
fixed-base corner associator retains every higher parameter boundary,
so any scalar mono corner remains a full weak marked mono. This gives
whole boundary and iterated-boundary closure without replacing the
large test class by an unproved small generating family.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty MonoidalCategory
open scoped Simplicial

namespace SSet.Marked

/-- Every full original Cartesian weak mono lifts each entire scalar-mono parameter into every actual
  intrinsic target. -/
theorem cartesianWeakMono_parameter_lifting {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) (hi : cartesianTestingTrivialCofibrations B i)
    {K L : SSet.{u}} (a : K ⟶ L) [Mono a] (Y : CartesianOver B) :
    HasLiftingProperty (overParameterPushoutProduct a i) (Over.mkIdTerminal.from Y.obj) := by
  have hI := (cartesianCotensorBoundaryTests_llp_iff i).mp
    ((cartesianTestingTrivialCofibrations_iff_cotensor i).mp hi).2 Y
  let q := overParameterMappingComparison i (Over.mkIdTerminal.from Y.obj)
  have hq : modelCategoryQuillen.I.{u}.rlp q :=
    (modelCategoryQuillen.I.rlp.arrow_iso_iff (overParameterMappingComparisonTerminalIso i Y.obj)).mpr hI
  have hm : (monomorphisms SSet.{u}).rlp q := by
    rw [SSet.rlp_monomorphisms]
    exact hq
  exact (overParameterPushoutProduct_hasLiftingProperty_iff a i (Over.mkIdTerminal.from Y.obj)).mpr
    (hm a inferInstance)

/-- The same full dual weak-mono test lifts each actual scalar monomorphism. -/
theorem cocartesianWeakMono_parameter_lifting {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) (hi : cocartesianTestingTrivialCofibrations B i)
    {K L : SSet.{u}} (a : K ⟶ L) [Mono a] (Y : CocartesianOver B) :
    HasLiftingProperty (overParameterPushoutProduct a i) (Over.mkIdTerminal.from Y.obj) := by
  have hI := (cocartesianCotensorBoundaryTests_llp_iff i).mp
    ((cocartesianTestingTrivialCofibrations_iff_cotensor i).mp hi).2 Y
  let q := overParameterMappingComparison i (Over.mkIdTerminal.from Y.obj)
  have hq : modelCategoryQuillen.I.{u}.rlp q :=
    (modelCategoryQuillen.I.rlp.arrow_iso_iff (overParameterMappingComparisonTerminalIso i Y.obj)).mpr hI
  have hm : (monomorphisms SSet.{u}).rlp q := by
    rw [SSet.rlp_monomorphisms]
    exact hq
  exact (overParameterPushoutProduct_hasLiftingProperty_iff a i (Over.mkIdTerminal.from Y.obj)).mpr
    (hm a inferInstance)

private theorem scalarBoundaryCorner_mono {K L : SSet.{u}} (a : K ⟶ L) [Mono a] (n : ℕ) :
    Mono ((Arrow.mk (boundary.{u} n).ι □ Arrow.mk a).hom) := by
  let _ : Mono (Arrow.mk (boundary.{u} n).ι).hom := (inferInstance : Mono (boundary.{u} n).ι)
  let _ : Mono (Arrow.mk a).hom := (inferInstance : Mono a)
  exact MonoidalCategory.Arrow.PushoutProduct.instMonoHomObjArrowFunctorPushoutProduct

/-- Every scalar-mono corner of an original Cartesian weak marked mono has the full native mapping
  boundary-right property. -/
theorem cartesianWeakMono_parameter_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) (hi : cartesianTestingTrivialCofibrations B i)
    {K L : SSet.{u}} (a : K ⟶ L) [Mono a] (Y : CartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) Y.obj).map
      (overParameterPushoutProduct a i).op) := by
  apply (overParameterBoundary_terminal_lifting_iff _ Y.obj).mp
  intro n
  let q := (Arrow.mk (boundary.{u} n).ι □ Arrow.mk a).hom
  let _ : Mono q := scalarBoundaryCorner_mono a n
  have h := cartesianWeakMono_parameter_lifting i hi q Y
  exact (HasLiftingProperty.iff_of_arrow_iso_left
    (overParameterPushoutProductAssociativityIso (boundary.{u} n).ι a i)
    (Over.mkIdTerminal.from Y.obj)).mpr h

/-- The same original scalar-mono corners have all cocartesian mapping boundary lifts. -/
theorem cocartesianWeakMono_parameter_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) (hi : cocartesianTestingTrivialCofibrations B i)
    {K L : SSet.{u}} (a : K ⟶ L) [Mono a] (Y : CocartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) Y.obj).map
      (overParameterPushoutProduct a i).op) := by
  apply (overParameterBoundary_terminal_lifting_iff _ Y.obj).mp
  intro n
  let q := (Arrow.mk (boundary.{u} n).ι □ Arrow.mk a).hom
  let _ : Mono q := scalarBoundaryCorner_mono a n
  have h := cocartesianWeakMono_parameter_lifting i hi q Y
  exact (HasLiftingProperty.iff_of_arrow_iso_left
    (overParameterPushoutProductAssociativityIso (boundary.{u} n).ι a i)
    (Over.mkIdTerminal.from Y.obj)).mpr h

/-- Every original Cartesian weak marked mono remains in the full class under any native scalar mono corner. -/
theorem cartesianWeakMono_parameter_closed {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) (hi : cartesianTestingTrivialCofibrations B i)
    {K L : SSet.{u}} (a : K ⟶ L) [Mono a] :
    cartesianTestingTrivialCofibrations B (overParameterPushoutProduct a i) := by
  let _ : Mono i := hi.1
  refine ⟨overParameterPushoutProduct_mono a i, (cartesianWeakEquivalences_iff _).mpr ?_⟩
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
    (cartesianWeakMono_parameter_mapping_rlp i hi a Y)

/-- The full cocartesian weak-mono class has the same native scalar mono corner closure. -/
theorem cocartesianWeakMono_parameter_closed {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) (hi : cocartesianTestingTrivialCofibrations B i)
    {K L : SSet.{u}} (a : K ⟶ L) [Mono a] :
    cocartesianTestingTrivialCofibrations B (overParameterPushoutProduct a i) := by
  let _ : Mono i := hi.1
  refine ⟨overParameterPushoutProduct_mono a i, (cocartesianWeakEquivalences_iff _).mpr ?_⟩
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
    (cocartesianWeakMono_parameter_mapping_rlp i hi a Y)

end SSet.Marked
