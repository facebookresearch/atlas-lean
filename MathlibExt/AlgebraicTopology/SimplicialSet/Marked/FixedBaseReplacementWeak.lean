/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseFibrantReplacement
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseMarkRefinementWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseAnodyneCornersWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalMappingWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CocartesianCriticalMappingWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InnerCellParameterLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EndpointParameterLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.TestingSaturation

/-!
# Weakness of the actual original fixed-base replacement units

Every original auxiliary cell over every prescribed whole base simplex,
and every constant-base Kan horn/marked-mono corner, has full intrinsic
mapping weakness. The proved full weak marked-mono saturation therefore
contains the actual original fixed-base small-object left class. The
same original functorial factors and replacement units are weak, at the
same native fixed-base cardinal and with the same intrinsic targets.

A uniform small generation of all weak marked monos, the converse full
arrow testing recognition, and the marked model axioms remain separate
requirements. No such conclusion is supplied as an input.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace SSet.Marked

local instance fixedBaseWeakUnitCardinalRegular (B : SSet.{u}) : Fact (FixedBaseSmallObject.cardinal B).IsRegular :=
  FixedBaseSmallObject.cardinal_regular B

/-- Every actual original Cartesian fixed-base generator has the full intrinsic mapping weakness. -/
theorem cartesianFixedBaseCells_le_weak (B : SSet.{u}) [Quasicategory B] :
    cartesianFixedBaseCells B ≤ cartesianWeakEquivalences B := by
  rintro A D f ⟨s⟩
  rcases s with ⟨j, r⟩ | ⟨a, n, k⟩
  · rcases j with ⟨n, i⟩ | n | k
    · exact innerCellOver_cartesian_weak n i.val i.property.1 i.property.2 r.hom
    · exact cartesianCriticalOver_weak n r
    · fin_cases k
      · exact cartesianEndpointOver_weak r
      · exact compositionCellOver_cartesian_weak r
      · exact kanMarkCellOver_cartesian_weak KanEdgeDetector.object.{u} r
  · let _ : Mono (fixedBaseMonoCell B a).hom := fixedBaseMonoCell_mono B a
    exact cartesianAnodyneCorner_weak _ _ (anodyneExtensions.horn_ι k)

/-- The same original dual fixed-base generators are all intrinsically mapping weak. -/
theorem cocartesianFixedBaseCells_le_weak (B : SSet.{u}) [Quasicategory B] :
    cocartesianFixedBaseCells B ≤ cocartesianWeakEquivalences B := by
  rintro A D f ⟨s⟩
  rcases s with ⟨j, r⟩ | ⟨a, n, k⟩
  · rcases j with ⟨n, i⟩ | n | k
    · exact innerCellOver_cocartesian_weak n i.val i.property.1 i.property.2 r.hom
    · exact cocartesianCriticalOver_weak n r
    · fin_cases k
      · exact cocartesianEndpointOver_weak r
      · exact compositionCellOver_cocartesian_weak r
      · exact kanMarkCellOver_cocartesian_weak KanEdgeDetector.object.{u} r
  · let _ : Mono (fixedBaseMonoCell B a).hom := fixedBaseMonoCell_mono B a
    exact cocartesianAnodyneCorner_weak _ _ (anodyneExtensions.horn_ι k)

/-- The entire actual Cartesian fixed-base family consists of original full weak marked monomorphisms. -/
theorem cartesianFixedBaseCells_le_testing (B : SSet.{u}) [Quasicategory B] :
    cartesianFixedBaseCells B ≤ cartesianTestingTrivialCofibrations B := by
  intro A D f hf
  exact ⟨cartesianFixedBaseCells_le_monomorphisms B f hf, cartesianFixedBaseCells_le_weak B f hf⟩

/-- The complete dual original generator family lies in the full weak marked-mono class. -/
theorem cocartesianFixedBaseCells_le_testing (B : SSet.{u}) [Quasicategory B] :
    cocartesianFixedBaseCells B ≤ cocartesianTestingTrivialCofibrations B := by
  intro A D f hf
  exact ⟨cocartesianFixedBaseCells_le_monomorphisms B f hf, cocartesianFixedBaseCells_le_weak B f hf⟩

/-- The whole original generated Cartesian left class, with all native transfinite factors, is intrinsically
  mapping weak and monic. -/
theorem cartesianFixedBase_left_le_testing (B : SSet.{u}) [Quasicategory B] :
    (cartesianFixedBaseCells B).rlp.llp ≤ cartesianTestingTrivialCofibrations B := by
  calc
    _ ≤ (cartesianTestingTrivialCofibrations B).rlp.llp :=
      antitone_llp (antitone_rlp (cartesianFixedBaseCells_le_testing B))
    _ = _ := cartesianTestingFibrations_llp B

/-- All actual original dual small-object left factors retain full weak marked-mono testing. -/
theorem cocartesianFixedBase_left_le_testing (B : SSet.{u}) [Quasicategory B] :
    (cocartesianFixedBaseCells B).rlp.llp ≤ cocartesianTestingTrivialCofibrations B := by
  calc
    _ ≤ (cocartesianTestingTrivialCofibrations B).rlp.llp :=
      antitone_llp (antitone_rlp (cocartesianFixedBaseCells_le_testing B))
    _ = _ := cocartesianTestingFibrations_llp B

/-- The same original Cartesian functorial factorization has genuinely weak monic left maps for every whole
  input arrow. -/
theorem cartesianFixedBaseFactorization_left_weak (B : SSet.{u}) [Quasicategory B]
    (f : Arrow (Over (max B))) :
    cartesianTestingTrivialCofibrations B ((FixedBaseSmallObject.cartesianFunctorialFactorization B).i.app f) :=
  cartesianFixedBase_left_le_testing B _ ((FixedBaseSmallObject.cartesianFunctorialFactorization B).hi f)

/-- The dual native functorial factorization retains the same whole weak left factor. -/
theorem cocartesianFixedBaseFactorization_left_weak (B : SSet.{u}) [Quasicategory B]
    (f : Arrow (Over (max B))) :
    cocartesianTestingTrivialCofibrations B ((FixedBaseSmallObject.cocartesianFunctorialFactorization B).i.app f) :=
  cocartesianFixedBase_left_le_testing B _ ((FixedBaseSmallObject.cocartesianFunctorialFactorization B).hi f)

/-- Every actual original Cartesian replacement unit is a full weak marked mono at the unchanged native
  fixed-base rank. -/
theorem cartesianFixedBaseReplacementUnit_weak (B : SSet.{u}) [Quasicategory B]
    (X : Over (max B)) :
    cartesianTestingTrivialCofibrations B ((cartesianFixedBaseReplacementUnit B).app X) :=
  cartesianFixedBase_left_le_testing B _ (cartesianFixedBaseReplacementUnit_left B X)

/-- The same original dual replacement unit has full intrinsic mapping weakness and original monicity. -/
theorem cocartesianFixedBaseReplacementUnit_weak (B : SSet.{u}) [Quasicategory B]
    (X : Over (max B)) :
    cocartesianTestingTrivialCofibrations B ((cocartesianFixedBaseReplacementUnit B).app X) :=
  cocartesianFixedBase_left_le_testing B _ (cocartesianFixedBaseReplacementUnit_left B X)

end SSet.Marked
