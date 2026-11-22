/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.PushoutJoinLeftHornAnodyne
import MathlibExt.AlgebraicTopology.SimplicialSet.PushoutJoinRightHornAnodyne
import MathlibExt.AlgebraicTopology.SimplicialSet.DirectedSimplexLifting

/-!
# Directed anodyne factors in the actual pushout join

The generated left horn class in the right factor, or the generated right
horn class in the left factor, gives an inner anodyne pushout join when
the other map is a monomorphism. These statements extend the already
proved horn computations, with no model-structure choice.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty
open scoped Simplicial

namespace SSet

/-- The generated left horn class in the right join factor gives inner anodyne lifting. -/
theorem innerAnodyneExtensions_pushoutJoin_leftAnodyne
    {A₀ A K₀ K : SSet.{u}} (a : A₀ ⟶ A) [Mono a] (i : K₀ ⟶ K)
    (hi : leftHornInclusions.rlp.llp i) :
    innerAnodyneExtensions (joinUnderPushoutObjObj a i).ι := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  apply pushoutJoin_mem_rlp_llp modelCategoryQuillen.I leftHornInclusions innerHornInclusions
  · intro A B K L f hf j hj
    obtain ⟨n⟩ := hf
    obtain @⟨m, k, hk⟩ := hj
    exact (innerAnodyneExtensions_eq_llp_rlp ▸
      innerAnodyneExtensions_pushoutJoin_leftHorn k hk (boundary.{u} n).ι)
  · rw [modelCategoryQuillen.llp_rlp_I]
    exact monomorphisms.infer_property a
  · exact hi

/-- The generated right horn class in the left join factor gives inner anodyne lifting. -/
theorem innerAnodyneExtensions_pushoutJoin_rightAnodyne
    {K₀ K A₀ A : SSet.{u}} (i : K₀ ⟶ K)
    (hi : rightHornInclusions.rlp.llp i) (a : A₀ ⟶ A) [Mono a] :
    innerAnodyneExtensions (joinUnderPushoutObjObj i a).ι := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  apply pushoutJoin_mem_rlp_llp rightHornInclusions modelCategoryQuillen.I innerHornInclusions
  · intro K L A B j hj f hf
    obtain @⟨m, k, hk⟩ := hj
    obtain ⟨n⟩ := hf
    exact (innerAnodyneExtensions_eq_llp_rlp ▸
      innerAnodyneExtensions_pushoutJoin_rightHorn k hk (boundary.{u} n).ι)
  · exact hi
  · rw [modelCategoryQuillen.llp_rlp_I]
    exact monomorphisms.infer_property a

/-- Over-slice restriction along a generated left-anodyne map has boundary lifting. -/
theorem sliceOver.rlp_I_restrictionComparison_of_leftAnodyne
    {K₀ K X B : SSet.{u}} (i : K₀ ⟶ K)
    (hi : leftHornInclusions.rlp.llp i) (t : K ⟶ X) (p : X ⟶ B)
    [InnerFibration p] : modelCategoryQuillen.I.rlp (sliceOver.restrictionComparison i t p) := by
  intro A D a ha
  obtain ⟨n⟩ := ha
  exact ((sliceOver.hasLiftingProperty_pushoutJoin_iff_forall i (boundary.{u} n).ι p).mp
    ((innerAnodyneExtensions_pushoutJoin_leftAnodyne (boundary.{u} n).ι i hi)
      p InnerFibration.mem)) t

/-- Under-slice restriction along a generated right-anodyne map has boundary lifting. -/
theorem sliceUnder.rlp_I_restrictionComparison_of_rightAnodyne
    {K₀ K X B : SSet.{u}} (i : K₀ ⟶ K)
    (hi : rightHornInclusions.rlp.llp i) (t : K ⟶ X) (p : X ⟶ B)
    [InnerFibration p] : modelCategoryQuillen.I.rlp (sliceUnder.restrictionComparison i t p) := by
  intro A D a ha
  obtain ⟨n⟩ := ha
  exact ((sliceUnder.hasLiftingProperty_pushoutJoin_iff_forall i (boundary.{u} n).ι p).mp
    ((innerAnodyneExtensions_pushoutJoin_rightAnodyne i hi (boundary.{u} n).ι)
      p InnerFibration.mem)) t

end SSet
