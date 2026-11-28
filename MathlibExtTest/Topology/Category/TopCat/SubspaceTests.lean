/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Category.TopCat.PreimageSubspacePullback
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp

/-! # Subspace restrictions of nonidentity affine maps -/

noncomputable section

open CategoryTheory TopCat

namespace MathlibExtTest.TopCatSubspace

private abbrev X : TopCat := TopCat.of ℝ
private def S : Set X := {x | 0 ≤ x}

private def plusOne : X ⟶ X := TopCat.ofHom ⟨fun x => x + 1, by fun_prop⟩
private def plusTwo : X ⟶ X := TopCat.ofHom ⟨fun x => x + 2, by fun_prop⟩

private lemma one_maps : Set.MapsTo plusOne S S := by
  intro x hx
  change (0 : ℝ) ≤ x at hx
  change (0 : ℝ) ≤ x + 1
  exact add_nonneg hx (by norm_num)

private lemma two_maps : Set.MapsTo plusTwo S S := by
  intro x hx
  change (0 : ℝ) ≤ x at hx
  change (0 : ℝ) ≤ x + 2
  exact add_nonneg hx (by norm_num)

private lemma identity_maps : Set.MapsTo (𝟙 X) S S := by
  intro x hx
  simpa only [ConcreteCategory.id_apply] using hx

example : subspaceMap (𝟙 X) identity_maps = 𝟙 (TopCat.of S) := by
  simp

example : subspaceMap plusOne one_maps ≫ subspaceMap plusTwo two_maps =
    subspaceMap (plusOne ≫ plusTwo) (fun _ hx => two_maps (one_maps hx)) := by
  simp

private def zeroPoint : S := ⟨0, le_rfl⟩

example : ((subspaceMap plusOne one_maps ≫ subspaceMap plusTwo two_maps) zeroPoint).val = 3 := by
  change (0 : ℝ) + 1 + 2 = 3
  norm_num

example : subspaceInclOfSubset (show S ⊆ Set.univ from Set.subset_univ _) ≫
    subspaceIncl (Set.univ : Set X) = subspaceIncl S := by
  exact subspaceInclOfSubset_comp _

private abbrev Q : TopCat := TopCat.of PUnit
private def pointToReal : Q ⟶ X := TopCat.ofHom ⟨fun _ => 0, continuous_const⟩
private def realToPoint : X ⟶ Q := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩

private lemma point_square_commutes : (𝟙 Q) ≫ (𝟙 Q) = pointToReal ≫ realToPoint := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact Subsingleton.elim _ _

private lemma point_identity_maps :
    Set.MapsTo (𝟙 Q) (Set.univ : Set Q) (Set.univ : Set Q) := by
  intro x hx
  simpa only [ConcreteCategory.id_apply] using hx

example : IsPullback
    (subspaceMap (𝟙 Q)
      point_identity_maps)
    (subspaceIncl (Set.univ : Set Q)) (subspaceIncl (Set.univ : Set Q)) (𝟙 Q) := by
  simpa only [Set.preimage_univ, TopCat.subspaceMap_id] using
    isPullback_preimageSubspace_of_comm
    (e₁ := 𝟙 Q) (p₁ := pointToReal) (p := 𝟙 Q) (b₁ := realToPoint)
    point_square_commutes (Set.univ : Set Q) (Set.univ : Set X) (by simp)

end MathlibExtTest.TopCatSubspace
