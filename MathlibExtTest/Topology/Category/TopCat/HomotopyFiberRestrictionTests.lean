/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberRestriction

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat

-- The public characteristic exposes the actual ambient total coordinate
-- while the restriction wrapper remains opaque to this consumer.
example {E B : TopCat.{u}} (p : E ⟶ B) {W U : Set B} (hWU : W ⊆ U) :
    restrictionTotalInclusion p hWU ≫ AlgebraicTopology.subspaceIncl (p ⁻¹' U) =
      AlgebraicTopology.subspaceIncl (p ⁻¹' W) := by
  rw [restrictionTotalInclusion_eq_subspaceInclOfSubset,
    AlgebraicTopology.subspaceInclOfSubset_comp]

-- The inverse of the public isomorphism recovers the original total-space
-- coordinate without unfolding its pasted-pullback constructor.
example {E₀ A E B : TopCat.{u}} {q : E₀ ⟶ A} {p : E ⟶ B}
    {s : E₀ ⟶ E} {h : A ⟶ B} (sq : IsPullback s q p h) (a : A) :
    (strictFiberRestrictionIso sq a).inv ≫
        pullback.fst q (TopCat.const (X := TopCat.of PUnit) a) ≫ s =
      pullback.fst p (TopCat.const (X := TopCat.of PUnit) (h a)) := by
  have ht := congrArg (fun k => (strictFiberRestrictionIso sq a).inv ≫ k)
    (strictFiberRestrictionIso_hom_fst sq a)
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using ht.symm

-- The actual intersection-to-member map is weak using exactly the two
-- local canonical comparisons, with no weakness premise on either inclusion.
example {E B : TopCat.{u}} (p : E ⟶ B) (U V : Set B)
    (w : TopCat.of (U ∩ V : Set B))
    (hinter : weakHomotopyEquivalences
      (strictFiberToHomotopyFiber (restrictionProjection p (U ∩ V)) w))
    (hleft : weakHomotopyEquivalences
      (strictFiberToHomotopyFiber (restrictionProjection p U)
        (AlgebraicTopology.subspaceInclOfSubset Set.inter_subset_left w))) :
    weakHomotopyEquivalences
      (homotopyFiberMapOfSquare
        (restrictionTotalInclusion p (Set.inter_subset_left : U ∩ V ⊆ U))
        (AlgebraicTopology.subspaceInclOfSubset Set.inter_subset_left)
        (restrictionProjection_nested_isPullback p Set.inter_subset_left).w.symm w) :=
  restrictionHomotopyFiberMap_mem p Set.inter_subset_left w hinter hleft

-- The overlap map retains the actual included path, including its parameter.
example {E B : TopCat.{u}} (p : E ⟶ B) {W U : Set B} (hWU : W ⊆ U)
    (w : TopCat.of W) (z : homotopyFiber (restrictionProjection p W) w)
    (t : TopCat.I.{u}) :
    homotopyFiberPath (restrictionProjection p U)
      (AlgebraicTopology.subspaceInclOfSubset hWU w)
      (homotopyFiberMapOfSquare (restrictionTotalInclusion p hWU)
        (AlgebraicTopology.subspaceInclOfSubset hWU)
        (restrictionProjection_nested_isPullback p hWU).w.symm w z) t =
      AlgebraicTopology.subspaceInclOfSubset hWU
        (homotopyFiberPath (restrictionProjection p W) w z t) := by
  exact congrArg (fun γ : C(TopCat.I.{u}, TopCat.of U) => γ t)
    (ConcreteCategory.congr_hom
      (homotopyFiberMapOfSquare_path (restrictionTotalInclusion p hWU)
        (AlgebraicTopology.subspaceInclOfSubset hWU)
        (restrictionProjection_nested_isPullback p hWU).w.symm w) z)

#print axioms TopCat.strictFiberRestrictionIso
#print axioms TopCat.strictFiberRestrictionIso_hom_fst
#print axioms TopCat.strictFiberRestrictionIso_hom_eq
#print axioms TopCat.isIso_strictFiberMapOfSquare_of_isPullback
#print axioms TopCat.homotopyFiberMapOfSquare_mem_of_isPullback_comparisons
#print axioms TopCat.restrictionProjection_nested_isPullback
#print axioms TopCat.restrictionHomotopyFiberMap_mem
#print axioms TopCat.restrictionTotalInclusion_eq_subspaceInclOfSubset

end TopCat
