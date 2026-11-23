/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.OpenCoverHomotopyPushout

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace TopCat

-- The two-set model has an actual pushout square with cofibration inputs.
example {X : TopCat.{u}} (U V : Set X) :
    IsPushout
      (realizedSubordinateSetInclusion (Set.inter_subset_left : U ∩ V ⊆ U))
      (realizedSubordinateSetInclusion (Set.inter_subset_right : U ∩ V ⊆ V))
      (realizedTwoSetCoverLeft U V) (realizedTwoSetCoverRight U V) :=
  realizedTwoSetCover_isPushout U V

example {X : TopCat.{u}} (U V : Set X) :
    Cofibration (realizedSubordinateSetInclusion (Set.inter_subset_left : U ∩ V ⊆ U)) :=
  realizedSubordinateSetInclusion_cofibration _

-- Its actual comparison on the intersection evaluates into that subspace.
example {X : TopCat.{u}} (U V : Set X) :
    realizedSubordinateSetInclusion (Set.inter_subset_left : U ∩ V ⊆ U) ≫
      realizedSubordinateSetEvaluation U ≫ AlgebraicTopology.subspaceIncl U =
        realizedSubordinateSetEvaluation (U ∩ V) ≫
          AlgebraicTopology.subspaceIncl (U ∩ V) := by
  rw [realizedSubordinateSetInclusion_evaluation_assoc]
  rw [AlgebraicTopology.subspaceInclOfSubset_comp]

-- The native square uses the actual open subspaces and inclusions.
example {X : TopCat.{u}} (U V : TopologicalSpace.Opens X)
    (hcover : (U : Set X) ∪ V = Set.univ) :
    IsPushout
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U))
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V))
      (AlgebraicTopology.subspaceIncl (U : Set X))
      (AlgebraicTopology.subspaceIncl (V : Set X)) :=
  isPushout_twoSetOpenCover U V hcover

-- For an arbitrary map p the actual total-space preimages form an open
-- cover, and their realized union comparison is weak without a premise on p.
example {E B : TopCat.{u}} (p : E ⟶ B) (U V : TopologicalSpace.Opens B)
    (hcover : (U : Set B) ∪ V = Set.univ) :
    weakHomotopyEquivalences
      (realizedTwoSetCoverComparison (p ⁻¹' (U : Set B)) (p ⁻¹' (V : Set B))) := by
  apply realizedTwoSetCoverComparison_mem_weakHomotopyEquivalences
    (U.comap p.hom) (V.comap p.hom)
  change p ⁻¹' ((U : Set B) ∪ V) = Set.univ
  rw [hcover, Set.preimage_univ]

-- Naturality keeps precisely the total/base cover map induced by p.
example {E B : TopCat.{u}} (p : E ⟶ B) (U V : Set B) :
    realizedTwoSetCoverMap p
        (fun _ hx => hx : Set.MapsTo p (p ⁻¹' U) U)
        (fun _ hx => hx : Set.MapsTo p (p ⁻¹' V) V) ≫
      realizedTwoSetCoverComparison U V =
        realizedTwoSetCoverComparison (p ⁻¹' U) (p ⁻¹' V) ≫ p :=
  realizedTwoSetCoverMap_comparison p _ _

-- Every standard replacement of the native cover span has a weak actual
-- comparison to the ambient space; no chosen TopCat functorial factorization
-- is needed to state or consume this theorem.
example {X : TopCat.{u}} (U V : TopologicalSpace.Opens X)
    (hcover : (U : Set X) ∪ V = Set.univ)
    (R : CofibrantSpanReplacement (span
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U))
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V)))) :
    weakHomotopyEquivalences (cofibrantSpanReplacementOpenCoverComparison U V hcover R) :=
  cofibrantSpanReplacementOpenCoverComparison_mem_weakHomotopyEquivalences U V hcover R

-- The public coordinate theorem supplies the actual point image of a
-- member of an arbitrary replacement, without unfolding comparison choices.
example {X : TopCat.{u}} (U V : TopologicalSpace.Opens X)
    (hcover : (U : Set X) ∪ V = Set.univ)
    (R : CofibrantSpanReplacement (span
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U))
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V))))
    (z : R.Q.obj WalkingSpan.left) :
    cofibrantSpanReplacementOpenCoverComparison U V hcover R
      (colimit.ι R.Q WalkingSpan.left z) = (R.counit.app WalkingSpan.left z).val :=
  ConcreteCategory.congr_hom
    (cofibrantSpanReplacementOpenCoverComparison_left U V hcover R) z

#print axioms TopCat.realizedSubordinateSetEvaluation
#print axioms TopCat.realizedSubordinateSetEvaluation_inclusion
#print axioms TopCat.realizedSubordinateSetEvaluation_mem_weakHomotopyEquivalences
#print axioms TopCat.realizedSubordinateSet_isCofibrant
#print axioms TopCat.realizedSubordinateSetInclusion_cofibration
#print axioms TopCat.realizedSubordinateSetInclusion_evaluation
#print axioms TopCat.realizedTwoSetCover_isPushout
#print axioms TopCat.realizedTwoSetCoverComparison_mem_weakHomotopyEquivalences
#print axioms TopCat.realizedTwoSetCoverMap_comparison
#print axioms TopCat.isPushout_twoSetOpenCover
#print axioms TopCat.cofibrantSpanReplacementOpenCoverComparison
#print axioms TopCat.cofibrantSpanReplacementOpenCoverComparison_left
#print axioms TopCat.cofibrantSpanReplacementOpenCoverComparison_right
#print axioms TopCat.cofibrantSpanReplacementOpenCoverComparison_mem_weakHomotopyEquivalences

end TopCat
