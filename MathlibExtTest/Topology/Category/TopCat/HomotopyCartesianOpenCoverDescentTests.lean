/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Category.TopCat.HomotopyCartesianOpenCoverDescent
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead

/-!
# Consumers of the actual constant-path square comparison

Check its actual strict-point-fiber map, both path endpoints, and its weak
strict-pullback case. The standard-cylinder client uses the literal tensor
object through the public provider boundary.
The open-cover clients retain the actual global point comparison and the
actual included total-space coordinate without a global fibration premise.
-/

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory SSet.modelCategoryQuillen Simplicial MonoidalCategory

noncomputable section

universe u

example {E B : TopCat.{u}} (p : E ⟶ B) (b : B) :
    TopCat.homotopyPullbackComparison
        (IsPullback.of_hasPullback p (TopCat.const (X := TopCat.of PUnit) b)).toCommSq =
      TopCat.strictFiberToHomotopyFiber p b :=
  TopCat.homotopyPullbackComparison_pointFiber p b

example {A E W B : TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : CommSq s q p h) :
    TopCat.homotopyPullbackComparison sq ≫ TopCat.homotopyPullbackPath p h ≫
        TopCat.pathEvalZero B = s ≫ p := by simp

example {A E W B : TopCat.{u}} {s : A ⟶ E} {q : A ⟶ W} {p : E ⟶ B} {h : W ⟶ B}
    (sq : CommSq s q p h) :
    TopCat.homotopyPullbackComparison sq ≫ TopCat.homotopyPullbackPath p h ≫
        TopCat.pathEvalOne B = q ≫ h := by simpa using sq.w

example {E W B : TopCat.{u}} (p : E ⟶ B) (h : W ⟶ B) [Fibration p] :
    TopCat.weakHomotopyEquivalences (TopCat.homotopyPullbackComparison
      (IsPullback.of_hasPullback p h).toCommSq) :=
  TopCat.homotopyPullbackComparison_mem_of_isPullback (IsPullback.of_hasPullback p h)

example {E B : TopCat.{u}} (p : E ⟶ B) (U V : TopologicalSpace.Opens B)
    (hc : (U : Set B) ∪ V = Set.univ)
    (hleft : TopCat.weakHomotopyEquivalences (TopCat.homotopyPullbackComparison
      (TopCat.restrictionProjection_nested_isPullback p
        (Set.inter_subset_left : (U : Set B) ∩ V ⊆ U)).toCommSq))
    (hright : TopCat.weakHomotopyEquivalences (TopCat.homotopyPullbackComparison
      (TopCat.restrictionProjection_nested_isPullback p
        (Set.inter_subset_right : (U : Set B) ∩ V ⊆ V)).toCommSq)) :
    TopCat.weakHomotopyEquivalences (TopCat.homotopyPullbackComparison
      (TopCat.restrictionProjection_isPullback p (U : Set B)).toCommSq) ∧
    TopCat.homotopyPullbackComparison
        (TopCat.restrictionProjection_isPullback p (U : Set B)).toCommSq ≫
      TopCat.homotopyPullbackLeft p (AlgebraicTopology.subspaceIncl (U : Set B)) =
        AlgebraicTopology.subspaceIncl (p ⁻¹' (U : Set B)) :=
  ⟨(TopCat.homotopyPullbackComparison_mem_of_twoSetOpenCover p U V hc hleft hright).1,
    TopCat.homotopyPullbackComparison_left _⟩

example {E B : TopCat.{u}} (p : E ⟶ B) (U V : TopologicalSpace.Opens B)
    (hc : (U : Set B) ∪ V = Set.univ)
    (hU : ∀ u : TopCat.of (U : Set B), TopCat.weakHomotopyEquivalences
      (TopCat.strictFiberToHomotopyFiber (TopCat.restrictionProjection p (U : Set B)) u))
    (hV : ∀ v : TopCat.of (V : Set B), TopCat.weakHomotopyEquivalences
      (TopCat.strictFiberToHomotopyFiber (TopCat.restrictionProjection p (V : Set B)) v))
    (hUV : ∀ w : TopCat.of ((U : Set B) ∩ V : Set B), TopCat.weakHomotopyEquivalences
      (TopCat.strictFiberToHomotopyFiber (TopCat.restrictionProjection p ((U : Set B) ∩ V)) w))
    (b : B) :
    TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber p b) ∧
      TopCat.strictFiberToHomotopyFiber p b ≫ TopCat.homotopyFiberToTotal p b =
        pullback.fst p (TopCat.const (X := TopCat.of PUnit) b) :=
  ⟨TopCat.strictFiberToHomotopyFiber_mem_of_twoSetOpenCover p U V hc hU hV hUV b,
    TopCat.strictFiberToHomotopyFiber_toTotal p b⟩

example (X : SSet.{u}) : (SSet.modelCategoryQuillen.standardCylinder X).IsGood := inferInstance

example {X Y : SSet.{u}} (f : X ⟶ Y) : (SSet.modelCategoryQuillen.standardCylinder X).I ⟶ Y :=
  CartesianMonoidalCategory.fst X (Δ[1] : SSet.{u}) ≫ f

#print axioms TopCat.homotopyPullbackComparison
#print axioms TopCat.homotopyPullbackComparison_naturality
#print axioms TopCat.homotopyPullbackComparison_pointFiber
#print axioms TopCat.homotopyPullbackComparison_mem_of_isPullback
#print axioms TopCat.homotopyPullbackComparison_mem_of_twoSetOpenCover
#print axioms TopCat.strictFiberToHomotopyFiber_mem_of_twoSetOpenCover
#print axioms SSet.modelCategoryQuillen.standardCylinder
#print axioms SSet.modelCategoryQuillen.standardCylinder_isGood
