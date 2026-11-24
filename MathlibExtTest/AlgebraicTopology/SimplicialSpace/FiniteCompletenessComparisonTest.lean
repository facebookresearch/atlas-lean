/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompletenessComparison

/-! # Original simplex and pushout consumers of the raw finite completeness comparison -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open SSet SSet.Rezk SSet.Rezk.FiniteCompleteness
open scoped Simplicial

namespace FiniteCompletenessComparisonTest

/-- Every original simplex operator restricts the same whole middle simplex through K. -/
theorem middle_restriction {n : ℕ} (θ : ⦋n⦌ ⟶ ⦋3⦌) :
    SSet.simplicialSpaceDiscrete.map (stdSimplex.map θ) ≫
        stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
      SSet.simplicialSpaceDiscrete.map
        (SSet.yonedaEquiv.symm
          (coherentIso.{u}.map θ.op
            (ComposableArrows.mk₃ WalkingIso.iso.hom WalkingIso.iso.inv WalkingIso.iso.hom))) := by
  rw [comparison_mid]
  simpa only [comparisonSimplex, Functor.map_comp] using
    congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ coherentIso.{u} =>
      SSet.simplicialSpaceDiscrete.map f)
      (SSet.yonedaEquiv_symm_naturality_left θ
        (ComposableArrows.mk₃ WalkingIso.iso.{u}.hom WalkingIso.iso.inv WalkingIso.iso.hom))

private theorem restrict_eq {n : ℕ} (θ : ⦋n⦌ ⟶ ⦋3⦌) (x : coherentIso.{u} _⦋n⦌)
    (hx : coherentIso.{u}.map θ.op
      (ComposableArrows.mk₃ WalkingIso.iso.hom WalkingIso.iso.inv WalkingIso.iso.hom) = x) :
    SSet.simplicialSpaceDiscrete.map (stdSimplex.map θ) ≫
        stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
      SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm x) := by
  rw [middle_restriction, hx]

/-- The four original vertices of the actual middle simplex are zero, one, zero, one. -/
theorem alternating_vertices :
    (SSet.simplicialSpaceDiscrete.map
        (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ 0)) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison = completenessMap.{u}) ∧
    (SSet.simplicialSpaceDiscrete.map
        (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ 1)) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
        SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm coherentIso.x₁)) ∧
    (SSet.simplicialSpaceDiscrete.map
        (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ 2)) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison = completenessMap.{u}) ∧
    (SSet.simplicialSpaceDiscrete.map
        (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ 3)) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
        SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm coherentIso.x₁)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact restrict_eq (SimplexCategory.const ⦋0⦌ ⦋3⦌ 0) coherentIso.x₀
      (ComposableArrows.ext₀ rfl)
  · exact restrict_eq (SimplexCategory.const ⦋0⦌ ⦋3⦌ 1) coherentIso.x₁
      (ComposableArrows.ext₀ rfl)
  · exact restrict_eq (SimplexCategory.const ⦋0⦌ ⦋3⦌ 2) coherentIso.x₀
      (ComposableArrows.ext₀ rfl)
  · exact restrict_eq (SimplexCategory.const ⦋0⦌ ⦋3⦌ 3) coherentIso.x₁
      (ComposableArrows.ext₀ rfl)

/-- All four faces retain the original unit triangles and original forward-edge degeneracies. -/
theorem full_faces :
    (SSet.simplicialSpaceDiscrete.map (stdSimplex.δ (3 : Fin 4)) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
        SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm coherentIso.homInvId.simplex)) ∧
    (SSet.simplicialSpaceDiscrete.map (stdSimplex.δ (0 : Fin 4)) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
        SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm coherentIso.invHomId.simplex)) ∧
    (SSet.simplicialSpaceDiscrete.map (stdSimplex.δ (1 : Fin 4)) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
        SSet.simplicialSpaceDiscrete.map
          (SSet.yonedaEquiv.symm (coherentIso.{u}.σ (0 : Fin 2) coherentIso.hom.edge))) ∧
    (SSet.simplicialSpaceDiscrete.map (stdSimplex.δ (2 : Fin 4)) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
        SSet.simplicialSpaceDiscrete.map
          (SSet.yonedaEquiv.symm (coherentIso.{u}.σ (1 : Fin 2) coherentIso.hom.edge))) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply restrict_eq <;>
    apply CategoryTheory.nerve.ext_of_isThin <;>
    funext i <;> fin_cases i <;> rfl

/-- The three consecutive edges are forward, inverse, forward in the full original nerve. -/
theorem consecutive_edges :
    (SSet.simplicialSpaceDiscrete.map (stdSimplex.map (SimplexCategory.mkOfSucc (0 : Fin 3))) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
        SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm coherentIso.hom.edge)) ∧
    (SSet.simplicialSpaceDiscrete.map (stdSimplex.map (SimplexCategory.mkOfSucc (1 : Fin 3))) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
        SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm coherentIso.inv.edge)) ∧
    (SSet.simplicialSpaceDiscrete.map (stdSimplex.map (SimplexCategory.mkOfSucc (2 : Fin 3))) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
        SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm coherentIso.hom.edge)) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply restrict_eq <;>
    apply CategoryTheory.nerve.ext_of_isThin <;>
    funext i <;> fin_cases i <;> rfl

/-- The same original 02 and 13 edges factor through the source and target point collapses. -/
theorem collapsed_edges :
    (SSet.simplicialSpaceDiscrete.map (stdSimplex.map edge02) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
        representableCollapse.{u} 1 ≫ completenessMap.{u}) ∧
    (SSet.simplicialSpaceDiscrete.map (stdSimplex.map edge13) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
        representableCollapse.{u} 1 ≫
          SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm coherentIso.x₁)) := by
  constructor
  · rw [comparison_mid]
    exact edge02_comparisonSimplex
  · rw [comparison_mid]
    exact edge13_comparisonSimplex

/-- The remaining long edge 03 is the same original forward isomorphism. -/
theorem edge03 :
    SSet.simplicialSpaceDiscrete.map
        (stdSimplex.map (SimplexCategory.intervalEdge 0 3 (by decide))) ≫
      stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison =
        SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm coherentIso.hom.edge) := by
  apply restrict_eq
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- Both chosen stages and the original finite/full collapses are retained in every universe. -/
theorem chosen_stages_and_collapse :
    (stage1Cocone.{u}.inl ≫ comparisonStage1 = completenessMap.{u}) ∧
    (stage1Cocone.{u}.inr ≫ comparisonStage1 = comparisonSimplex.{u}) ∧
    (stage2Cocone.{u}.inl ≫ comparison = comparisonStage1.{u}) ∧
    (stage2Cocone.{u}.inr ≫ comparison =
      SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm coherentIso.x₁)) ∧
    (comparison.{u} ≫ epsilon = kappa.{u}) := by
  refine ⟨comparisonStage1_first, comparisonStage1_mid, ?_, comparison_last,
    comparison_epsilon⟩
  exact pushout.inl_desc _ _ _

/-- The original factorization still typechecks after raising the value universe. -/
theorem raised_universe : comparison.{u + 1} ≫ epsilon = kappa.{u + 1} :=
  comparison_epsilon

end FiniteCompletenessComparisonTest
