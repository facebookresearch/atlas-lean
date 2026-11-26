/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompleteness
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The original finite completeness map to the full walking isomorphism

The full alternating three-simplex `(zero, one, zero, one)` has identity restrictions on the
original edges 02 and 13. It descends through the two existing chosen pushouts defining `K`.
Both original point restrictions and the whole three-simplex restriction are retained. Its
composite with the original full-nerve collapse is the original finite collapse.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.Rezk.FiniteCompleteness

private abbrev alternatingSimplex : coherentIso.{u} _⦋3⦌ :=
  ComposableArrows.mk₃ WalkingIso.iso.{u}.hom WalkingIso.iso.inv WalkingIso.iso.hom

private theorem scalar_edge02 :
    stdSimplex.map edge02 ≫ yonedaEquiv.symm alternatingSimplex.{u} =
      stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) ≫
        yonedaEquiv.symm coherentIso.x₀ := by
  rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left]
  apply congrArg yonedaEquiv.symm
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem scalar_edge13 :
    stdSimplex.map edge13 ≫ yonedaEquiv.symm alternatingSimplex.{u} =
      stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) ≫
        yonedaEquiv.symm coherentIso.x₁ := by
  rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left]
  apply congrArg yonedaEquiv.symm
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The actual full alternating three-simplex, made discrete in the inner direction. -/
def comparisonSimplex : representable.{u} 3 ⟶ walkingIsomorphism.{u} :=
  SSet.simplicialSpaceDiscrete.map
    (yonedaEquiv.symm
      (ComposableArrows.mk₃ WalkingIso.iso.{u}.hom WalkingIso.iso.inv WalkingIso.iso.hom))

/-- The original 02 edge of the whole comparison simplex is the constant source point. -/
@[reassoc]
theorem edge02_comparisonSimplex :
    SSet.simplicialSpaceDiscrete.map (stdSimplex.map edge02) ≫ comparisonSimplex.{u} =
      representableCollapse.{u} 1 ≫ completenessMap.{u} := by
  simpa only [comparisonSimplex, representableCollapse, completenessMap, Functor.map_comp]
    using congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ coherentIso.{u} =>
      SSet.simplicialSpaceDiscrete.map f) scalar_edge02

/-- The original 13 edge of the whole comparison simplex is the constant target point. -/
@[reassoc]
theorem edge13_comparisonSimplex :
    SSet.simplicialSpaceDiscrete.map (stdSimplex.map edge13) ≫ comparisonSimplex.{u} =
      representableCollapse.{u} 1 ≫
        SSet.simplicialSpaceDiscrete.map (yonedaEquiv.symm coherentIso.x₁) := by
  simpa only [comparisonSimplex, representableCollapse, Functor.map_comp]
    using congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ coherentIso.{u} =>
      SSet.simplicialSpaceDiscrete.map f) scalar_edge13

/-- Descend through the actual first chosen pushout, retaining its source point and simplex. -/
def comparisonStage1 : stage1.{u} ⟶ walkingIsomorphism.{u} :=
  pushout.desc completenessMap comparisonSimplex edge02_comparisonSimplex.symm

/-- The first chosen pushout's original point maps to the existing source vertex. -/
@[reassoc]
theorem comparisonStage1_first :
    stage1Cocone.{u}.inl ≫ comparisonStage1 = completenessMap.{u} := by
  exact pushout.inl_desc _ _ _

/-- The first chosen pushout's original simplex maps to the same whole alternating simplex. -/
@[reassoc]
theorem comparisonStage1_mid :
    stage1Cocone.{u}.inr ≫ comparisonStage1 = comparisonSimplex.{u} := by
  exact pushout.inr_desc _ _ _

/-- The closed original comparison from the same finite object to the same full nerve. -/
def comparison : K.{u} ⟶ walkingIsomorphism.{u} :=
  pushout.desc comparisonStage1
    (SSet.simplicialSpaceDiscrete.map (yonedaEquiv.symm coherentIso.x₁)) (by
      unfold secondLeg
      rw [Category.assoc, comparisonStage1_mid]
      exact edge13_comparisonSimplex)

/-- The original first point through both chosen pushouts maps to the source vertex. -/
@[reassoc]
theorem comparison_first :
    stage1Cocone.{u}.inl ≫ stage2Cocone.inl ≫ comparison = completenessMap.{u} := by
  change stage1Cocone.inl ≫ pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]
  exact comparisonStage1_first

/-- The original middle simplex through both chosen pushouts remains the whole alternating
three-simplex, so all its original face and edge restrictions are retained. -/
@[reassoc]
theorem comparison_mid :
    stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ comparison = comparisonSimplex.{u} := by
  change stage1Cocone.inr ≫ pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]
  exact comparisonStage1_mid

/-- The original last point maps to the existing target vertex of the full nerve. -/
@[reassoc]
theorem comparison_last :
    stage2Cocone.{u}.inr ≫ comparison =
      SSet.simplicialSpaceDiscrete.map (yonedaEquiv.symm coherentIso.x₁) := by
  exact pushout.inr_desc _ _ _

/-- The original full-nerve collapse after the comparison is the original finite collapse. -/
@[reassoc]
theorem comparison_epsilon : comparison.{u} ≫ epsilon = kappa.{u} :=
  kappa_unique _

end SSet.Rezk.FiniteCompleteness
