/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompleteness
public import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open SSet.Rezk SSet.Rezk.FiniteCompleteness

namespace MathlibExtTest.SimplicialSpace.FiniteCompleteness

/-- The two source edge labels have the original ordered endpoints. -/
theorem ordered_edges :
    (edge02.toOrderHom 0 = 0 ∧ edge02.toOrderHom 1 = 2) ∧
      (edge13.toOrderHom 0 = 1 ∧ edge13.toOrderHom 1 = 3) :=
  ⟨edge02_vertices, edge13_vertices⟩

/-- Arbitrary compatible original labels descend through both selected pushouts,
with all three prescribed legs retained. -/
theorem exists_map_preserving_legs (W : SimplicialObject SSet.{u})
    (a c : representable.{u} 0 ⟶ W) (b : representable.{u} 3 ⟶ W)
    (h02 : representableCollapse.{u} 1 ≫ a =
      SSet.simplicialSpaceDiscrete.map (SSet.stdSimplex.map edge02) ≫ b)
    (h13 : SSet.simplicialSpaceDiscrete.map (SSet.stdSimplex.map edge13) ≫ b =
      representableCollapse.{u} 1 ≫ c) :
    ∃ f : K.{u} ⟶ W,
      (stage1Cocone.inl ≫ stage2Cocone.inl ≫ f = a) ∧
        (stage1Cocone.inr ≫ stage2Cocone.inl ≫ f = b) ∧
          stage2Cocone.inr ≫ f = c := by
  let d : stage1.{u} ⟶ W := pushout.desc a b h02
  have hd0 : stage1Cocone.inl ≫ d = a := pushout.inl_desc a b h02
  have hd3 : stage1Cocone.inr ≫ d = b := pushout.inr_desc a b h02
  have hd13 : secondLeg.{u} ≫ d = representableCollapse.{u} 1 ≫ c := by
    dsimp only [secondLeg]
    rw [Category.assoc, hd3, h13]
  let f : K.{u} ⟶ W := pushout.desc d c hd13
  have hf0 : stage2Cocone.inl ≫ f = d := pushout.inl_desc d c hd13
  have hf1 : stage2Cocone.inr ≫ f = c := pushout.inr_desc d c hd13
  refine ⟨f, ?_, ?_, hf1⟩
  · rw [hf0, hd0]
  · rw [hf0, hd3]

/-- The same original three legs determine a map uniquely. -/
theorem map_unique_from_legs {W : SimplicialObject SSet.{u}}
    (f g : K.{u} ⟶ W)
    (h0 : stage1Cocone.inl ≫ stage2Cocone.inl ≫ f =
      stage1Cocone.inl ≫ stage2Cocone.inl ≫ g)
    (h3 : stage1Cocone.inr ≫ stage2Cocone.inl ≫ f =
      stage1Cocone.inr ≫ stage2Cocone.inl ≫ g)
    (h1 : stage2Cocone.inr ≫ f = stage2Cocone.inr ≫ g) : f = g := by
  apply pushout.hom_ext
  · apply pushout.hom_ext
    · exact h0
    · exact h3
  · exact h1

/-- Both selected cocones remain colimiting at every original outer degree. -/
theorem colimits_in_every_degree (m : SimplexCategoryᵒᵖ) :
    Nonempty (IsColimit
      (((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj m).mapCocone stage1Cocone.{u})) ∧
      Nonempty (IsColimit
        (((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj m).mapCocone stage2Cocone.{u})) :=
  ⟨⟨stage1PointwiseIsColimit m⟩, ⟨stage2PointwiseIsColimit m⟩⟩

/-- The original four collapse equations retain the same maps after designation. -/
theorem designated_collapse_equations :
    (SimplicialSpace.ofSimplicialObject.map stage1Cocone.{u}.inl ≫
      SimplicialSpace.ofSimplicialObject.map stage2Cocone.inl ≫
        SimplicialSpace.ofSimplicialObject.map kappa =
          𝟙 (SimplicialSpace.ofSimplicialObject.obj (representable.{u} 0))) ∧
    (SimplicialSpace.ofSimplicialObject.map stage1Cocone.{u}.inr ≫
      SimplicialSpace.ofSimplicialObject.map stage2Cocone.inl ≫
        SimplicialSpace.ofSimplicialObject.map kappa =
          SimplicialSpace.ofSimplicialObject.map (representableCollapse.{u} 3)) ∧
    (SimplicialSpace.ofSimplicialObject.map stage2Cocone.{u}.inr ≫
      SimplicialSpace.ofSimplicialObject.map kappa =
        𝟙 (SimplicialSpace.ofSimplicialObject.obj (representable.{u} 0))) ∧
    (SimplicialSpace.ofSimplicialObject.map completenessMap.{u} ≫
      SimplicialSpace.ofSimplicialObject.map epsilon =
        𝟙 (SimplicialSpace.ofSimplicialObject.obj (representable.{u} 0))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply InducedCategory.hom_ext
    exact kappa_first.{u}
  · apply InducedCategory.hom_ext
    exact kappa_mid.{u}
  · apply InducedCategory.hom_ext
    exact kappa_last.{u}
  · apply InducedCategory.hom_ext
    exact completenessMap_epsilon.{u}

/-- The two distinct original source objects keep their own collapse uniqueness statements. -/
theorem both_original_collapses_unique
    (f : K.{u} ⟶ representable.{u} 0)
    (g : walkingIsomorphism.{u} ⟶ representable.{u} 0) :
    f = kappa ∧ g = epsilon :=
  ⟨kappa_unique f, epsilon_unique g⟩

example : Nonempty (IsColimit stage1Cocone.{0}) ∧
    Nonempty (IsColimit stage2Cocone.{0}) :=
  ⟨⟨stage1IsColimit⟩, ⟨stage2IsColimit⟩⟩

example : Nonempty (IsColimit stage1Cocone.{1}) ∧
    Nonempty (IsColimit stage2Cocone.{1}) :=
  ⟨⟨stage1IsColimit⟩, ⟨stage2IsColimit⟩⟩

example (m : SimplexCategoryᵒᵖ) :
    Nonempty (IsColimit
      (((evaluation SimplexCategoryᵒᵖ SSet.{1}).obj m).mapCocone stage1Cocone.{1})) ∧
      Nonempty (IsColimit
        (((evaluation SimplexCategoryᵒᵖ SSet.{1}).obj m).mapCocone stage2Cocone.{1})) :=
  colimits_in_every_degree m

end MathlibExtTest.SimplicialSpace.FiniteCompleteness
