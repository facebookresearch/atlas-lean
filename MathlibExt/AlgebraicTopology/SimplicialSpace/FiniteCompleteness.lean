/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingMaps
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The finite completeness object

Johnson-Freyd–Scheimbauer, *Twisted quantum field theories*, Example A.10,
uses `F(0) ⨿_{F(1)} F(3) ⨿_{F(1)} F(0)`, collapsing the edges 02 and 13.
Here `F(n)` is the existing inner-discrete outer representable. Both pushouts
are the chosen native pushouts, and their original cocones remain explicit.

Horel, *A model structure on internal categories in simplicial sets*,
Definition 2.2, uses the collapse of the full walking-isomorphism nerve to
`F(0)`. The existing selected vertex is a section of that collapse.

These are raw objects and maps. The finite object is distinct from both the
full walking-isomorphism nerve and the finite two-triangle Joyal interval.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet.Rezk.FiniteCompleteness

/-- The first collapsed edge of the three-simplex, from vertex zero to two. -/
def edge02 : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 3 :=
  SimplexCategory.intervalEdge 0 2 (by decide)

/-- The second collapsed edge, from vertex one to three. -/
def edge13 : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 3 :=
  SimplexCategory.intervalEdge 1 2 (by decide)

/-- The ordered vertices of the first collapsed edge. -/
theorem edge02_vertices :
    edge02.toOrderHom 0 = 0 ∧ edge02.toOrderHom 1 = 2 := by
  decide

/-- The ordered vertices of the second collapsed edge. -/
theorem edge13_vertices :
    edge13.toOrderHom 0 = 1 ∧ edge13.toOrderHom 1 = 3 := by
  decide

private def representableZeroIsTerminal : IsTerminal (representable.{u} 0) := by
  have h : IsTerminal (Δ[0] : SSet.{u}) := by
    change IsTerminal ((uliftYoneda : SimplexCategory ⥤ SSet.{u}).obj ⦋0⦌)
    exact SimplexCategory.isTerminalZero.isTerminalObj
      (uliftYoneda : SimplexCategory ⥤ SSet.{u}) _
  exact h.isTerminalObj SSet.simplicialSpaceDiscrete _

/-- The unique collapse of the original representable to the zero representable. -/
def representableCollapse (n : ℕ) : representable.{u} n ⟶ representable.{u} 0 :=
  SSet.simplicialSpaceDiscrete.map
    (stdSimplex.map (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0))

/-- The chosen first pushout, which collapses the original 02 edge. -/
abbrev stage1 : SimplicialObject SSet.{u} :=
  pushout (representableCollapse.{u} 1)
    (SSet.simplicialSpaceDiscrete.map (stdSimplex.map edge02))

/-- The actual first cocone, with its original two injections. -/
abbrev stage1Cocone : PushoutCocone (representableCollapse.{u} 1)
    (SSet.simplicialSpaceDiscrete.map (stdSimplex.map edge02)) :=
  pushout.cocone _ _

/-- The chosen first cocone is a colimit. -/
def stage1IsColimit : IsColimit stage1Cocone.{u} :=
  pushout.isColimit _ _

/-- The first cocone is colimiting in every original outer degree. -/
def stage1PointwiseIsColimit (m : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj m).mapCocone
      stage1Cocone.{u}) :=
  isColimitOfPreserves ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj m)
    stage1IsColimit

/-- The original 13 edge followed by the same first cocone's three-simplex injection. -/
def secondLeg : representable.{u} 1 ⟶ stage1.{u} :=
  SSet.simplicialSpaceDiscrete.map (stdSimplex.map edge13) ≫ stage1Cocone.inr

/-- The finite completeness object, with the second edge collapsed by a chosen pushout. -/
abbrev K : SimplicialObject SSet.{u} :=
  pushout secondLeg.{u} (representableCollapse.{u} 1)

/-- The actual second cocone, retaining the middle object and last point. -/
abbrev stage2Cocone : PushoutCocone secondLeg.{u} (representableCollapse.{u} 1) :=
  pushout.cocone _ _

/-- The chosen second cocone is a colimit. -/
def stage2IsColimit : IsColimit stage2Cocone.{u} :=
  pushout.isColimit _ _

/-- The second cocone is colimiting in every original outer degree. -/
def stage2PointwiseIsColimit (m : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj m).mapCocone
      stage2Cocone.{u}) :=
  isColimitOfPreserves ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj m)
    stage2IsColimit

/-- The original unique collapse of the finite completeness object. -/
def kappa : K.{u} ⟶ representable.{u} 0 where
  app m :=
    { app _ := ↾fun _ => ULift.up (SimplexCategory.const m.unop (SimplexCategory.mk 0) 0)
      naturality _ _ _ := by ext x; rfl }
  naturality _ _ _ := by
    ext n x
    rfl

/-- The first point followed through both chosen pushouts and the collapse is the identity. -/
@[reassoc]
theorem kappa_first :
    stage1Cocone.{u}.inl ≫ stage2Cocone.inl ≫ kappa = 𝟙 (representable.{u} 0) :=
  representableZeroIsTerminal.hom_ext _ _

/-- The original three-simplex restriction is its original collapse. -/
@[reassoc]
theorem kappa_mid :
    stage1Cocone.{u}.inr ≫ stage2Cocone.inl ≫ kappa = representableCollapse.{u} 3 :=
  representableZeroIsTerminal.hom_ext _ _

/-- The last point followed by the collapse is the identity. -/
@[reassoc]
theorem kappa_last :
    stage2Cocone.{u}.inr ≫ kappa = 𝟙 (representable.{u} 0) :=
  representableZeroIsTerminal.hom_ext _ _

/-- Every map from this finite object to the original zero representable is the same collapse. -/
theorem kappa_unique (f : K.{u} ⟶ representable.{u} 0) : f = kappa :=
  representableZeroIsTerminal.hom_ext _ _

/-- Horel's original collapse of the existing full walking-isomorphism nerve. -/
def epsilon : walkingIsomorphism.{u} ⟶ representable.{u} 0 where
  app m :=
    { app _ := ↾fun _ => ULift.up (SimplexCategory.const m.unop (SimplexCategory.mk 0) 0)
      naturality _ _ _ := by ext x; rfl }
  naturality _ _ _ := by
    ext n x
    rfl

/-- Every collapse of the full original nerve is this same map. -/
theorem epsilon_unique (f : walkingIsomorphism.{u} ⟶ representable.{u} 0) :
    f = epsilon :=
  representableZeroIsTerminal.hom_ext _ _

/-- The existing zero-selected completeness map is a section of the full-nerve collapse. -/
@[reassoc]
theorem completenessMap_epsilon :
    completenessMap.{u} ≫ epsilon = 𝟙 (representable.{u} 0) :=
  representableZeroIsTerminal.hom_ext _ _

end SSet.Rezk.FiniteCompleteness
