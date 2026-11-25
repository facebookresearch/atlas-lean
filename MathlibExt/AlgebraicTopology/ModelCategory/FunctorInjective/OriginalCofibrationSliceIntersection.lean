/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCofibrationComponentTrees
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramSliceIntersection
public import MathlibExt.CategoryTheory.Functor.SmallIndex

/-!
# Compatible intersections for actual original coefficient cofibrations

The original coefficient model and its actual cofibrant-generation data construct
the good component trees at one selected rank. Every original lower-colimit choice,
unbounded compatible slice and bounded seed then has its genuine bounded receiving
slice and literal compatible intersection, with both full original natural maps.

## Source and scope

This is the original-cofibration application of Jacob Lurie's *Higher Topos Theory*,
Lemma A.3.3.16 in the proof of Lemma A.3.3.3, author PDF dated April 9, 2017
(2017-04-09). The component trees are constructed by the original scalar producer,
using the goodification and compact retract arguments of A.1.5.7 and A.1.5.12–13.
The bound is on the arrows of the same actual bounded ordinary index D. Original
coefficient, object, Hom and working universes, the same f and all selected tree
labels and lower maps are retained. Whole transfinite filtration, generator
exhaustion and model recognition are separate constructions.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open CategoryTheory.SmallObject.DiagramSliceExhaustion
open HomotopicalAlgebra HomotopicalAlgebra.FunctorInjective

namespace HomotopicalAlgebra.FunctorInjective

attribute [local instance] CategoryTheory.Functor.EssentialIndexData.indexCategory

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] (s : Functor.EssentialIndexData.{w} D C)
  (b : BoundedConstruction d kappaLP s.equivalence)
  {F G : D ⥤ C} (f : F ⟶ G) (hf : ∀ a : D, cofibrations C (f.app a))

/-- The original model constructs the component trees before intersecting arbitrary
original slices. Every actual lower-colimit choice is allowed, and both original
action inclusions and the literal support intersection are retained. -/
theorem originalCofibrationSliceIntersection :
    letI := originalComponentOrders d kappaLP s.equivalence b f hf
    let theta := originalComponentPresentation d kappaLP s.equivalence b f hf
    ∀ (L : ∀ a : D, LowerSetColimitData (theta.component a).tree.diagram)
      (A : OriginalSlice theta L)
      (_ : HasCardinalLT (Arrow D) b.cardinal)
      (seed : DiagramActionCapture.Supports
        (P := originalComponentLabels d kappaLP s.equivalence b f hf) b.cardinal),
      ∃ (N Nprime : DiagramSliceExtensions.Slice theta L b.cardinal),
        (∀ a, seed a ≤ N.supports a) ∧
        (∀ a, (Nprime.supports a).1 = A.supports a ⊓ (N.supports a).1) ∧
        Nonempty (OriginalSlice.Inclusion (OriginalSlice.ofBounded b.cardinal Nprime) A) ∧
        Nonempty (OriginalSlice.Inclusion (OriginalSlice.ofBounded b.cardinal Nprime)
          (OriginalSlice.ofBounded b.cardinal N)) := by
  let _ := originalComponentOrders d kappaLP s.equivalence b f hf
  dsimp only
  let theta := originalComponentPresentation d kappaLP s.equivalence b f hf
  intro L A hArrow seed
  let _ : IsCardinalLocallyPresentable C b.cardinal := b.profile.baseLocallyPresentable
  exact DiagramSliceIntersection.existsGenericBoundedCompatibleIntersection theta L A
    b.cardinal b.profile.uncountable hArrow (originalComponentGood d kappaLP s.equivalence b f hf)
        seed

end HomotopicalAlgebra.FunctorInjective
