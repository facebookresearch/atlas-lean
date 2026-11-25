/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalCofibrationSliceIntersection

set_option autoImplicit false
noncomputable section

universe w uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open CategoryTheory.SmallObject.DiagramSliceExhaustion
open HomotopicalAlgebra HomotopicalAlgebra.FunctorInjective

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] (s : Functor.EssentialIndexData.{w} D C)
  (b : BoundedConstruction d kappaLP s.equivalence)
  {F G : D ⥤ C} (f : F ⟶ G) (hf : ∀ a : D, cofibrations C (f.app a))

-- Consume both actual maps, their original chosen lower legs, both bounds and full f equations.
example :
    letI := originalComponentOrders d kappaLP s.equivalence b f hf
    let theta := originalComponentPresentation d kappaLP s.equivalence b f hf
    ∀ (L : ∀ a : D, LowerSetColimitData (theta.component a).tree.diagram)
      (A : OriginalSlice theta L) (_ : HasCardinalLT (Arrow D) b.cardinal)
      (seed : DiagramActionCapture.Supports
        (P := originalComponentLabels d kappaLP s.equivalence b f hf) b.cardinal),
      ∃ (N Nprime : DiagramSliceExtensions.Slice theta L b.cardinal)
        (iA : OriginalSlice.Inclusion (OriginalSlice.ofBounded b.cardinal Nprime) A)
        (iN : OriginalSlice.Inclusion (OriginalSlice.ofBounded b.cardinal Nprime)
          (OriginalSlice.ofBounded b.cardinal N)),
        (∀ a, seed a ≤ N.supports a) ∧
        (∀ a, (Nprime.supports a).1 = A.supports a ⊓ (N.supports a).1) ∧
        (∀ a, iA.toNatTrans.app a = ((L a).map (iA.le a)).right) ∧
        (∀ a, iN.toNatTrans.app a = ((L a).map (iN.le a)).right) ∧
        (OriginalSlice.ofBounded b.cardinal Nprime).root ≫
          (OriginalSlice.ofBounded b.cardinal Nprime).target = f ∧
        (OriginalSlice.ofBounded b.cardinal N).root ≫
          (OriginalSlice.ofBounded b.cardinal N).target = f := by
  let _ := originalComponentOrders d kappaLP s.equivalence b f hf
  dsimp only
  intro L A hArrow seed
  obtain ⟨N, Nprime, hseed, hintersection, ⟨iA⟩, ⟨iN⟩⟩ :=
    originalCofibrationSliceIntersection d kappaLP s b f hf L A hArrow seed
  refine ⟨N, Nprime, iA, iN, hseed, hintersection, (fun _ => rfl), (fun _ => rfl), ?_, ?_⟩
  · exact OriginalSlice.factor (OriginalSlice.ofBounded b.cardinal Nprime)
  · exact OriginalSlice.factor (OriginalSlice.ofBounded b.cardinal N)
