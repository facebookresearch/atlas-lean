/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalTestingCorners
public import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct

/-!
# Finite Joyal Interval Function Restriction
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped Simplicial
universe u
namespace SSet.joyalInterval

/-- Restriction along an actual monic testing equivalence lifts against all monos. -/
theorem testingTrivialCofibrations_rlp_pre
    {A B Q : SSet.{u}} [Quasicategory Q] (i : A ⟶ B)
    (hi : productPrecylinder.testingTrivialCofibrations auxiliaryAnodyneExtensions i) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((MonoidalClosed.pre i).app Q) := by
  let : MorphismProperty.HasFactorization auxiliaryAnodyneExtensions
      auxiliaryAnodyneExtensions.rlp := by
    change MorphismProperty.HasFactorization auxiliaryAnodyneExtensions auxiliaryNaiveFibrations
    infer_instance
  have hi' := (productPrecylinder.testingTrivialCofibrations_iff
    auxiliaryAnodyneExtensions i).mp hi
  let : Mono i := hi'.1
  let t : IsTerminal (Δ[0] : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀
  let p : Q ⟶ (Δ[0] : SSet.{u}) := t.from Q
  have hQ : auxiliaryAnodyneExtensions.naiveFibrantObjects Q := by
    change auxiliaryNaiveFibrantObjects Q
    exact (auxiliaryNaiveFibrantObjects_iff Q).mpr inferInstance
  have hp : auxiliaryAnodyneExtensions.naiveFibrations p :=
    (auxiliaryAnodyneExtensions.naiveFibrantObjects_iff_of_isTerminal p t).mp hQ
  have ht : auxiliaryAnodyneExtensions.naiveFibrantObjects (Δ[0] : SSet.{u}) := by
    rw [auxiliaryAnodyneExtensions.naiveFibrantObjects_iff_of_isTerminal
      (𝟙 (Δ[0] : SSet.{u})) t]
    exact MorphismProperty.rlp_of_isIso _ _
  have hpR : (auxiliaryAnodyneExtensions.naiveFibrations ⊓
      MorphismProperty.ofObjectProperty ⊤ auxiliaryAnodyneExtensions.naiveFibrantObjects) p :=
    ⟨hp, trivial, ht⟩
  intro U V j hj
  let : Mono j := hj
  have hc := testingTrivialCofibrations_pushoutProduct i j (.inl hi'.2)
  have hclass : productPrecylinder.testingTrivialCofibrations auxiliaryAnodyneExtensions =
      MorphismProperty.monomorphisms SSet.{u} ⊓
        (auxiliaryAnodyneExtensions.naiveFibrations ⊓
          MorphismProperty.ofObjectProperty ⊤ auxiliaryAnodyneExtensions.naiveFibrantObjects).llp :=
    HomotopicalAlgebra.Precylinder.IsAnodyneSystem.testingTrivialCofibrations_eq_inf_llp_naiveFibrantCodomain
      productPrecylinder.{u} auxiliaryAnodyneExtensions.{u}
  have hc' := (congrArg (fun W : MorphismProperty SSet.{u} ↦
    W (Arrow.mk i □ Arrow.mk j).hom) hclass).mp hc
  have hLP : HasLiftingProperty (Arrow.mk i □ Arrow.mk j).hom p := hc'.2 p hpR
  exact (MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_isTerminal_iff
    (f := i) (g := j) (X := Q) t).mp hLP
end SSet.joyalInterval
