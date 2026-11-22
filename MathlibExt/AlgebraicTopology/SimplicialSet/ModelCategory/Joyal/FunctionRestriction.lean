/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalCategoricalEquivalences
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FibrantObjects
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.GenuineTrivialFibrations

/-!
# Genuine categorical fibrations between functor quasicategories

Restriction along a monomorphism `i : A ⟶ B` induces a genuine Joyal
categorical fibration `Q^B ⟶ Q^A` for every quasicategory `Q`.  When `i`
is also a categorical equivalence, this restriction map is a genuine trivial
categorical fibration.

The fibration proof is the closed form of the pushout-product argument.  A
monic categorical equivalence `j` is identified with an interval-testing
equivalence, so the corner `i □ j` is a monic testing equivalence.  It lifts
against the terminal map of `Q`; the terminal tensor–Hom adjunction turns this
lift into the required lift of `j` against restriction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped Simplicial

namespace SSet

/-- For a quasicategory `Q`, restriction along a monomorphism is a genuine
categorical fibration between the function quasicategories. -/
theorem categoricalFibrations_pre_app_of_mono {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (Q : SSet.{u}) [Quasicategory Q] :
    categoricalFibrations ((pre i).app Q) := by
  rw [categoricalFibrations.mem_iff]
  intro X Y j hj hW
  let _ : Mono j := hj
  have hjTesting :
      joyalInterval.productPrecylinder.testingEquivalences
        joyalInterval.auxiliaryAnodyneExtensions j := by
    rw [joyalInterval.testingEquivalences_eq_categoricalEquivalences]
    exact hW
  have hc := joyalInterval.testingTrivialCofibrations_pushoutProduct
    i j (.inr hjTesting)
  have hc' :=
    (joyalInterval.productPrecylinder.testingTrivialCofibrations_iff
      joyalInterval.auxiliaryAnodyneExtensions (Arrow.mk i □ Arrow.mk j).hom).mp hc
  have hcW : categoricalEquivalences (Arrow.mk i □ Arrow.mk j).hom := by
    rw [← joyalInterval.testingEquivalences_eq_categoricalEquivalences]
    exact hc'.2
  let t : IsTerminal (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀
  let p : Q ⟶ (Δ[0] : SSet.{u}) := t.from Q
  have hp : categoricalFibrations p := by
    let e : (Δ[0] : SSet.{u}) ≅ ⊤_ SSet.{u} :=
      t.uniqueUpToIso terminalIsTerminal
    have hp' : categoricalFibrations (terminal.from Q) :=
      (categoricalFibrations.terminalFrom_iff_quasicategory Q).2 inferInstance
    have hpComp : categoricalFibrations (p ≫ e.hom) := by
      rw [terminalIsTerminal.hom_ext (p ≫ e.hom) (terminal.from Q)]
      exact hp'
    exact (MorphismProperty.cancel_right_of_respectsIso
      categoricalFibrations p e.hom).1 hpComp
  have hLP : HasLiftingProperty (Arrow.mk i □ Arrow.mk j).hom p :=
    (categoricalFibrations.mem_iff p).1 hp _ hc'.1 hcW
  exact (MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_isTerminal_iff
    (f := i) (g := j) (X := Q) t).mp hLP

/-- If a monomorphism `i` is also a categorical equivalence, restriction
along `i` into a quasicategory is both a genuine categorical fibration and a
categorical equivalence. Equivalently, it is a genuine trivial categorical
fibration. -/
theorem categoricalFibrations_and_categoricalEquivalences_pre_app_of_mono
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (hi : categoricalEquivalences i)
    (Q : SSet.{u}) [Quasicategory Q] :
    categoricalFibrations ((pre i).app Q) ∧
      categoricalEquivalences ((pre i).app Q) := by
  have hiTesting :
      joyalInterval.productPrecylinder.testingEquivalences
        joyalInterval.auxiliaryAnodyneExtensions i := by
    rw [joyalInterval.testingEquivalences_eq_categoricalEquivalences]
    exact hi
  have hiTrivial :
      joyalInterval.productPrecylinder.testingTrivialCofibrations
        joyalInterval.auxiliaryAnodyneExtensions i :=
    (joyalInterval.productPrecylinder.testingTrivialCofibrations_iff
      joyalInterval.auxiliaryAnodyneExtensions i).2 ⟨inferInstance, hiTesting⟩
  have hMonoRLP : (MorphismProperty.monomorphisms SSet.{u}).rlp
      ((pre i).app Q) :=
    joyalInterval.testingTrivialCofibrations_rlp_pre i hiTrivial
  have hBoundaryRLP : modelCategoryQuillen.I.rlp ((pre i).app Q) := by
    rw [← rlp_monomorphisms]
    exact hMonoRLP
  exact (categoricalFibrations_and_categoricalEquivalences_iff _).2 hBoundaryRLP

end SSet
