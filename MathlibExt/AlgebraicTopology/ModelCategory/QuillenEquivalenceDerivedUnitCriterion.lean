/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

/-!
# Quillen equivalences from chosen derived units

For the original Quillen adjunction, retain a chosen fibrant replacement of
each left image, its actual trivial cofibration, and its complete adjunct.
Weak derived units and reflection of weak equivalences between fibrant objects
give the full cofibrant-source and fibrant-target Hovey criterion.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty

namespace CategoryTheory.Adjunction.IsQuillenEquivalence

/-- The chosen replacement maps and derived units imply the entire original
adjoint-map criterion. Reflection is required only between fibrant objects. -/
theorem mkOfDerivedUnitCriterion
    {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [adj.IsQuillenAdjunction]
    (replacement : C → D)
    (inclusion : ∀ X : C, L.obj X ⟶ replacement X)
    (hInclusion : ∀ X : C, trivialCofibrations D (inclusion X))
    (hFibrant : ∀ X : C, IsFibrant (replacement X))
    (hUnit : ∀ X : C, IsCofibrant X →
      WeakEquivalence (adj.homEquiv X (replacement X) (inclusion X)))
    (hReflect : ∀ {A B : D}, IsFibrant A → IsFibrant B →
      ∀ f : A ⟶ B, WeakEquivalence (R.map f) → WeakEquivalence f) :
    adj.IsQuillenEquivalence where
  toIsQuillenAdjunction := inferInstance
  homEquiv_weakEquivalence_iff {X Y} hXcof hYfib f := by
    let _ : Cofibration (inclusion X) := (cofibration_iff _).mpr (hInclusion X).1
    let _ : WeakEquivalence (inclusion X) := (weakEquivalence_iff _).mpr (hInclusion X).2
    let _ : IsFibrant (replacement X) := hFibrant X
    let u : X ⟶ R.obj (replacement X) :=
      adj.homEquiv X (replacement X) (inclusion X)
    let _ : WeakEquivalence u := hUnit X hXcof
    let sq : CommSq f (inclusion X) (terminal.from Y) (terminal.from (replacement X)) :=
      ⟨terminalIsTerminal.hom_ext _ _⟩
    have hLift : HasLiftingProperty (inclusion X) (terminal.from Y) := inferInstance
    let _ : sq.HasLift := hLift.sq_hasLift sq
    let g : replacement X ⟶ Y := sq.lift
    have hg : inclusion X ≫ g = f := sq.fac_left
    have hadj : adj.homEquiv X Y f = u ≫ R.map g := by
      rw [← hg, adj.homEquiv_naturality_right]
    have hf : WeakEquivalence f ↔ WeakEquivalence g := by
      rw [← hg]
      exact weakEquivalence_precomp_iff (inclusion X) g
    have ha : WeakEquivalence (adj.homEquiv X Y f) ↔ WeakEquivalence (R.map g) := by
      rw [hadj]
      exact weakEquivalence_precomp_iff u (R.map g)
    have hBrown : WeakEquivalence g ↔ WeakEquivalence (R.map g) := by
      constructor
      · intro h
        let _ : WeakEquivalence g := h
        exact IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) g
      · exact hReflect (hFibrant X) hYfib g
    simpa only [weakEquivalence_iff] using hf.trans (hBrown.trans ha.symm)

/-- MMSS Lemma A.2(iii), with the original full unit and every target arrow:
creation of target weak equivalences and weak units on all cofibrant sources
imply the complete cofibrant-source/fibrant-target adjoint-map criterion. -/
theorem mkOfUnitAndCreatesWeakEquivalences
    {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [adj.IsQuillenAdjunction]
    (hUnit : ∀ X : C, IsCofibrant X → WeakEquivalence (adj.unit.app X))
    (hCreate : ∀ {A B : D} (f : A ⟶ B),
      WeakEquivalence f ↔ WeakEquivalence (R.map f)) :
    adj.IsQuillenEquivalence where
  toIsQuillenAdjunction := inferInstance
  homEquiv_weakEquivalence_iff {X Y} hXcof _ f := by
    let _ : WeakEquivalence (adj.unit.app X) := hUnit X hXcof
    have hAdj : adj.homEquiv X Y f = adj.unit.app X ≫ R.map f :=
      adj.homEquiv_unit X Y f
    have ha : WeakEquivalence (adj.homEquiv X Y f) ↔ WeakEquivalence (R.map f) := by
      rw [hAdj]
      exact weakEquivalence_precomp_iff (adj.unit.app X) (R.map f)
    simpa only [weakEquivalence_iff] using (hCreate f).trans ha.symm

end CategoryTheory.Adjunction.IsQuillenEquivalence
