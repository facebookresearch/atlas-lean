/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# A fibrant-source criterion for Quillen equivalences

To recognize a Quillen equivalence, it suffices to check the adjoint-map
criterion on bifibrant sources and fibrant targets. A trivial cofibration
into a fibrant replacement of the original cofibrant source gives the reduction.

The original Formal-Math development is by Tsutomu Okano and Avocado.
-/

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty

universe u v u' v'

namespace CategoryTheory.Adjunction.IsQuillenEquivalence

/-- For a Quillen adjunction, checking the adjoint-map criterion on bifibrant sources and
fibrant targets suffices for the full Quillen equivalence criterion. -/
public theorem mkOfFibrantSourceCriterion
    {C : Type u} [Category.{v} C] [ModelCategory C]
    {D : Type u'} [Category.{v'} D] [ModelCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [hQ : adj.IsQuillenAdjunction]
    (hcrit : ∀ (X : C) (Y : D) [IsCofibrant X] [IsFibrant X] [IsFibrant Y]
      (f : L.obj X ⟶ Y),
      weakEquivalences D f ↔ weakEquivalences C (adj.homEquiv X Y f)) :
    adj.IsQuillenEquivalence where
  toIsQuillenAdjunction := hQ
  homEquiv_weakEquivalence_iff {X Y} _ _ f := by
    let fac := factorizationData (trivialCofibrations C) (fibrations C) (terminal.from X)
    have : Cofibration fac.i := (cofibration_iff _).mpr fac.hi.1
    have : WeakEquivalence fac.i := (weakEquivalence_iff _).mpr fac.hi.2
    have : IsFibrant fac.Z := (isFibrant_iff_of_isTerminal fac.p terminalIsTerminal).mpr
      ((fibration_iff _).mpr fac.hp)
    have : IsCofibrant fac.Z := isCofibrant_of_cofibration fac.i
    have hLi := hQ.preservesTrivialCofibrations _ fac.hi
    have : WeakEquivalence (L.map fac.i) := (weakEquivalence_iff _).mpr hLi.2
    let sq : CommSq f (L.map fac.i) (terminal.from Y) (terminal.from (L.obj fac.Z)) :=
      ⟨terminalIsTerminal.hom_ext _ _⟩
    have hp : HasLiftingProperty (L.map fac.i) (terminal.from Y) :=
      hasLiftingProperty_of_wfs _ _ hLi (mem_fibrations (terminal.from Y))
    have : sq.HasLift := hp.sq_hasLift sq
    let g : L.obj fac.Z ⟶ Y := sq.lift
    have hg : L.map fac.i ≫ g = f := sq.fac_left
    have hadj : fac.i ≫ adj.homEquiv fac.Z Y g = adj.homEquiv X Y f := by
      rw [← adj.homEquiv_naturality_left, hg]
    have hfull := hcrit fac.Z Y g
    simp only [← weakEquivalence_iff] at hfull ⊢
    calc
      WeakEquivalence f ↔ WeakEquivalence g := by
        rw [← hg, weakEquivalence_precomp_iff]
      _ ↔ WeakEquivalence (adj.homEquiv fac.Z Y g) := hfull
      _ ↔ WeakEquivalence (adj.homEquiv X Y f) := by
        rw [← hadj, weakEquivalence_precomp_iff]

end CategoryTheory.Adjunction.IsQuillenEquivalence
