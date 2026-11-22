/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty
universe u v u' v'

namespace CategoryTheory.Adjunction.IsQuillenEquivalence

/-- The native adjoint-map criterion on fibrant cofibrant sources extends
to every cofibrant source using an actual trivial-cofibration replacement
and the original diagonal and adjunct equations. -/
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
  homEquiv_weakEquivalence_iff {X Y} hX hY f := by
    let fac := factorizationData (trivialCofibrations C) (fibrations C) (terminal.from X)
    let : Cofibration fac.i := (cofibration_iff _).mpr fac.hi.1
    let : WeakEquivalence fac.i := (weakEquivalence_iff _).mpr fac.hi.2
    let : Fibration fac.p := (fibration_iff _).mpr fac.hp
    let : IsFibrant fac.Z := (isFibrant_iff_of_isTerminal fac.p terminalIsTerminal).mpr
      inferInstance
    let : IsCofibrant fac.Z := isCofibrant_of_cofibration fac.i
    have hLi : trivialCofibrations D (L.map fac.i) :=
      hQ.preservesTrivialCofibrations _ fac.hi
    let : Cofibration (L.map fac.i) := (cofibration_iff _).mpr hLi.1
    let : WeakEquivalence (L.map fac.i) := (weakEquivalence_iff _).mpr hLi.2
    let sq : CommSq f (L.map fac.i) (terminal.from Y) (terminal.from (L.obj fac.Z)) :=
      ⟨terminalIsTerminal.hom_ext _ _⟩
    have hp : HasLiftingProperty (L.map fac.i) (terminal.from Y) := inferInstance
    let : sq.HasLift := hp.sq_hasLift sq
    let g : L.obj fac.Z ⟶ Y := sq.lift
    have hg : L.map fac.i ≫ g = f := sq.fac_left
    have hadj : fac.i ≫ adj.homEquiv fac.Z Y g = adj.homEquiv X Y f := by
      rw [← adj.homEquiv_naturality_left, hg]
    have hfull := hcrit fac.Z Y g
    simp only [← weakEquivalence_iff] at hfull ⊢
    have hf : WeakEquivalence f ↔ WeakEquivalence g := by
      rw [← hg]
      exact weakEquivalence_precomp_iff (L.map fac.i) g
    have ha : WeakEquivalence (adj.homEquiv X Y f) ↔
        WeakEquivalence (adj.homEquiv fac.Z Y g) := by
      rw [← hadj]
      exact weakEquivalence_precomp_iff fac.i _
    exact hf.trans (hfull.trans ha.symm)

end CategoryTheory.Adjunction.IsQuillenEquivalence
