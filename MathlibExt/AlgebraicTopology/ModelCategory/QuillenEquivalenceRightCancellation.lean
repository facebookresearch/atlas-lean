/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

/-!
# Right cancellation of Quillen equivalences

If the second Quillen adjunction and the actual composite are Quillen
equivalences, the first Quillen adjunction is a Quillen equivalence.
The proof covers every cofibrant source and every fibrant target. A target
cofibrant replacement supplies a lift of the original map. A fibrant
replacement of its second left image supplies the second derived unit.
Brown's lemma applies only between the two actual fibrant objects.

This is the cancellation direction used in MMSS Corollary 10.5, through
Lemma A.2(ii). It does not assume every target is cofibrant or that a right
Quillen functor preserves weak equivalences on arbitrary objects.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty

namespace CategoryTheory.Adjunction.IsQuillenEquivalence

/-- Right cancellation for the original composed adjunction, with the full
cofibrant-source/fibrant-target adjoint-map criterion. -/
theorem cancel_right
    {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {E : Type u₃} [Category.{v₃} E] [ModelCategory E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    [adj.IsQuillenAdjunction] [adj'.IsQuillenEquivalence]
    [(adj.comp adj').IsQuillenEquivalence] : adj.IsQuillenEquivalence where
  toIsQuillenAdjunction := inferInstance
  homEquiv_weakEquivalence_iff {X Y} hXcof hYfib f := by
    let fac := factorizationData (cofibrations D) (trivialFibrations D)
      (initial.to Y)
    let _ : Cofibration fac.i := (cofibration_iff _).mpr fac.hi
    let _ : IsCofibrant fac.Z :=
      (isCofibrant_iff_of_isInitial fac.i initialIsInitial).mpr inferInstance
    let _ : Fibration fac.p := (fibration_iff _).mpr fac.hp.1
    let _ : WeakEquivalence fac.p := (weakEquivalence_iff _).mpr fac.hp.2
    let _ : IsFibrant fac.Z := isFibrant_of_fibration fac.p
    let _ : IsCofibrant (L.obj X) :=
      (IsQuillenAdjunction.preservesCofibrantObjects (adj := adj)).isCofibrant inferInstance
    let sq : CommSq (initial.to fac.Z) (initial.to (L.obj X)) fac.p f :=
      ⟨initialIsInitial.hom_ext _ _⟩
    have hpLift : HasLiftingProperty (initial.to (L.obj X)) fac.p := inferInstance
    let _ : sq.HasLift := hpLift.sq_hasLift sq
    let f₀ : L.obj X ⟶ fac.Z := sq.lift
    have hf₀ : f₀ ≫ fac.p = f := sq.fac_right
    have hpR : trivialFibrations C (R.map fac.p) :=
      IsQuillenAdjunction.preservesTrivialFibrations (adj := adj) fac.p fac.hp
    let _ : WeakEquivalence (R.map fac.p) :=
      (weakEquivalence_iff _).mpr hpR.2
    let tgt := factorizationData (trivialCofibrations E) (fibrations E)
      (terminal.from (L'.obj fac.Z))
    let _ : Fibration tgt.p := (fibration_iff _).mpr tgt.hp
    let _ : IsFibrant tgt.Z :=
      (isFibrant_iff_of_isTerminal tgt.p terminalIsTerminal).mpr inferInstance
    let _ : WeakEquivalence tgt.i := (weakEquivalence_iff _).mpr tgt.hi.2
    let u : fac.Z ⟶ R'.obj tgt.Z := adj'.homEquiv fac.Z tgt.Z tgt.i
    let _ : WeakEquivalence u :=
      (weakEquivalence_homEquiv_iff (adj := adj') tgt.i).mp inferInstance
    let _ : IsFibrant (R'.obj tgt.Z) :=
      (IsQuillenAdjunction.preservesFibrantObjects (adj := adj')).isFibrant inferInstance
    let _ : WeakEquivalence (R.map u) :=
      IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) u
    let g : L'.obj (L.obj X) ⟶ tgt.Z := L'.map f₀ ≫ tgt.i
    have hsecond : adj'.homEquiv (L.obj X) tgt.Z g = f₀ ≫ u :=
      adj'.homEquiv_naturality_left f₀ tgt.i
    have hcomp : (adj.comp adj').homEquiv X tgt.Z g =
        adj.homEquiv X fac.Z f₀ ≫ R.map u := by
      simp only [Adjunction.comp_homEquiv, Equiv.trans_apply, hsecond,
        adj.homEquiv_naturality_right]
    have hsecondWeak := weakEquivalence_homEquiv_iff (adj := adj') g
    rw [hsecond] at hsecondWeak
    have hcompositeWeak := weakEquivalence_homEquiv_iff (adj := adj.comp adj') g
    rw [hcomp] at hcompositeWeak
    have hfull : WeakEquivalence f₀ ↔
        WeakEquivalence (adj.homEquiv X fac.Z f₀) :=
      (hsecondWeak.trans (weakEquivalence_postcomp_iff f₀ u)).symm.trans
        (hcompositeWeak.trans
          (weakEquivalence_postcomp_iff (adj.homEquiv X fac.Z f₀) (R.map u)))
    have hf : WeakEquivalence f ↔ WeakEquivalence f₀ := by
      rw [← hf₀]
      exact weakEquivalence_postcomp_iff f₀ fac.p
    have hadj : adj.homEquiv X Y f =
        adj.homEquiv X fac.Z f₀ ≫ R.map fac.p := by
      rw [← hf₀, adj.homEquiv_naturality_right]
    have ha : WeakEquivalence (adj.homEquiv X Y f) ↔
        WeakEquivalence (adj.homEquiv X fac.Z f₀) := by
      rw [hadj]
      exact weakEquivalence_postcomp_iff (adj.homEquiv X fac.Z f₀) (R.map fac.p)
    simpa only [weakEquivalence_iff] using hf.trans (hfull.trans ha.symm)

end CategoryTheory.Adjunction.IsQuillenEquivalence
