/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# Right cancellation of Quillen equivalences

If the second adjunction and the actual composite are Quillen equivalences,
then the first Quillen adjunction is a Quillen equivalence. A cofibrant
replacement of the target and a fibrant replacement of its second left image
supply the endpoints needed for Brown preservation and the adjoint-map criteria.

This is the cancellation direction used in Mandell–May–Schwede–Shipley,
*Model categories of diagram spectra*, Corollary 10.5 via Lemma A.2(ii).
The original Formal-Math development is by Tsutomu Okano.
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty

namespace CategoryTheory.Adjunction.IsQuillenEquivalence

/-- Right cancellation for the actual composed Quillen adjunction. -/
theorem cancel_right
    {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {E : Type u₃} [Category.{v₃} E] [ModelCategory E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    [hQ : adj.IsQuillenAdjunction] [adj'.IsQuillenEquivalence]
    [(adj.comp adj').IsQuillenEquivalence] : adj.IsQuillenEquivalence where
  toIsQuillenAdjunction := hQ
  homEquiv_weakEquivalence_iff {X Y} _ _ f := by
    let fac := factorizationData (cofibrations D) (trivialFibrations D) (initial.to Y)
    have : IsCofibrant fac.Z :=
      (isCofibrant_iff_of_isInitial fac.i initialIsInitial).mpr ((cofibration_iff _).mpr fac.hi)
    have : Fibration fac.p := (fibration_iff _).mpr fac.hp.1
    have : WeakEquivalence fac.p := (weakEquivalence_iff _).mpr fac.hp.2
    have : IsFibrant fac.Z := isFibrant_of_fibration fac.p
    have : IsCofibrant (L.obj X) :=
      (IsQuillenAdjunction.preservesCofibrantObjects (adj := adj)).isCofibrant inferInstance
    let sq : CommSq (initial.to fac.Z) (initial.to (L.obj X)) fac.p f :=
      ⟨initialIsInitial.hom_ext _ _⟩
    have hpLift : HasLiftingProperty (initial.to (L.obj X)) fac.p :=
      hasLiftingProperty_of_wfs _ _ (mem_cofibrations _) fac.hp
    have : sq.HasLift := hpLift.sq_hasLift sq
    let f₀ : L.obj X ⟶ fac.Z := sq.lift
    have hf₀ : f₀ ≫ fac.p = f := sq.fac_right
    have : WeakEquivalence (R.map fac.p) := (weakEquivalence_iff _).mpr
      (IsQuillenAdjunction.preservesTrivialFibrations (adj := adj) fac.p fac.hp).2
    let tgt := factorizationData (trivialCofibrations E) (fibrations E)
      (terminal.from (L'.obj fac.Z))
    have : IsFibrant tgt.Z :=
      (isFibrant_iff_of_isTerminal tgt.p terminalIsTerminal).mpr ((fibration_iff _).mpr tgt.hp)
    let u : fac.Z ⟶ R'.obj tgt.Z := adj'.homEquiv fac.Z tgt.Z tgt.i
    have : WeakEquivalence u :=
      (weakEquivalence_homEquiv_iff (adj := adj') tgt.i).mp ((weakEquivalence_iff _).mpr tgt.hi.2)
    have : IsFibrant (R'.obj tgt.Z) :=
      (IsQuillenAdjunction.preservesFibrantObjects (adj := adj')).isFibrant inferInstance
    have : WeakEquivalence (R.map u) :=
      IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) u
    let g : L'.obj (L.obj X) ⟶ tgt.Z := L'.map f₀ ≫ tgt.i
    have hsecond : adj'.homEquiv (L.obj X) tgt.Z g = f₀ ≫ u :=
      adj'.homEquiv_naturality_left f₀ tgt.i
    have hcomp : (adj.comp adj').homEquiv X tgt.Z g =
        adj.homEquiv X fac.Z f₀ ≫ R.map u := by
      simp only [Adjunction.comp_homEquiv, Equiv.trans_apply, hsecond,
        adj.homEquiv_naturality_right]
    have hadj : adj.homEquiv X Y f = adj.homEquiv X fac.Z f₀ ≫ R.map fac.p := by
      rw [← hf₀, adj.homEquiv_naturality_right]
    simp only [← weakEquivalence_iff]
    calc
      WeakEquivalence f ↔ WeakEquivalence (f₀ ≫ u) := by
        rw [← hf₀, weakEquivalence_postcomp_iff, weakEquivalence_postcomp_iff]
      _ ↔ WeakEquivalence g := hsecond ▸ (weakEquivalence_homEquiv_iff (adj := adj') g).symm
      _ ↔ WeakEquivalence (adj.homEquiv X fac.Z f₀ ≫ R.map u) :=
        hcomp ▸ weakEquivalence_homEquiv_iff (adj := adj.comp adj') g
      _ ↔ WeakEquivalence (adj.homEquiv X Y f) := by
        rw [hadj, weakEquivalence_postcomp_iff, weakEquivalence_postcomp_iff]

end CategoryTheory.Adjunction.IsQuillenEquivalence
