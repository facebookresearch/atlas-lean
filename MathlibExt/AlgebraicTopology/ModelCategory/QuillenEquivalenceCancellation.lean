/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceCriterion

/-!
# Left cancellation of Quillen equivalences

The first equivalence and the equivalence of the actual composite imply that
the second Quillen adjunction is an equivalence. A native cofibrant
factorization of the first right image supplies the derived counit; Brown's
lemma and the two original Hovey criteria prove the full second criterion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty

namespace CategoryTheory.Adjunction.IsQuillenEquivalence

/-- Left cancellation for the actual composed Quillen adjunction. The result
contains the full original-map Hovey criterion and requires no universal
cofibrancy or functorial-factorization hypothesis. -/
theorem cancel_left
    {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {E : Type u₃} [Category.{v₃} E] [ModelCategory E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    [adj.IsQuillenEquivalence] [adj'.IsQuillenAdjunction]
    [(adj.comp adj').IsQuillenEquivalence] : adj'.IsQuillenEquivalence := by
  apply mkOfFibrantSourceCriterion adj'
  intro X Y hXcof hXfib hYfib f
  let fac := factorizationData (cofibrations C) (trivialFibrations C)
    (initial.to (R.obj X))
  let _ : Cofibration fac.i := (cofibration_iff _).mpr fac.hi
  let _ : IsCofibrant fac.Z :=
    (isCofibrant_iff_of_isInitial fac.i initialIsInitial).mpr inferInstance
  let _ : WeakEquivalence fac.p := (weakEquivalence_iff _).mpr fac.hp.2
  let e : L.obj fac.Z ⟶ X := (adj.homEquiv fac.Z X).symm fac.p
  let _ : WeakEquivalence e := by
    apply (weakEquivalence_homEquiv_iff (adj := adj) e).mpr
    change WeakEquivalence ((adj.homEquiv fac.Z X) ((adj.homEquiv fac.Z X).symm fac.p))
    simpa only [Equiv.apply_symm_apply] using (inferInstance : WeakEquivalence fac.p)
  let _ : IsCofibrant (L.obj fac.Z) :=
    (IsQuillenAdjunction.preservesCofibrantObjects (adj := adj)).isCofibrant inferInstance
  let _ : IsFibrant (R'.obj Y) :=
    (IsQuillenAdjunction.preservesFibrantObjects (adj := adj')).isFibrant inferInstance
  let _ : WeakEquivalence (L'.map e) :=
    IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adj') e
  have hadj : (adj.comp adj').homEquiv fac.Z Y (L'.map e ≫ f) =
      adj.homEquiv fac.Z (R'.obj Y) (e ≫ adj'.homEquiv X Y f) := by
    simp only [Adjunction.comp_homEquiv, Equiv.trans_apply, adj'.homEquiv_naturality_left]
  have hcomp := weakEquivalence_homEquiv_iff (adj := adj.comp adj') (L'.map e ≫ f)
  rw [hadj] at hcomp
  have hfull := (weakEquivalence_precomp_iff (L'.map e) f).symm.trans
    (hcomp.trans ((weakEquivalence_homEquiv_iff (adj := adj)
      (e ≫ adj'.homEquiv X Y f)).symm.trans
        (weakEquivalence_precomp_iff e (adj'.homEquiv X Y f))))
  simpa only [weakEquivalence_iff] using hfull

end CategoryTheory.Adjunction.IsQuillenEquivalence
