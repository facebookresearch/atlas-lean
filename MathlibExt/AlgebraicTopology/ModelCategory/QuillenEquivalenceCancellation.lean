/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceCriterion

/-!
# Left cancellation of Quillen equivalences

If the first adjunction and the actual composite are Quillen equivalences,
then the second Quillen adjunction is a Quillen equivalence. Fibrant-source
recognition lets the proof use the derived counit at a bifibrant object.

The original Formal-Math development is by Tsutomu Okano.
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty

namespace CategoryTheory.Adjunction.IsQuillenEquivalence

/-- Left cancellation for the actual composed Quillen adjunction. -/
theorem cancel_left
    {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {E : Type u₃} [Category.{v₃} E] [ModelCategory E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    [adj.IsQuillenEquivalence] [adj'.IsQuillenAdjunction]
    [(adj.comp adj').IsQuillenEquivalence] : adj'.IsQuillenEquivalence := by
  apply mkOfFibrantSourceCriterion adj'
  intro X Y _ _ _ f
  let fac := factorizationData (cofibrations C) (trivialFibrations C) (initial.to (R.obj X))
  have : IsCofibrant fac.Z :=
    (isCofibrant_iff_of_isInitial fac.i initialIsInitial).mpr ((cofibration_iff _).mpr fac.hi)
  have hp : WeakEquivalence fac.p := (weakEquivalence_iff _).mpr fac.hp.2
  -- Use the adjunct of the replacement map directly, rather than factoring the counit.
  let e : L.obj fac.Z ⟶ X := (adj.homEquiv fac.Z X).symm fac.p
  have he : WeakEquivalence e := (weakEquivalence_homEquiv_iff (adj := adj) e).mpr
    (by simpa only [e, Equiv.apply_symm_apply] using hp)
  have : IsCofibrant (L.obj fac.Z) :=
    (IsQuillenAdjunction.preservesCofibrantObjects (adj := adj)).isCofibrant inferInstance
  have : IsFibrant (R'.obj Y) :=
    (IsQuillenAdjunction.preservesFibrantObjects (adj := adj')).isFibrant inferInstance
  have : WeakEquivalence (L'.map e) :=
    IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adj') e
  rw [← weakEquivalence_iff, ← weakEquivalence_iff,
    ← weakEquivalence_precomp_iff (L'.map e) f,
    ← weakEquivalence_precomp_iff e (adj'.homEquiv X Y f),
    weakEquivalence_homEquiv_iff (adj := adj.comp adj'),
    weakEquivalence_homEquiv_iff (adj := adj)]
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply, adj'.homEquiv_naturality_left]

end CategoryTheory.Adjunction.IsQuillenEquivalence
