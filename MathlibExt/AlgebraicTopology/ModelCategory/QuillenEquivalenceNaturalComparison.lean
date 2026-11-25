/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# Quillen equivalences under complete natural comparisons

The adjoint-map criterion is transported along the original full natural
isomorphism. Both directions of the Hom bijection are recorded before using
the criterion. Every cofibrant source and fibrant target remains quantified.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory HomotopicalAlgebra

namespace CategoryTheory.Adjunction

section CompleteHomComparison
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {L M : C ⥤ D} {R : D ⥤ C}

/-- The entire forward Hom function is the original comparison followed by the first adjunct. -/
theorem homEquiv_of_leftComparison (a : L ⊣ R) (b : M ⊣ R) (e : L ≅ M)
    (hUnit : ∀ X : C, a.unit.app X ≫ R.map (e.hom.app X) = b.unit.app X)
    (X : C) (Y : D) (f : M.obj X ⟶ Y) :
    b.homEquiv X Y f = a.homEquiv X Y (e.hom.app X ≫ f) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_comp, ← Category.assoc, hUnit X]

/-- The inverse Hom function retains the actual inverse comparison on every original arrow. -/
theorem homEquiv_symm_of_leftComparison (a : L ⊣ R) (b : M ⊣ R) (e : L ≅ M)
    (hUnit : ∀ X : C, a.unit.app X ≫ R.map (e.hom.app X) = b.unit.app X)
    (X : C) (Y : D) (g : X ⟶ R.obj Y) :
    (b.homEquiv X Y).symm g = e.inv.app X ≫ (a.homEquiv X Y).symm g := by
  apply (b.homEquiv X Y).injective
  have hEI : e.hom.app X ≫ e.inv.app X = 𝟙 (L.obj X) := (e.app X).hom_inv_id
  rw [Equiv.apply_symm_apply, homEquiv_of_leftComparison a b e hUnit,
    ← Category.assoc, hEI, Category.id_comp, Equiv.apply_symm_apply]

end CompleteHomComparison

namespace IsQuillenEquivalence
variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)

/-- A genuine full left natural isomorphism preserves the complete Hovey criterion. -/
instance ofNatIsoLeft {M : C ⥤ D} (e : L ≅ M) [a.IsQuillenEquivalence] :
    (a.ofNatIsoLeft e).IsQuillenEquivalence where
  toIsQuillenAdjunction := inferInstance
  homEquiv_weakEquivalence_iff {X Y} hX hY f := by
    let _ : WeakEquivalence (e.hom.app X) := inferInstance
    rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
    simpa only [weakEquivalence_iff] using
      (weakEquivalence_precomp_iff (e.hom.app X) f).symm.trans
        (weakEquivalence_homEquiv_iff (adj := a) (e.hom.app X ≫ f))

/-- A genuine full right natural isomorphism retains every original adjunct and target. -/
instance ofNatIsoRight {S : D ⥤ C} (e : R ≅ S) [a.IsQuillenEquivalence] :
    (a.ofNatIsoRight e).IsQuillenEquivalence where
  toIsQuillenAdjunction := inferInstance
  homEquiv_weakEquivalence_iff {X Y} hX hY f := by
    let _ : WeakEquivalence (e.hom.app Y) := inferInstance
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    simpa only [weakEquivalence_iff] using
      (weakEquivalence_homEquiv_iff (adj := a) f).trans
        (weakEquivalence_postcomp_iff (a.homEquiv X Y f) (e.hom.app Y)).symm

/-- The full canonical unit comparison transfers the criterion to the unchanged second adjunction.
-/
theorem of_leftComparison {M : C ⥤ D} (b : M ⊣ R) (e : L ≅ M)
    (hUnit : ∀ X : C, a.unit.app X ≫ R.map (e.hom.app X) = b.unit.app X)
    [a.IsQuillenEquivalence] : b.IsQuillenEquivalence where
  toIsQuillenAdjunction :=
    { preservesCofibrations :=
        (inferInstance : (a.ofNatIsoLeft e).IsQuillenAdjunction).preservesCofibrations
      preservesTrivialCofibrations :=
        (inferInstance : (a.ofNatIsoLeft e).IsQuillenAdjunction).preservesTrivialCofibrations }
  homEquiv_weakEquivalence_iff {X Y} hX hY f := by
    let _ : WeakEquivalence (e.hom.app X) := inferInstance
    rw [homEquiv_of_leftComparison a b e hUnit]
    simpa only [weakEquivalence_iff] using
      (weakEquivalence_precomp_iff (e.hom.app X) f).symm.trans
        (weakEquivalence_homEquiv_iff (adj := a) (e.hom.app X ≫ f))

end IsQuillenEquivalence
end CategoryTheory.Adjunction
