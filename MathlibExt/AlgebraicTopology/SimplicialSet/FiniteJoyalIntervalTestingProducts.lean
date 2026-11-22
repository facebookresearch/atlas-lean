/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalHomotopyCurry
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFibrantObjects
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingTwoOutOfThree
public import Mathlib.CategoryTheory.Limits.Shapes.PiProd
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Product stability of the actual finite-interval testing class

Testing precomposition is conjugated through the actual quotient currying
equivalence. Function objects of naive targets are again naive by the
quasicategory dictionary. Isomorphism transport and the chosen product
comparison then retain the original finite product maps and their labels.

This is a project proof before model construction, in the context of
Cisinski, Corollary 3.6.3 (July 30, 2026, printed pp.113–114 / PDF pp.129–130).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory MonoidalClosed

universe u v w

namespace SSet.joyalInterval

private instance testingContainsIdentities :
    (productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).ContainsIdentities := by
  rw [productPrecylinder.testingEquivalences_eq_iInf_isomorphisms auxiliaryAnodyneExtensions]
  infer_instance

private instance testingRespectsIso :
    (productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).RespectsIso := by
  rw [productPrecylinder.testingEquivalences_eq_iInf_isomorphisms auxiliaryAnodyneExtensions]
  infer_instance

/-- Product with an arbitrary simplicial set on the left preserves the actual
finite-interval homotopy-class testing predicate. -/
theorem testingEquivalences_whiskerLeft (S : SSet.{u}) {X Y : SSet.{u}}
    (f : X ⟶ Y) (hf : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions f) :
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions (S ◁ f) := by
  intro Q hQ
  have : Quasicategory Q := (auxiliaryNaiveFibrantObjects_iff Q).mp hQ
  have hQS : auxiliaryAnodyneExtensions.naiveFibrantObjects ((ihom S).obj Q) :=
    (auxiliaryNaiveFibrantObjects_iff ((ihom S).obj Q)).mpr inferInstance
  have htest := hf ((ihom S).obj Q) hQS
  have hmap : productPrecylinder.homotopyClassPrecomp (S ◁ f) Q =
      fun h ↦ (homotopyClassCurryEquiv S X Q).symm
        (productPrecylinder.homotopyClassPrecomp f ((ihom S).obj Q)
          (homotopyClassCurryEquiv S Y Q h)) := by
    funext h
    apply (homotopyClassCurryEquiv S X Q).injective
    simpa only [Equiv.apply_symm_apply] using homotopyClassCurryEquiv_precomp S f h
  rw [hmap]
  exact (homotopyClassCurryEquiv S X Q).symm.bijective.comp
    (htest.comp (homotopyClassCurryEquiv S Y Q).bijective)

/-- The actual braiding transports testing stability to product on the right. -/
theorem testingEquivalences_whiskerRight (S : SSet.{u}) {X Y : SSet.{u}}
    (f : X ⟶ Y) (hf : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions f) :
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions (f ▷ S) := by
  have h : f ▷ S = (β_ X S).hom ≫ (S ◁ f) ≫ (β_ Y S).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact BraidedCategory.braiding_naturality_left f S
  rw [h]
  exact (productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).comp_mem _ _
    ((productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).of_isIso _)
    ((productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).comp_mem _ _
      (testingEquivalences_whiskerLeft S f hf)
      ((productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).of_isIso _))

/-- The binary tensor of two testing equivalences is a testing equivalence. -/
theorem testingEquivalences_tensorHom {X Y X' Y' : SSet.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions f)
    (hg : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions g) :
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions (f ⊗ₘ g) := by
  rw [tensorHom_def]
  exact (productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).comp_mem _ _
    (testingEquivalences_whiskerRight X' f hf) (testingEquivalences_whiskerLeft Y g hg)

private lemma testingEquivalences_prodMap {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions f)
    (hg : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions g) :
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions (prod.map f g) := by
  let eX := (tensorLeftIsoProd X).app X'
  let eY := (tensorLeftIsoProd Y).app Y'
  have hw : (f ⊗ₘ g) ≫ eY.hom = eX.hom ≫ prod.map f g := by
    apply prod.hom_ext <;> simp [eX, eY, tensorLeftIsoProd]
  have h : prod.map f g = eX.inv ≫ (f ⊗ₘ g) ≫ eY.hom := by
    apply (cancel_epi eX.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hw.symm
  rw [h]
  exact (productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).comp_mem _ _
    ((productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).of_isIso _)
    ((productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).comp_mem _ _
      (testingEquivalences_tensorHom f g hf hg)
      ((productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).of_isIso _))

private lemma testingEquivalences_piMap_reindex {I : Type v} {J : Type w}
    [Finite I] [Finite J] {X Y : J → SSet.{u}} (e : I ≃ J)
    (f : ∀ j, X j ⟶ Y j)
    (hf : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions
      (Limits.Pi.map (fun i ↦ f (e i)))) :
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions (Limits.Pi.map f) := by
  let eX := Limits.Pi.reindex e X
  let eY := Limits.Pi.reindex e Y
  have hw : Limits.Pi.map (fun i ↦ f (e i)) ≫ eY.hom = eX.hom ≫ Limits.Pi.map f := by
    apply Limits.Pi.hom_ext
    intro j
    obtain ⟨i, rfl⟩ := e.surjective j
    have hx : eX.hom ≫ Limits.Pi.π X (e i) = Limits.Pi.π (X ∘ e) i :=
      Limits.Pi.reindex_hom_π e X i
    have hy : eY.hom ≫ Limits.Pi.π Y (e i) = Limits.Pi.π (Y ∘ e) i :=
      Limits.Pi.reindex_hom_π e Y i
    calc
      (Limits.Pi.map (fun i ↦ f (e i)) ≫ eY.hom) ≫ Limits.Pi.π Y (e i) =
          Limits.Pi.map (fun i ↦ f (e i)) ≫ Limits.Pi.π (Y ∘ e) i := by
        rw [Category.assoc, hy]
      _ = Limits.Pi.π (X ∘ e) i ≫ f (e i) :=
        Limits.Pi.map_π (f := X ∘ e) (g := Y ∘ e) (fun i ↦ f (e i)) i
      _ = (eX.hom ≫ Limits.Pi.map f) ≫ Limits.Pi.π Y (e i) := by
        rw [Category.assoc, Limits.Pi.map_π, ← Category.assoc, hx]
  let eA : Arrow.mk (Limits.Pi.map (fun i ↦ f (e i))) ≅ Arrow.mk (Limits.Pi.map f) :=
    Arrow.isoMk eX eY hw.symm
  exact ((productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).arrow_mk_iso_iff
    eA).mp hf

private lemma testingEquivalences_piMap_unique {I : Type v} [Unique I]
    {X Y : I → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions (f i)) :
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions (Limits.Pi.map f) := by
  let eX := productUniqueIso X
  let eY := productUniqueIso Y
  have hw : Limits.Pi.map f ≫ eY.hom = eX.hom ≫ f default := by
    simp [eX, eY, Limits.Pi.map_π]
  let eA : Arrow.mk (Limits.Pi.map f) ≅ Arrow.mk (f default) :=
    Arrow.isoMk eX eY hw.symm
  exact ((productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).arrow_mk_iso_iff
    eA).mpr (hf default)

private lemma testingEquivalences_piMap_fin :
    ∀ (n : ℕ) (X Y : Fin n → SSet.{u}) (f : ∀ i, X i ⟶ Y i),
      (∀ i, productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions (f i)) →
        productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions (Limits.Pi.map f) := by
  classical
  intro n
  induction n with
  | zero =>
    intro X Y f hf
    let : ∀ i, IsIso (f i) := fun i ↦ Fin.elim0 i
    exact (productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).of_isIso _
  | succ n ih =>
    intro X Y f hf
    let : Unique {i : Fin (n + 1) // i = 0} :=
      { default := ⟨0, rfl⟩
        uniq := fun i ↦ Subtype.ext i.property }
    have h₀ : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions
        (Limits.Pi.map (fun i : {i : Fin (n + 1) // i = 0} ↦ f i.1)) :=
      testingEquivalences_piMap_unique _ (fun i ↦ hf i.1)
    have h₁ : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions
        (Limits.Pi.map (fun i : {i : Fin (n + 1) // i ≠ 0} ↦ f i.1)) := by
      apply testingEquivalences_piMap_reindex (finSuccAboveEquiv (0 : Fin (n + 1)))
      exact ih _ _ _ (fun i ↦ hf _)
    rw [Limits.Pi.map_eq_prod_map f (fun i ↦ i = 0)]
    exact (productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).comp_mem _ _
      ((productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).of_isIso _)
      ((productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).comp_mem _ _
        (testingEquivalences_prodMap _ _ h₀ h₁)
        ((productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).of_isIso _))

/-- The actual product map of every finite indexed family of testing
equivalences is a testing equivalence, in any index universe. -/
theorem testingEquivalences_pi_map_of_finite {I : Type v} [Finite I]
    {X Y : I → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions (f i)) :
    productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions (Limits.Pi.map f) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  apply testingEquivalences_piMap_reindex e.symm
  exact testingEquivalences_piMap_fin n _ _ _ (fun i ↦ hf _)

end SSet.joyalInterval
