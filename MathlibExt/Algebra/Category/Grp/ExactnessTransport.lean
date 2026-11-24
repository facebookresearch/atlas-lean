/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: @toskua
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Transport of multiplicative exactness through group isomorphisms

A commuting ladder of arbitrary group isomorphisms transports multiplicative
exactness along both complete morphisms. No commutativity hypothesis is needed.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe v uC vC

open CategoryTheory

namespace GrpCat

section OriginalCanonicalContext
attribute [local instance 2000] CategoryTheory.CategoryStruct.toQuiver

/-- Multiplicative exactness transports through a full ladder of arbitrary group isomorphisms. -/
theorem mulExact_of_iso_ladder
    {A₁ A₂ A₃ B₁ B₂ B₃ : GrpCat.{v}}
    (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) (e₃ : A₃ ≅ B₃)
    (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (f' : B₁ ⟶ B₂) (g' : B₂ ⟶ B₃)
    (h₁ : f ≫ e₂.hom = e₁.hom ≫ f') (h₂ : g ≫ e₃.hom = e₂.hom ≫ g')
    (hexact : Function.MulExact f'.hom g'.hom) : Function.MulExact f.hom g.hom := by
  let E₁ := e₁.groupIsoToMulEquiv
  let E₂ := e₂.groupIsoToMulEquiv
  let E₃ := e₃.groupIsoToMulEquiv
  intro x
  constructor
  · intro hx
    have hx' : g'.hom (E₂ x) = 1 :=
      (ConcreteCategory.congr_hom h₂ x).symm.trans
        ((congrArg E₃ hx).trans E₃.map_one)
    obtain ⟨z, hz⟩ := (hexact (E₂ x)).mp hx'
    refine ⟨E₁.symm z, ?_⟩
    apply E₂.injective
    exact (ConcreteCategory.congr_hom h₁ (E₁.symm z)).trans
      ((congrArg f'.hom (E₁.apply_symm_apply z)).trans hz)
  · rintro ⟨z, rfl⟩
    apply E₃.injective
    calc
      E₃ (g.hom (f.hom z)) = g'.hom (E₂ (f.hom z)) :=
        ConcreteCategory.congr_hom h₂ (f.hom z)
      _ = g'.hom (f'.hom (E₁ z)) :=
        congrArg g'.hom (ConcreteCategory.congr_hom h₁ z)
      _ = 1 := hexact.apply_apply_eq_one (E₁ z)
      _ = E₃ 1 := E₃.map_one.symm

end OriginalCanonicalContext

end GrpCat

namespace CategoryTheory

/-- An actual natural group isomorphism transports a proved image equation back to the
original map. -/
theorem originalGroupNatIso_image
    {C : Type uC} [Category.{vC} C] {F G : C ⥤ GrpCat.{v}}
    (e : F ≅ G) {X Y : C} (f : X ⟶ Y) (b : G.obj X) (x : F.obj Y)
    (hb : (G.map f).hom b = (e.hom.app Y).hom x) :
    ∃ y : F.obj X, (F.map f).hom y = x := by
  have hn := ConcreteCategory.congr_hom (e.inv.naturality f) b
  refine ⟨(e.inv.app X).hom b, ?_⟩
  exact hn.symm.trans ((congrArg (e.inv.app Y).hom hb).trans
    (ConcreteCategory.congr_hom (e.hom_inv_id_app Y) x))

end CategoryTheory

namespace CategoryTheory

/-- A genuine group isomorphism after a map preserves its exact original kernel. -/
theorem originalGroupMap_kernel_post_iso
    {A B C : GrpCat.{v}} (f : A ⟶ B) (e : B ⟶ C) [IsIso e] (x : A) :
    (f ≫ e).hom x = 1 ↔ f.hom x = 1 := by
  constructor
  · intro h
    apply (asIso e).groupIsoToMulEquiv.injective
    exact h.trans (map_one e.hom).symm
  · intro h
    exact (congrArg e.hom h).trans (map_one e.hom)

/-- The actual same-source double-collapse equations give the full original kernel comparison. -/
theorem originalGroupMap_double_collapse_kernel
    {A B C D : GrpCat.{v}}
    (r : A ⟶ B) (L R : B ⟶ C) (ρ : A ⟶ D) (s : D ⟶ C) (b : A ⟶ C)
    [IsIso L] [IsIso R] (hL : r ≫ L = ρ ≫ s) (hR : r ≫ R = b) (x : A) :
    s.hom (ρ.hom x) = 1 ↔ b.hom x = 1 := by
  change (ρ ≫ s).hom x = 1 ↔ b.hom x = 1
  rw [← hL, ← hR, originalGroupMap_kernel_post_iso,
    originalGroupMap_kernel_post_iso]

end CategoryTheory

namespace CategoryTheory

/-- The genuine group five lemma retains all ten actual groups and every original square. -/
theorem originalGrpCat_fiveLemma
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : GrpCat.{v}}
    (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃) (f₃ : A₃ ⟶ A₄) (f₄ : A₄ ⟶ A₅)
    (g₁ : B₁ ⟶ B₂) (g₂ : B₂ ⟶ B₃) (g₃ : B₃ ⟶ B₄) (g₄ : B₄ ⟶ B₅)
    (a₁ : A₁ ⟶ B₁) (a₂ : A₂ ⟶ B₂) (a₃ : A₃ ⟶ B₃)
    (a₄ : A₄ ⟶ B₄) (a₅ : A₅ ⟶ B₅)
    (h₁ : a₁ ≫ g₁ = f₁ ≫ a₂) (h₂ : a₂ ≫ g₂ = f₂ ≫ a₃)
    (h₃ : a₃ ≫ g₃ = f₃ ≫ a₄) (h₄ : a₄ ≫ g₄ = f₄ ≫ a₅)
    (hf₁ : Function.MulExact f₁.hom f₂.hom)
    (hf₂ : Function.MulExact f₂.hom f₃.hom)
    (hf₃ : Function.MulExact f₃.hom f₄.hom)
    (hg₁ : Function.MulExact g₁.hom g₂.hom)
    (hg₂ : Function.MulExact g₂.hom g₃.hom)
    (hg₃ : Function.MulExact g₃.hom g₄.hom)
    [IsIso a₁] [IsIso a₂] [IsIso a₄] [IsIso a₅] : IsIso a₃ := by
  have hc₁ : g₁.hom.comp a₁.hom = a₂.hom.comp f₁.hom := congrArg GrpCat.Hom.hom h₁
  have hc₂ : g₂.hom.comp a₂.hom = a₃.hom.comp f₂.hom := congrArg GrpCat.Hom.hom h₂
  have hc₃ : g₃.hom.comp a₃.hom = a₄.hom.comp f₃.hom := congrArg GrpCat.Hom.hom h₃
  have hc₄ : g₄.hom.comp a₄.hom = a₅.hom.comp f₄.hom := congrArg GrpCat.Hom.hom h₄
  have hb := MonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f₁.hom f₂.hom f₃.hom f₄.hom g₁.hom g₂.hom g₃.hom g₄.hom
    a₁.hom a₂.hom a₃.hom a₄.hom a₅.hom hc₁ hc₂ hc₃ hc₄
    hf₁ hf₂ hf₃ hg₁ hg₂ hg₃
    (asIso a₁).groupIsoToMulEquiv.surjective
    (asIso a₂).groupIsoToMulEquiv.bijective
    (asIso a₄).groupIsoToMulEquiv.bijective
    (asIso a₅).groupIsoToMulEquiv.injective
  let e := (MulEquiv.ofBijective a₃.hom hb).toGrpIso
  have he : e.hom = a₃ := by
    apply GrpCat.hom_ext
    ext x
    rfl
  exact he ▸ e.isIso_hom

end CategoryTheory
