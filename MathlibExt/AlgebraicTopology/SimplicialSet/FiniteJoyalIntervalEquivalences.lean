/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalInterval
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv

/-!
# The finite interval detects equivalence edges

The two full unit triangles give separate left and right inverses in the
ordinary homotopy category of any target. In a quasicategory, the accepted
inverse-triangle theorem and the finite interval's full presentation
construct a strict realization of every equivalence edge.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

private lemma sourceIdentity {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) :
    joyalInterval.constSource ≫ yonedaEquiv.symm e.edge =
      yonedaEquiv.symm (Edge.id x₀).edge := by
  dsimp only [joyalInterval.constSource]
  rw [Category.assoc, Edge.δ_one_yonedaEquiv_symm,
    stdSimplex.σ_comp_yonedaEquiv_symm]
  rfl

private lemma targetIdentity {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) :
    joyalInterval.constTarget ≫ yonedaEquiv.symm e.edge =
      yonedaEquiv.symm (Edge.id x₁).edge := by
  dsimp only [joyalInterval.constTarget]
  rw [Category.assoc, Edge.δ_zero_yonedaEquiv_symm,
    stdSimplex.σ_comp_yonedaEquiv_symm]
  rfl

private lemma leftUnit {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁)
    (L : X _⦋2⦌) (h₂ : X.δ 2 L = e.edge) (h₁ : X.δ 1 L = (Edge.id x₀).edge) :
    ∃ g : Edge x₁ x₀, Nonempty (Edge.CompStruct e g (Edge.id x₀)) := by
  obtain ⟨a, b, c, f, g, h, H, hH⟩ := Edge.CompStruct.exists_of_simplex L
  have hf : f.edge = e.edge := H.d₂.symm.trans ((congrArg (X.δ 2) hH).trans h₂)
  have hh : h.edge = (Edge.id x₀).edge :=
    H.d₁.symm.trans ((congrArg (X.δ 1) hH).trans h₁)
  have hb : b = x₁ := f.tgt_eq.symm.trans ((congrArg (X.δ 0) hf).trans e.tgt_eq)
  have hc : c = x₀ := h.tgt_eq.symm.trans
    ((congrArg (X.δ 0) hh).trans (Edge.id x₀).tgt_eq)
  exact ⟨g.ofEq hb hc, ⟨H.ofEq hf rfl hh⟩⟩

private lemma rightUnit {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁)
    (R : X _⦋2⦌) (h₀ : X.δ 0 R = e.edge) (h₁ : X.δ 1 R = (Edge.id x₁).edge) :
    ∃ g : Edge x₁ x₀, Nonempty (Edge.CompStruct g e (Edge.id x₁)) := by
  obtain ⟨a, b, c, g, f, h, H, hH⟩ := Edge.CompStruct.exists_of_simplex R
  have hf : f.edge = e.edge := H.d₀.symm.trans ((congrArg (X.δ 0) hH).trans h₀)
  have hh : h.edge = (Edge.id x₁).edge :=
    H.d₁.symm.trans ((congrArg (X.δ 1) hH).trans h₁)
  have ha : a = x₁ := h.src_eq.symm.trans
    ((congrArg (X.δ 1) hh).trans (Edge.id x₁).src_eq)
  have hb : b = x₀ := f.src_eq.symm.trans ((congrArg (X.δ 1) hf).trans e.src_eq)
  exact ⟨g.ofEq ha hb, ⟨H.ofEq rfl hf hh⟩⟩

namespace Edge

/-- Chosen inverse triangles have a unique full realization on the finite interval. -/
theorem InvStruct.exists_joyalInterval_realization {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
    {e : Edge x₀ x₁} (I : e.InvStruct) :
    ∃! t : joyalInterval.{u} ⟶ X,
      joyalInterval.forward ≫ t = yonedaEquiv.symm e.edge ∧
      joyalInterval.leftInverse ≫ t = yonedaEquiv.symm I.inv.edge ∧
      joyalInterval.rightInverse ≫ t = yonedaEquiv.symm I.inv.edge ∧
      joyalInterval.leftTriangle ≫ t = yonedaEquiv.symm I.homInvId.simplex ∧
      joyalInterval.rightTriangle ≫ t = yonedaEquiv.symm I.invHomId.simplex := by
  exact joyalInterval.existsUnique_realization
    (yonedaEquiv.symm e.edge) (yonedaEquiv.symm I.inv.edge) (yonedaEquiv.symm I.inv.edge)
    (yonedaEquiv.symm I.homInvId.simplex) (yonedaEquiv.symm I.invHomId.simplex)
    I.homInvId.δ_zero_yonedaEquiv_symm
    (I.homInvId.δ_one_yonedaEquiv_symm.trans (sourceIdentity e).symm)
    I.homInvId.δ_two_yonedaEquiv_symm
    I.invHomId.δ_zero_yonedaEquiv_symm
    (I.invHomId.δ_one_yonedaEquiv_symm.trans (targetIdentity e).symm)
    I.invHomId.δ_two_yonedaEquiv_symm

/-- A strict finite-interval extension makes an edge invertible in any target's h-category. -/
theorem isEquivalence_of_joyalInterval_extension {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
    {e : Edge x₀ x₁} {t : joyalInterval.{u} ⟶ X}
    (ht : joyalInterval.forward ≫ t = yonedaEquiv.symm e.edge) : e.IsEquivalence := by
  have hL₂ : X.δ 2 (yonedaEquiv (joyalInterval.leftTriangle ≫ t)) = e.edge := by
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      congrArg yonedaEquiv ((joyalInterval.δ_two_leftTriangle_assoc t).trans ht)
  have hL₁ : X.δ 1 (yonedaEquiv (joyalInterval.leftTriangle ≫ t)) =
      (Edge.id x₀).edge := by
    have h : stdSimplex.δ (1 : Fin 3) ≫ (joyalInterval.leftTriangle ≫ t) =
        yonedaEquiv.symm (Edge.id x₀).edge :=
      (joyalInterval.δ_one_leftTriangle_assoc t).trans (by rw [ht, sourceIdentity e])
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      congrArg yonedaEquiv h
  have hR₀ : X.δ 0 (yonedaEquiv (joyalInterval.rightTriangle ≫ t)) = e.edge := by
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      congrArg yonedaEquiv ((joyalInterval.δ_zero_rightTriangle_assoc t).trans ht)
  have hR₁ : X.δ 1 (yonedaEquiv (joyalInterval.rightTriangle ≫ t)) =
      (Edge.id x₁).edge := by
    have h : stdSimplex.δ (1 : Fin 3) ≫ (joyalInterval.rightTriangle ≫ t) =
        yonedaEquiv.symm (Edge.id x₁).edge :=
      (joyalInterval.δ_one_rightTriangle_assoc t).trans (by rw [ht, targetIdentity e])
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using
      congrArg yonedaEquiv h
  obtain ⟨g, ⟨hg⟩⟩ := leftUnit e _ hL₂ hL₁
  obtain ⟨h, ⟨hh⟩⟩ := rightUnit e _ hR₀ hR₁
  have hfg : HomotopyCategory.homMk e ≫ HomotopyCategory.homMk g = 𝟙 _ := by
    rw [HomotopyCategory.homMk_comp_homMk hg, HomotopyCategory.homMk_id]
  have hhf : HomotopyCategory.homMk h ≫ HomotopyCategory.homMk e = 𝟙 _ := by
    rw [HomotopyCategory.homMk_comp_homMk hh, HomotopyCategory.homMk_id]
  have hgh : HomotopyCategory.homMk g = HomotopyCategory.homMk h := by
    calc
      HomotopyCategory.homMk g =
          (HomotopyCategory.homMk h ≫ HomotopyCategory.homMk e) ≫ HomotopyCategory.homMk g := by
        rw [hhf, Category.id_comp]
      _ = HomotopyCategory.homMk h ≫ (HomotopyCategory.homMk e ≫ HomotopyCategory.homMk g) :=
        Category.assoc _ _ _
      _ = HomotopyCategory.homMk h := by rw [hfg, Category.comp_id]
  exact ⟨⟨HomotopyCategory.homMk g, hfg, by rw [hgh]; exact hhf⟩⟩

/-- Every equivalence edge in a quasicategory has a strict finite-interval extension. -/
theorem IsEquivalence.exists_joyalInterval_extension {X : SSet.{u}} [Quasicategory X]
    {x₀ x₁ : X _⦋0⦌} {e : Edge x₀ x₁} (he : e.IsEquivalence) :
    ∃ t : joyalInterval.{u} ⟶ X, joyalInterval.forward ≫ t = yonedaEquiv.symm e.edge := by
  obtain ⟨I⟩ := he.nonempty_invStruct
  obtain ⟨t, ht, _⟩ := I.exists_joyalInterval_realization
  exact ⟨t, ht.1⟩

/-- The strict finite-interval extension criterion in a quasicategory. -/
theorem isEquivalence_iff_joyalInterval_extension {X : SSet.{u}} [Quasicategory X]
    {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) :
    e.IsEquivalence ↔
      ∃ t : joyalInterval.{u} ⟶ X, joyalInterval.forward ≫ t = yonedaEquiv.symm e.edge :=
  ⟨fun he => he.exists_joyalInterval_extension,
    fun ⟨_, ht⟩ => isEquivalence_of_joyalInterval_extension ht⟩

end Edge

namespace joyalInterval

/-- Every map from the finite interval sends its forward edge to an equivalence. -/
theorem isEquivalence_forward {X : SSet.{u}} (t : joyalInterval.{u} ⟶ X) :
    (Edge.mk' (yonedaEquiv (forward ≫ t))).IsEquivalence :=
  Edge.isEquivalence_of_joyalInterval_extension (t := t)
    (yonedaEquiv.symm_apply_apply _).symm

end joyalInterval

end SSet
