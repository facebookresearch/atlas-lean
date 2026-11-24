/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFiller
public import MathlibExt.CategoryTheory.Limits.Types.PushoutComplement
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Degreewise normal form of labelled attachment

For a monic family, each degree of the actual one-step attachment consists
of its old simplices and one complementary simplex for every complete cell
label. The forward bijection uses the actual unit and cell maps. Its map
naturality retains the label and its prescribed attaching map.

This is the direct labelled set-pushout argument in Cisinski's
Construction 2.4.36 and Lemmas 2.4.35–2.4.37, July 30, 2026, pp.63–65.
Complements are taken only in each degree, without a simplicial complement.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace SSet.labelledFreeFiller

variable {I : Type u} {K D : I → SSet.{u}} (j : ∀ s, K s ⟶ D s)

private def degreeCofan (F : I → SSet.{u}) (c : Cofan F) (n : ℕ) :
    Cofan (fun s => F s _⦋n⦌) :=
  Cofan.mk (c.pt _⦋n⦌) (fun s => (c.inj s).app (op ⦋n⦌))

private def degreeCofanIsColimit {F : I → SSet.{u}} {c : Cofan F}
    (hc : IsColimit c) (n : ℕ) : IsColimit (degreeCofan F c n) :=
  isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj (op ⦋n⦌)) F
    (fun s => c.inj s) hc

private def degreeCofanEquiv {F : I → SSet.{u}} {c : Cofan F}
    (hc : IsColimit c) (n : ℕ) : (Σ s, F s _⦋n⦌) ≃ c.pt _⦋n⦌ :=
  CofanTypes.equivOfIsColimit
    ((Cofan.isColimit_cofanTypes_iff (degreeCofan F c n)).2
      ⟨degreeCofanIsColimit hc n⟩)

private lemma degreeCofanEquiv_apply {F : I → SSet.{u}} {c : Cofan F}
    (hc : IsColimit c) (n : ℕ) (s : I) (x : F s _⦋n⦌) :
    degreeCofanEquiv hc n ⟨s, x⟩ = (c.inj s).app (op ⦋n⦌) x := rfl

private lemma labelledPushout (X : SSet.{u}) (n : ℕ) :
    IsPushout
      (↾fun q : Σ x : Index K X, K x.1 _⦋n⦌ => q.1.2.app (op ⦋n⦌) q.2)
      (↾fun q : Σ x : Index K X, K x.1 _⦋n⦌ =>
        (⟨q.1, (j q.1.1).app (op ⦋n⦌) q.2⟩ : Σ x : Index K X, D x.1 _⦋n⦌))
      ((unit j).app X |>.app (op ⦋n⦌))
      (↾fun q : Σ x : Index K X, D x.1 _⦋n⦌ =>
        (cell j q.1.1 q.1.2).app (op ⦋n⦌) q.2) := by
  let c := attachCells j X
  let e₁ := degreeCofanEquiv c.isColimit₁ n
  let e₂ := degreeCofanEquiv c.isColimit₂ n
  have hp := c.isPushout.map ((evaluation _ _).obj (op ⦋n⦌))
  apply hp.of_iso e₁.toIso.symm (Iso.refl _) e₂.toIso.symm (Iso.refl _)
  · apply ConcreteCategory.hom_ext
    intro z
    obtain ⟨q, rfl⟩ := e₁.surjective z
    rcases q with ⟨x, k⟩
    rcases x with ⟨s, a⟩
    change c.g₁.app (op ⦋n⦌) (e₁ ⟨⟨s, a⟩, k⟩) =
      (e₁.symm (e₁ ⟨⟨s, a⟩, k⟩)).1.2.app (op ⦋n⦌)
        (e₁.symm (e₁ ⟨⟨s, a⟩, k⟩)).2
    rw [Equiv.symm_apply_apply]
    rw [show e₁ ⟨⟨s, a⟩, k⟩ = (c.cofan₁.inj ⟨s, a⟩).app (op ⦋n⦌) k from
      degreeCofanEquiv_apply c.isColimit₁ n ⟨s, a⟩ k]
    change ((c.cofan₁.inj ⟨s, a⟩ ≫ c.g₁).app (op ⦋n⦌)) k = a.app (op ⦋n⦌) k
    rw [cofan₁_inj_g₁]
    rfl
  · apply ConcreteCategory.hom_ext
    intro z
    obtain ⟨q, rfl⟩ := e₁.surjective z
    rcases q with ⟨x, k⟩
    rcases x with ⟨s, a⟩
    change e₂.symm (c.m.app (op ⦋n⦌) (e₁ ⟨⟨s, a⟩, k⟩)) =
      ⟨(e₁.symm (e₁ ⟨⟨s, a⟩, k⟩)).1,
        (j (e₁.symm (e₁ ⟨⟨s, a⟩, k⟩)).1.1).app (op ⦋n⦌)
          (e₁.symm (e₁ ⟨⟨s, a⟩, k⟩)).2⟩
    rw [Equiv.symm_apply_apply]
    apply e₂.injective
    rw [Equiv.apply_symm_apply]
    change c.m.app (op ⦋n⦌) ((c.cofan₁.inj ⟨s, a⟩).app (op ⦋n⦌) k) =
      (c.cofan₂.inj ⟨s, a⟩).app (op ⦋n⦌) ((j s).app (op ⦋n⦌) k)
    change ((c.cofan₁.inj ⟨s, a⟩ ≫ c.m).app (op ⦋n⦌)) k = _
    rw [c.hm]
    rfl
  · simp
  · apply ConcreteCategory.hom_ext
    intro z
    obtain ⟨q, rfl⟩ := e₂.surjective z
    change c.g₂.app (op ⦋n⦌) (e₂ q) =
      (cell j (e₂.symm (e₂ q)).1.1 (e₂.symm (e₂ q)).1.2).app (op ⦋n⦌)
        (e₂.symm (e₂ q)).2
    rw [Equiv.symm_apply_apply]
    change c.g₂.app (op ⦋n⦌) ((c.cofan₂.inj q.1).app (op ⦋n⦌) q.2) = _
    rfl

private lemma sigmaMap_injective (X : SSet.{u}) (n : ℕ) [∀ s, Mono (j s)] :
    Function.Injective (fun q : Σ x : Index K X, K x.1 _⦋n⦌ =>
      (⟨q.1, (j q.1.1).app (op ⦋n⦌) q.2⟩ : Σ x : Index K X, D x.1 _⦋n⦌)) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ h
  obtain rfl : x = y := congrArg Sigma.fst h
  have hm : Mono ((j x.1).app (op ⦋n⦌)) :=
    (NatTrans.mono_iff_mono_app (j x.1)).mp inferInstance _
  have hi := (mono_iff_injective ((j x.1).app (op ⦋n⦌))).1 hm
  exact congrArg (Sigma.mk x) (hi (by simpa using h))

private def complementSigmaEquiv (X : SSet.{u}) (n : ℕ) :
    (Σ x : Index K X, {d : D x.1 _⦋n⦌ // d ∉ Set.range ((j x.1).app (op ⦋n⦌))}) ≃
      {q : Σ x : Index K X, D x.1 _⦋n⦌ //
        q ∉ Set.range (fun a : Σ x : Index K X, K x.1 _⦋n⦌ =>
          (⟨a.1, (j a.1.1).app (op ⦋n⦌) a.2⟩ : Σ x : Index K X, D x.1 _⦋n⦌))} where
  toFun q := ⟨⟨q.1, q.2.val⟩, by
    rintro ⟨⟨x, k⟩, h⟩
    obtain rfl : x = q.1 := congrArg Sigma.fst h
    exact q.2.property ⟨k, by simpa using h⟩⟩
  invFun q := ⟨q.val.1, q.val.2, by
    rintro ⟨k, h⟩
    exact q.property ⟨⟨q.val.1, k⟩, by simp [h]⟩⟩
  left_inv q := rfl
  right_inv q := rfl

private lemma degreewise_bijective (X : SSet.{u}) (n : ℕ) [∀ s, Mono (j s)] :
    Function.Bijective (fun q : X _⦋n⦌ ⊕ Σ x : Index K X,
      {d : D x.1 _⦋n⦌ // d ∉ Set.range ((j x.1).app (op ⦋n⦌))} =>
      q.elim (((unit j).app X).app (op ⦋n⦌))
        (fun x => (cell j x.1.1 x.1.2).app (op ⦋n⦌) x.2.val)) := by
  let e := (Equiv.sumCongr (Equiv.refl _) (complementSigmaEquiv j X n)).trans
    (Types.pushoutComplementEquiv (labelledPushout j X n) (sigmaMap_injective j X n))
  have he : (e : _ → _) = (fun q => q.elim (((unit j).app X).app (op ⦋n⦌))
      (fun x => (cell j x.1.1 x.1.2).app (op ⦋n⦌) x.2.val)) := by
    funext q
    rcases q with x | d <;> rfl
  rw [← he]
  exact e.bijective

/-- The actual degree of labelled attachment consists of old simplices and
the complementary simplices of every complete labelled cell. -/
def degreewiseEquiv (X : SSet.{u}) (n : ℕ) [∀ s, Mono (j s)] :
    (X _⦋n⦌ ⊕ Σ x : Index K X,
      {d : D x.1 _⦋n⦌ // d ∉ Set.range ((j x.1).app (op ⦋n⦌))}) ≃
        (labelledFreeFiller j).obj X _⦋n⦌ :=
  Equiv.ofBijective
    (fun q => q.elim (((unit j).app X).app (op ⦋n⦌))
      (fun x => (cell j x.1.1 x.1.2).app (op ⦋n⦌) x.2.val))
    (by exact degreewise_bijective j X n)

@[simp]
lemma degreewiseEquiv_inl (X : SSet.{u}) (n : ℕ) [∀ s, Mono (j s)] (x : X _⦋n⦌) :
    degreewiseEquiv j X n (Sum.inl x) = ((unit j).app X).app (op ⦋n⦌) x := rfl

@[simp]
lemma degreewiseEquiv_inr (X : SSet.{u}) (n : ℕ) [∀ s, Mono (j s)]
    (x : Index K X) (d : D x.1 _⦋n⦌)
    (hd : d ∉ Set.range ((j x.1).app (op ⦋n⦌))) :
    degreewiseEquiv j X n (Sum.inr ⟨x, d, hd⟩) =
      (cell j x.1 x.2).app (op ⦋n⦌) d := rfl

/-- Naturality preserves the complete generator label and transports its
attaching map; the complementary simplex is unchanged. -/
lemma degreewiseEquiv_naturality {X Y : SSet.{u}} (m : X ⟶ Y) (n : ℕ)
    [∀ s, Mono (j s)]
    (q : X _⦋n⦌ ⊕ Σ x : Index K X,
      {d : D x.1 _⦋n⦌ // d ∉ Set.range ((j x.1).app (op ⦋n⦌))}) :
    ((labelledFreeFiller j).map m).app (op ⦋n⦌) (degreewiseEquiv j X n q) =
      degreewiseEquiv j Y n (q.map (m.app (op ⦋n⦌))
        (fun x => ⟨⟨x.1.1, x.1.2 ≫ m⟩, x.2⟩)) := by
  rcases q with x | ⟨⟨s, a⟩, d, hd⟩
  · simp only [Sum.map_inl, degreewiseEquiv_inl]
    change (((unit j).app X ≫ (labelledFreeFiller j).map m).app (op ⦋n⦌)) x =
      ((m ≫ (unit j).app Y).app (op ⦋n⦌)) x
    rw [← (unit j).naturality]
    rfl
  · simp only [Sum.map_inr, degreewiseEquiv_inr]
    change ((cell j s a ≫ (labelledFreeFiller j).map m).app (op ⦋n⦌)) d =
      (cell j s (a ≫ m)).app (op ⦋n⦌) d
    rw [cell_naturality]

end SSet.labelledFreeFiller
