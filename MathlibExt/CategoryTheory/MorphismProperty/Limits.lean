/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Generic cobase-change witness API

Small reusable extension of Mathlib's morphism-property cobase-change API.

Main results:

* `CategoryTheory.MorphismProperty.IsStableUnderCobaseChangeAgainst.of_isPushout`:
  push a `P` morphism through a pushout square along a `Q` morphism.
  Preserves Mathlib's `IsPushout i f f' j` orientation: `i` is the `Q` leg,
  `f` is the `P` leg, and `f'` is the resulting pushed `P` leg.
* `CategoryTheory.MorphismProperty.IsStableUnderCobaseChangeAgainst.of_le`:
  contravariant restriction in the right-hand class: stability against `Q`
  implies stability against any `R ≤ Q`.

Variance: `P` is the class being pushed forward (covariant in the conclusion);
the right-hand class `Q` is contravariant (a smaller class is easier to be
stable against). No specialized counterexample structure is exposed.
-/

@[expose] public section

namespace CategoryTheory
namespace MorphismProperty

open Limits

universe v u

variable {C : Type u} [Category.{v} C]
variable {P Q R : MorphismProperty C}

/-- Push a `P` morphism through a pushout square along a `Q` leg.

Given `h : P.IsStableUnderCobaseChangeAgainst Q`, a pushout square
`sq : IsPushout i f f' j` in Mathlib's orientation, `hi : Q i`, and
`hf : P f`, conclude `P f'`. -/
theorem IsStableUnderCobaseChangeAgainst.of_isPushout
    (h : P.IsStableUnderCobaseChangeAgainst Q)
    {X Y Z W : C} {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ W} {j : Z ⟶ W}
    (sq : IsPushout i f f' j) (hi : Q i) (hf : P f) : P f' :=
  ((h.isStableUnderCobaseChangeAlong i hi).of_isPushout sq hf)

/-- Contravariant restriction of stability in the right-hand class.

From stability against `Q` and `hRQ : R ≤ Q`, conclude stability against `R`. -/
theorem IsStableUnderCobaseChangeAgainst.of_le
    (h : P.IsStableUnderCobaseChangeAgainst Q) (hRQ : R ≤ Q) :
    P.IsStableUnderCobaseChangeAgainst R := by
  constructor
  intro X Y f hf
  exact h.isStableUnderCobaseChangeAlong f (hRQ f hf)

section CoproductClosure

set_option autoImplicit false
noncomputable section

universe ν

/-- Flatten two actual coproduct presentations without changing their endpoint. -/
theorem coproducts_coproducts_le (P : MorphismProperty C) :
    coproducts.{ν} (coproducts.{ν} P) ≤ coproducts.{ν} P := by
  classical
  -- A local witness view. Both cofan points are the original source/target.
  have presentation (Q : MorphismProperty C) {X Y : C} (q : X ⟶ Y)
      (hq : coproducts.{ν} Q q) :
      ∃ (I : Type ν) (A B : I → C)
        (a : ∀ i, A i ⟶ X) (b : ∀ i, B i ⟶ Y)
        (g : ∀ i, A i ⟶ B i)
        (_hA : IsColimit (Cofan.mk X a)) (_hB : IsColimit (Cofan.mk Y b)),
        (∀ i, Q (g i)) ∧ (∀ i, a i ≫ q = g i ≫ b i) := by
    obtain ⟨I, hq⟩ := (coproducts_iff Q q).1 hq
    obtain ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩ := hq
    refine ⟨I, (fun i => F₁.obj ⟨i⟩), (fun i => F₂.obj ⟨i⟩),
      (fun i => c₁.ι.app ⟨i⟩), (fun i => c₂.ι.app ⟨i⟩),
      (fun i => φ.app ⟨i⟩), ?_, ?_, ?_, ?_⟩
    · let e : F₁ ≅ Discrete.functor (fun i : I => F₁.obj ⟨i⟩) :=
        Discrete.natIsoFunctor
      have h : IsColimit ((Cocone.precompose e.inv).obj c₁) :=
        (IsColimit.precomposeInvEquiv e c₁).symm h₁
      apply IsColimit.ofIsoColimit h
      refine Cocone.ext (Iso.refl _) ?_
      rintro ⟨i⟩
      change (𝟙 _ ≫ c₁.ι.app ⟨i⟩) ≫ 𝟙 _ = c₁.ι.app ⟨i⟩
      simp only [Category.id_comp, Category.comp_id]
    · let e : F₂ ≅ Discrete.functor (fun i : I => F₂.obj ⟨i⟩) :=
        Discrete.natIsoFunctor
      have h : IsColimit ((Cocone.precompose e.inv).obj c₂) :=
        (IsColimit.precomposeInvEquiv e c₂).symm h₂
      apply IsColimit.ofIsoColimit h
      refine Cocone.ext (Iso.refl _) ?_
      rintro ⟨i⟩
      change (𝟙 _ ≫ c₂.ι.app ⟨i⟩) ≫ 𝟙 _ = c₂.ι.app ⟨i⟩
      simp only [Category.id_comp, Category.comp_id]
    · intro i
      exact hφ ⟨i⟩
    · intro i
      exact h₁.fac (Cocone.mk _ (φ ≫ c₂.ι)) ⟨i⟩
  -- Descend through supplied inner cofans and then the supplied outer cofan.
  have flatten {I : Type ν} {M : I → C}
      (J : I → Type ν) (A : ∀ i, J i → C)
      (a : ∀ i, ∀ j, A i j ⟶ M i)
      (ha : ∀ i, IsColimit (Cofan.mk (M i) (a i)))
      (c : Cofan M) (hc : IsColimit c) :
      IsColimit (Cofan.mk c.pt
        (fun p : Σ i, J i => a p.1 p.2 ≫ c.inj p.1)) := by
    let desc (d : Cofan (fun p : Σ i, J i => A p.1 p.2)) : c.pt ⟶ d.pt :=
      Cofan.IsColimit.desc hc (fun i =>
        Cofan.IsColimit.desc (ha i) (fun j => d.inj ⟨i, j⟩))
    have fac (d : Cofan (fun p : Σ i, J i => A p.1 p.2)) (p : Σ i, J i) :
        (a p.1 p.2 ≫ c.inj p.1) ≫ desc d = d.inj p := by
      have ho : c.inj p.1 ≫ desc d =
          Cofan.IsColimit.desc (ha p.1) (fun j => d.inj ⟨p.1, j⟩) :=
        Cofan.IsColimit.fac hc _ p.1
      have hi : a p.1 p.2 ≫
          Cofan.IsColimit.desc (ha p.1) (fun j => d.inj ⟨p.1, j⟩) =
          d.inj p := Cofan.IsColimit.fac (ha p.1) _ p.2
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun f => a p.1 p.2 ≫ f) ho).trans hi)
    refine Cofan.IsColimit.mk _ desc fac ?_
    intro d m hm
    refine Cofan.IsColimit.hom_ext hc _ _ (fun i => ?_)
    refine Cofan.IsColimit.hom_ext (ha i) _ _ (fun j => ?_)
    have h₁ : a i j ≫ (c.inj i ≫ m) = d.inj ⟨i, j⟩ :=
      (Category.assoc _ _ _).symm.trans (hm ⟨i, j⟩)
    have h₂ : a i j ≫ (c.inj i ≫ desc d) = d.inj ⟨i, j⟩ :=
      (Category.assoc _ _ _).symm.trans (fac d ⟨i, j⟩)
    exact h₁.trans h₂.symm
  intro X Y q hq
  obtain ⟨I, A, B, a, b, g, hA, hB, hg, hw⟩ :=
    presentation (coproducts.{ν} P) q hq
  choose J S T s t k hS hT hk hst using
    (fun i : I => presentation P (g i) (hg i))
  let c₁ : Cofan (fun p : Σ i, J i => S p.1 p.2) :=
    Cofan.mk X (fun p => s p.1 p.2 ≫ a p.1)
  let c₂ : Cofan (fun p : Σ i, J i => T p.1 p.2) :=
    Cofan.mk Y (fun p => t p.1 p.2 ≫ b p.1)
  have hc₁ : IsColimit c₁ := flatten J S s hS (Cofan.mk X a) hA
  have hc₂ : IsColimit c₂ := flatten J T t hT (Cofan.mk Y b) hB
  apply P.colimitsOfShape_le_coproducts (Σ i, J i) q
  refine colimitsOfShape.mk'
    (Discrete.functor (fun p : Σ i, J i => S p.1 p.2))
    (Discrete.functor (fun p : Σ i, J i => T p.1 p.2))
    c₁ c₂ hc₁ hc₂
    (Discrete.natTrans (fun p => k p.as.1 p.as.2))
    (fun p => hk p.as.1 p.as.2) q ?_
  rintro ⟨⟨i, j⟩⟩
  change (s i j ≫ a i) ≫ q = k i j ≫ (t i j ≫ b i)
  calc
    (s i j ≫ a i) ≫ q = s i j ≫ (a i ≫ q) := Category.assoc _ _ _
    _ = s i j ≫ (g i ≫ b i) := congrArg (fun f => s i j ≫ f) (hw i)
    _ = (s i j ≫ g i) ≫ b i := (Category.assoc _ _ _).symm
    _ = (k i j ≫ t i j) ≫ b i := congrArg (fun f => f ≫ b i) (hst i j)
    _ = k i j ≫ (t i j ≫ b i) := Category.assoc _ _ _

/-- A coproduct of supplied pushout squares is a pushout of their original
coproduct generator map, at the original endpoint. -/
theorem coproducts_pushouts_le [HasCoproducts.{ν} C] (P : MorphismProperty C) :
    coproducts.{ν} P.pushouts ≤ (coproducts.{ν} P).pushouts := by
  classical
  intro X Y q hq
  obtain ⟨I, hq⟩ := (coproducts_iff P.pushouts q).1 hq
  obtain ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩ := hq
  let _ : HasColimitsOfShape (Discrete I) C := inferInstance
  choose A B p f g hp hs using (fun i : I => hφ ⟨i⟩)
  let pAgg : (∐ A) ⟶ ∐ B := CategoryTheory.Limits.Sigma.map p
  let fAgg : (∐ A) ⟶ c₁.pt := Sigma.desc (fun i => f i ≫ c₁.ι.app ⟨i⟩)
  let gAgg : (∐ B) ⟶ c₂.pt := Sigma.desc (fun i => g i ≫ c₂.ι.app ⟨i⟩)
  let q₀ : c₁.pt ⟶ c₂.pt := h₁.desc (Cocone.mk _ (φ ≫ c₂.ι))
  have hg (i : I) : Sigma.ι B i ≫ gAgg = g i ≫ c₂.ι.app ⟨i⟩ :=
    Sigma.ι_comp_desc _ i
  have hq₀ (i : I) : c₁.ι.app ⟨i⟩ ≫ q₀ = φ.app ⟨i⟩ ≫ c₂.ι.app ⟨i⟩ :=
    h₁.fac (Cocone.mk _ (φ ≫ c₂.ι)) ⟨i⟩
  have comm : fAgg ≫ q₀ = pAgg ≫ gAgg := by
    apply Sigma.hom_ext
    intro i
    simp only [fAgg, pAgg, gAgg, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
      Sigma.ι_map_assoc, Category.assoc]
    rw [hq₀ i]
    simpa only [Category.assoc] using
      congrArg (fun h => h ≫ c₂.ι.app ⟨i⟩) (hs i).w
  have compatible (s : PushoutCocone fAgg pAgg) (i : I) :
      f i ≫ (c₁.ι.app ⟨i⟩ ≫ s.inl) = p i ≫ (Sigma.ι B i ≫ s.inr) := by
    have h := congrArg (fun k => Sigma.ι A i ≫ k) s.condition
    simpa only [fAgg, pAgg, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
      Sigma.ι_map, Sigma.ι_map_assoc, Category.assoc] using h
  let desc (s : PushoutCocone fAgg pAgg) : c₂.pt ⟶ s.pt :=
    h₂.desc (Cocone.mk s.pt (Discrete.natTrans (fun i =>
      (hs i.as).desc (c₁.ι.app i ≫ s.inl) (Sigma.ι B i.as ≫ s.inr)
        (compatible s i.as))))
  have hdesc (s : PushoutCocone fAgg pAgg) (i : I) :
      c₂.ι.app ⟨i⟩ ≫ desc s =
        (hs i).desc (c₁.ι.app ⟨i⟩ ≫ s.inl) (Sigma.ι B i ≫ s.inr)
          (compatible s i) :=
    h₂.fac (Cocone.mk s.pt (Discrete.natTrans (fun j =>
      (hs j.as).desc (c₁.ι.app j ≫ s.inl) (Sigma.ι B j.as ≫ s.inr)
        (compatible s j.as)))) ⟨i⟩
  have facLeft (s : PushoutCocone fAgg pAgg) : q₀ ≫ desc s = s.inl := by
    apply h₁.hom_ext
    rintro ⟨i⟩
    calc
      c₁.ι.app ⟨i⟩ ≫ (q₀ ≫ desc s) =
          φ.app ⟨i⟩ ≫ (c₂.ι.app ⟨i⟩ ≫ desc s) := by
        rw [← Category.assoc, hq₀ i, Category.assoc]
      _ = φ.app ⟨i⟩ ≫ (hs i).desc
          (c₁.ι.app ⟨i⟩ ≫ s.inl) (Sigma.ι B i ≫ s.inr) (compatible s i) :=
        congrArg (fun h => φ.app ⟨i⟩ ≫ h) (hdesc s i)
      _ = c₁.ι.app ⟨i⟩ ≫ s.inl :=
        (hs i).inl_desc _ _ (compatible s i)
  have facRight (s : PushoutCocone fAgg pAgg) : gAgg ≫ desc s = s.inr := by
    apply Sigma.hom_ext
    intro i
    calc
      Sigma.ι B i ≫ (gAgg ≫ desc s) =
          g i ≫ (c₂.ι.app ⟨i⟩ ≫ desc s) := by
        rw [← Category.assoc, hg i, Category.assoc]
      _ = g i ≫ (hs i).desc
          (c₁.ι.app ⟨i⟩ ≫ s.inl) (Sigma.ι B i ≫ s.inr) (compatible s i) :=
        congrArg (fun h => g i ≫ h) (hdesc s i)
      _ = Sigma.ι B i ≫ s.inr :=
        (hs i).inr_desc _ _ (compatible s i)
  have uniq (s : PushoutCocone fAgg pAgg) (m : c₂.pt ⟶ s.pt)
      (hmLeft : q₀ ≫ m = s.inl) (hmRight : gAgg ≫ m = s.inr) : m = desc s := by
    apply h₂.hom_ext
    rintro ⟨i⟩
    apply (hs i).hom_ext
    · simpa only [← Category.assoc, hq₀ i] using
        congrArg (fun h => c₁.ι.app ⟨i⟩ ≫ h) (hmLeft.trans (facLeft s).symm)
    · simpa only [← Category.assoc, hg i] using
        congrArg (fun h => Sigma.ι B i ≫ h) (hmRight.trans (facRight s).symm)
  change (coproducts.{ν} P).pushouts q₀
  refine ⟨∐ A, ∐ B, pAgg, fAgg, gAgg, ?_, ?_⟩
  · apply P.colimitsOfShape_le_coproducts I pAgg
    simpa only [pAgg, CategoryTheory.Limits.Sigma.map] using
      (colimitsOfShape_colimMap (W := P)
        (X := Discrete.functor A) (Y := Discrete.functor B)
        (Discrete.natTrans (fun i : Discrete I => p i.as))
        (fun i : Discrete I => hp i.as))
  · exact IsPushout.of_isColimit
      (PushoutCocone.IsColimit.mk comm desc facLeft facRight uniq)

end

end CoproductClosure

end MorphismProperty
end CategoryTheory
