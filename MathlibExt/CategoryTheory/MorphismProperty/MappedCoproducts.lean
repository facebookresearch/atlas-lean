/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Coproducts of literal images of a morphism property

A coproduct of literal functor images has a representative in the image of
any coproduct-stable source property. The comparison retains the supplied
cofans and their whole Arrow isomorphisms.
-/

@[expose] public section

noncomputable section

universe w u v uD vD

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]

/-- A coproduct of literal images is the image of a coproduct,
with the original cofan comparisons. -/
theorem coproducts_strictMap_le_map (P : MorphismProperty C) (F : C ⥤ D)
    [HasCoproducts.{w} C] [PreservesColimitsOfSize.{w, w} F]
    [P.IsStableUnderCoproducts.{w}] :
    (P.strictMap F).coproducts.{w} ≤ P.map F := by
  classical
  intro X Y q hq
  obtain ⟨I, F₁, F₂, c₁, c₂, hc₁, hc₂, α, hα⟩ := (coproducts_iff _ q).mp hq
  let q₀ := hc₁.desc (Cocone.mk _ (α ≫ c₂.ι))
  have representative {X Y : D} (g : X ⟶ Y) (hg : P.strictMap F g) :
      ∃ (A B : C) (f : A ⟶ B), P f ∧ Nonempty (Arrow.mk (F.map f) ≅ Arrow.mk g) := by
    cases hg with
    | map hf => exact ⟨_, _, _, hf, ⟨Iso.refl _⟩⟩
  choose A B f hf hχ using (fun i : I => representative (α.app ⟨i⟩) (hα ⟨i⟩))
  let χ (i : I) : Arrow.mk (F.map (f i)) ≅ Arrow.mk (α.app ⟨i⟩) := (hχ i).some
  let FA := Discrete.functor A
  let FB := Discrete.functor B
  let β : FA ⟶ FB := Discrete.natTrans (fun i => f i.as)
  let e₁ : FA ⋙ F ≅ F₁ := Discrete.natIso (fun i => Arrow.leftFunc.mapIso (χ i.as))
  let e₂ : FB ⋙ F ≅ F₂ := Discrete.natIso (fun i => Arrow.rightFunc.mapIso (χ i.as))
  let c₁' : Cocone (FA ⋙ F) := (Cocone.precompose e₁.hom).obj c₁
  let c₂' : Cocone (FB ⋙ F) := (Cocone.precompose e₂.hom).obj c₂
  let hc₁' : IsColimit c₁' := (IsColimit.precomposeInvEquiv e₁.symm c₁).symm hc₁
  let hc₂' : IsColimit c₂' := (IsColimit.precomposeInvEquiv e₂.symm c₂).symm hc₂
  let hFA := isColimitOfPreserves F (colimit.isColimit FA)
  let hFB := isColimitOfPreserves F (colimit.isColimit FB)
  let s : F.obj (colimit FA) ≅ c₁.pt := hFA.coconePointUniqueUpToIso hc₁'
  let t : F.obj (colimit FB) ≅ c₂.pt := hFB.coconePointUniqueUpToIso hc₂'
  have hs (i : I) : F.map (colimit.ι FA ⟨i⟩) ≫ s.hom = (χ i).hom.left ≫ c₁.ι.app ⟨i⟩ :=
    hFA.comp_coconePointUniqueUpToIso_hom hc₁' ⟨i⟩
  have ht (i : I) : F.map (colimit.ι FB ⟨i⟩) ≫ t.hom = (χ i).hom.right ≫ c₂.ι.app ⟨i⟩ :=
    hFB.comp_coconePointUniqueUpToIso_hom hc₂' ⟨i⟩
  have hq' (i : I) : c₁.ι.app ⟨i⟩ ≫ q₀ = α.app ⟨i⟩ ≫ c₂.ι.app ⟨i⟩ :=
    hc₁.fac (Cocone.mk _ (α ≫ c₂.ι)) ⟨i⟩
  let g : colimit FA ⟶ colimit FB := colimMap β
  have hg : P g := P.colimMap β (fun i => hf i.as)
  have hw : s.hom ≫ q₀ = F.map g ≫ t.hom := by
    apply hFA.hom_ext
    rintro ⟨i⟩
    change F.map (colimit.ι FA ⟨i⟩) ≫ (s.hom ≫ q₀) =
      F.map (colimit.ι FA ⟨i⟩) ≫ (F.map g ≫ t.hom)
    have hχ : (χ i).hom.left ≫ α.app ⟨i⟩ = F.map (f i) ≫ (χ i).hom.right := (χ i).hom.w
    have hb : colimit.ι FA ⟨i⟩ ≫ g = f i ≫ colimit.ι FB ⟨i⟩ := colimit.ι_map β ⟨i⟩
    calc
      F.map (colimit.ι FA ⟨i⟩) ≫ (s.hom ≫ q₀) =
          (χ i).hom.left ≫ c₁.ι.app ⟨i⟩ ≫ q₀ := by rw [← Category.assoc, hs, Category.assoc]
      _ = (χ i).hom.left ≫ α.app ⟨i⟩ ≫ c₂.ι.app ⟨i⟩ := by rw [hq']
      _ = F.map (f i) ≫ (χ i).hom.right ≫ c₂.ι.app ⟨i⟩ := by
        rw [← Category.assoc, hχ, Category.assoc]
      _ = F.map (f i) ≫ F.map (colimit.ι FB ⟨i⟩) ≫ t.hom := by rw [← ht]
      _ = F.map (colimit.ι FA ⟨i⟩) ≫ (F.map g ≫ t.hom) := by
        rw [← Category.assoc, ← F.map_comp, ← hb, F.map_comp, Category.assoc]
  exact ⟨colimit FA, colimit FB, g, hg, ⟨Arrow.isoMk s t hw⟩⟩

end CategoryTheory.MorphismProperty
