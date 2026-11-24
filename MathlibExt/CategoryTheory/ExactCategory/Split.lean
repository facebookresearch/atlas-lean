/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.Functor
public import MathlibExt.Algebra.Homology.ShortComplex.SplittingComp

/-!
# The canonical split exact structure

For an additive category `C` (encoded by `Preadditive`, `HasZeroObject`,
`HasBinaryBiproducts`), a short complex is declared exact when it admits a
splitting. This defines an exact structure.
-/

@[expose] public section

open CategoryTheory Limits Preadditive ShortComplex

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace CategoryTheory.ExactCategory

/-- A short complex is split admissible exact iff it admits a splitting. -/
def isSplitAdmissibleExact (S : ShortComplex C) : Prop :=
  Nonempty S.Splitting

omit [HasBinaryBiproducts C] in
/-- A split admissible exact short complex is short exact. -/
theorem shortExact_of_isSplitAdmissibleExact {S : ShortComplex C}
    (h : isSplitAdmissibleExact S) : S.ShortExact := by
  obtain ⟨s⟩ := h
  exact s.shortExact

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- Being split admissible exact is stable under isomorphisms of short complexes. -/
theorem isSplitAdmissibleExact_of_iso {S T : ShortComplex C} (e : S ≅ T)
    (h : isSplitAdmissibleExact S) : isSplitAdmissibleExact T := by
  obtain ⟨s⟩ := h
  exact ⟨s.ofIso e⟩

section CompositionLemmas

omit [HasZeroObject C] in
private lemma epiComp_desc_zero
    {X₁ X₂ Y Z W : C}
    {f₁ : X₁ ⟶ Y} {g₁ : Y ⟶ Z} {w₁ : f₁ ≫ g₁ = 0}
    {f₂ : X₂ ⟶ Z} {g₂ : Z ⟶ W} {w₂ : f₂ ≫ g₂ = 0}
    (s₁ : (ShortComplex.mk f₁ g₁ w₁).Splitting) :
    biprod.desc f₁ (f₂ ≫ s₁.s) ≫ (g₁ ≫ g₂) = 0 := by
  apply biprod.hom_ext'
  · calc biprod.inl ≫ biprod.desc f₁ (f₂ ≫ s₁.s) ≫ (g₁ ≫ g₂)
        = (biprod.inl ≫ biprod.desc f₁ (f₂ ≫ s₁.s)) ≫ (g₁ ≫ g₂) := by
          simp only [Category.assoc]
      _ = f₁ ≫ (g₁ ≫ g₂) := by simp [biprod.inl_desc]
      _ = (f₁ ≫ g₁) ≫ g₂ := by simp only [Category.assoc]
      _ = 0 ≫ g₂ := by rw [w₁]
      _ = 0 := by simp
      _ = biprod.inl ≫ 0 := by simp
  · calc biprod.inr ≫ biprod.desc f₁ (f₂ ≫ s₁.s) ≫ (g₁ ≫ g₂)
        = (biprod.inr ≫ biprod.desc f₁ (f₂ ≫ s₁.s)) ≫ (g₁ ≫ g₂) := by
          simp only [Category.assoc]
      _ = (f₂ ≫ s₁.s) ≫ (g₁ ≫ g₂) := by simp [biprod.inr_desc]
      _ = f₂ ≫ (s₁.s ≫ g₁) ≫ g₂ := by simp only [Category.assoc]
      _ = f₂ ≫ g₂ := by rw [s₁.s_g]; simp
      _ = 0 := w₂
      _ = biprod.inr ≫ 0 := by simp

omit [HasZeroObject C] in
private noncomputable def epiCompSplitting
    {X₁ X₂ Y Z W : C}
    {f₁ : X₁ ⟶ Y} {g₁ : Y ⟶ Z} {w₁ : f₁ ≫ g₁ = 0}
    {f₂ : X₂ ⟶ Z} {g₂ : Z ⟶ W} {w₂ : f₂ ≫ g₂ = 0}
    (s₁ : (ShortComplex.mk f₁ g₁ w₁).Splitting)
    (s₂ : (ShortComplex.mk f₂ g₂ w₂).Splitting) :
    (ShortComplex.mk (biprod.desc f₁ (f₂ ≫ s₁.s)) (g₁ ≫ g₂)
      (epiComp_desc_zero (w₂:=w₂) s₁)).Splitting where
  r := biprod.lift s₁.r (g₁ ≫ s₂.r)
  s := s₂.s ≫ s₁.s
  f_r := by
    apply biprod.hom_ext'
    · have h_inl_desc : biprod.inl ≫ biprod.desc f₁ (f₂ ≫ s₁.s) = f₁ := by
        simp [biprod.inl_desc]
      have h_f₁_lift : f₁ ≫ biprod.lift s₁.r (g₁ ≫ s₂.r) = biprod.inl := by
        apply biprod.hom_ext
        · calc (f₁ ≫ biprod.lift s₁.r (g₁ ≫ s₂.r)) ≫ biprod.fst
              = f₁ ≫ (biprod.lift s₁.r (g₁ ≫ s₂.r) ≫ biprod.fst) := by
                simp only [Category.assoc]
            _ = f₁ ≫ s₁.r := by simp [biprod.lift_fst]
            _ = 𝟙 X₁ := s₁.f_r
            _ = biprod.inl ≫ biprod.fst := by simp
        · calc (f₁ ≫ biprod.lift s₁.r (g₁ ≫ s₂.r)) ≫ biprod.snd
              = f₁ ≫ (g₁ ≫ s₂.r) := by simp only [Category.assoc, biprod.lift_snd]
            _ = (f₁ ≫ g₁) ≫ s₂.r := by simp only [Category.assoc]
            _ = 0 ≫ s₂.r := by rw [w₁]
            _ = 0 := by simp
            _ = biprod.inl ≫ biprod.snd := by simp
      calc biprod.inl ≫ biprod.desc f₁ (f₂ ≫ s₁.s) ≫ biprod.lift s₁.r (g₁ ≫ s₂.r)
          = f₁ ≫ biprod.lift s₁.r (g₁ ≫ s₂.r) := by
            simp only [← Category.assoc, h_inl_desc]
        _ = biprod.inl := h_f₁_lift
        _ = biprod.inl ≫ 𝟙 (X₁ ⊞ X₂) := by simp
    · have h_inr_desc : biprod.inr ≫ biprod.desc f₁ (f₂ ≫ s₁.s) = f₂ ≫ s₁.s := by
        simp [biprod.inr_desc]
      have h_f₂_lift : (f₂ ≫ s₁.s) ≫ biprod.lift s₁.r (g₁ ≫ s₂.r) = biprod.inr := by
        apply biprod.hom_ext
        · calc ((f₂ ≫ s₁.s) ≫ biprod.lift s₁.r (g₁ ≫ s₂.r)) ≫ biprod.fst
              = (f₂ ≫ s₁.s) ≫ s₁.r := by simp only [Category.assoc, biprod.lift_fst]
            _ = f₂ ≫ (s₁.s ≫ s₁.r) := by simp only [Category.assoc]
            _ = f₂ ≫ 0 := by rw [s₁.s_r]
            _ = 0 := by simp
            _ = biprod.inr ≫ biprod.fst := by simp
        · calc ((f₂ ≫ s₁.s) ≫ biprod.lift s₁.r (g₁ ≫ s₂.r)) ≫ biprod.snd
              = (f₂ ≫ s₁.s) ≫ (g₁ ≫ s₂.r) := by simp only [Category.assoc, biprod.lift_snd]
            _ = f₂ ≫ (s₁.s ≫ g₁) ≫ s₂.r := by simp only [Category.assoc]
            _ = f₂ ≫ s₂.r := by rw [s₁.s_g]; simp
            _ = 𝟙 X₂ := s₂.f_r
            _ = biprod.inr ≫ biprod.snd := by simp
      calc biprod.inr ≫ biprod.desc f₁ (f₂ ≫ s₁.s) ≫ biprod.lift s₁.r (g₁ ≫ s₂.r)
          = (f₂ ≫ s₁.s) ≫ biprod.lift s₁.r (g₁ ≫ s₂.r) := by
            simp only [← Category.assoc, h_inr_desc]
        _ = biprod.inr := h_f₂_lift
        _ = biprod.inr ≫ 𝟙 (X₁ ⊞ X₂) := by simp
  s_g := by
    calc (s₂.s ≫ s₁.s) ≫ (g₁ ≫ g₂)
        = s₂.s ≫ (s₁.s ≫ g₁) ≫ g₂ := by simp only [Category.assoc]
      _ = s₂.s ≫ g₂ := by rw [s₁.s_g]; simp
      _ = 𝟙 W := s₂.s_g
  id := by
    have h_lift_desc : biprod.lift s₁.r (g₁ ≫ s₂.r) ≫ biprod.desc f₁ (f₂ ≫ s₁.s) =
        s₁.r ≫ f₁ + (g₁ ≫ s₂.r) ≫ (f₂ ≫ s₁.s) := by
      rw [biprod.lift_desc]
    calc biprod.lift s₁.r (g₁ ≫ s₂.r) ≫ biprod.desc f₁ (f₂ ≫ s₁.s) +
          (g₁ ≫ g₂) ≫ (s₂.s ≫ s₁.s)
        = (s₁.r ≫ f₁ + (g₁ ≫ s₂.r) ≫ (f₂ ≫ s₁.s)) +
          g₁ ≫ g₂ ≫ s₂.s ≫ s₁.s := by rw [h_lift_desc]; simp only [Category.assoc]
      _ = s₁.r ≫ f₁ + ((g₁ ≫ s₂.r) ≫ (f₂ ≫ s₁.s) + g₁ ≫ g₂ ≫ s₂.s ≫ s₁.s) := by
          abel
      _ = s₁.r ≫ f₁ + (g₁ ≫ s₂.r ≫ f₂ ≫ s₁.s + g₁ ≫ g₂ ≫ s₂.s ≫ s₁.s) := by
          simp only [Category.assoc]
      _ = s₁.r ≫ f₁ + g₁ ≫ (s₂.r ≫ f₂ + g₂ ≫ s₂.s) ≫ s₁.s := by
          simp only [Category.assoc, comp_add, add_comp]
      _ = s₁.r ≫ f₁ + g₁ ≫ s₁.s := by rw [s₂.id]; simp
      _ = 𝟙 Y := s₁.id

end CompositionLemmas

section PushoutPullback

omit [HasZeroObject C] in
private lemma splitMono_pushout_comm
    {X Y Z₁ : C}
    {f : X ⟶ Y} {g₁ : Y ⟶ Z₁} {w₁ : f ≫ g₁ = 0}
    (s₁ : (ShortComplex.mk f g₁ w₁).Splitting)
    {X' : C} (f' : X ⟶ X') :
    f' ≫ (biprod.inl : X' ⟶ X' ⊞ Z₁) = f ≫ biprod.lift (s₁.r ≫ f') g₁ := by
  apply biprod.hom_ext
  · calc (f' ≫ biprod.inl) ≫ biprod.fst
        = f' := by simp only [Category.assoc, biprod.inl_fst, Category.comp_id]
      _ = 𝟙 X ≫ f' := by simp
      _ = (f ≫ s₁.r) ≫ f' := by rw [s₁.f_r]
      _ = f ≫ (s₁.r ≫ f') := by simp only [Category.assoc]
      _ = f ≫ (biprod.lift (s₁.r ≫ f') g₁ ≫ biprod.fst) := by simp only [biprod.lift_fst]
      _ = (f ≫ biprod.lift (s₁.r ≫ f') g₁) ≫ biprod.fst := by
          simp only [← Category.assoc]
  · calc (f' ≫ biprod.inl) ≫ biprod.snd
        = 0 := by simp only [Category.assoc, biprod.inl_snd, comp_zero]
      _ = f ≫ (0 : Y ⟶ Z₁) := by
          have h : f ≫ (0 : Y ⟶ Z₁) = 0 := by simp
          exact h.symm
      _ = f ≫ g₁ := by
          have h0 : f ≫ (0 : Y ⟶ Z₁) = 0 := by simp
          calc f ≫ (0 : Y ⟶ Z₁) = 0 := h0
            _ = f ≫ g₁ := w₁.symm
      _ = f ≫ (biprod.lift (s₁.r ≫ f') g₁ ≫ biprod.snd) := by simp only [biprod.lift_snd]
      _ = (f ≫ biprod.lift (s₁.r ≫ f') g₁) ≫ biprod.snd := by
          simp only [← Category.assoc]

omit [HasZeroObject C] in
private noncomputable abbrev splitMono_pushoutCocone
    {X Y Z₁ : C}
    {f : X ⟶ Y} {g₁ : Y ⟶ Z₁} {w₁ : f ≫ g₁ = 0}
    (s₁ : (ShortComplex.mk f g₁ w₁).Splitting)
    {X' : C} (f' : X ⟶ X') :
    PushoutCocone f' f :=
  PushoutCocone.mk (biprod.inl : X' ⟶ X' ⊞ Z₁)
    (biprod.lift (s₁.r ≫ f') g₁ : Y ⟶ X' ⊞ Z₁)
    (splitMono_pushout_comm s₁ f')

omit [HasZeroObject C] in
private noncomputable def splitMono_pushout_isColimit
    {X Y Z₁ : C}
    {f : X ⟶ Y} {g₁ : Y ⟶ Z₁} {w₁ : f ≫ g₁ = 0}
    (s₁ : (ShortComplex.mk f g₁ w₁).Splitting)
    {X' : C} (f' : X ⟶ X') :
    IsColimit (splitMono_pushoutCocone s₁ f') := by
  let c := splitMono_pushoutCocone s₁ f'
  apply PushoutCocone.isColimitAux' (t:=c)
  intro s
  have hcomm : f' ≫ s.inl = f ≫ s.inr := s.condition
  let l : c.pt ⟶ s.pt := biprod.desc s.inl (s₁.s ≫ s.inr)
  have hl_inl : c.inl ≫ l = s.inl := by
    calc c.inl ≫ l = biprod.inl ≫ biprod.desc s.inl (s₁.s ≫ s.inr) := rfl
      _ = s.inl := by simp only [biprod.inl_desc]
  have hl_inr : c.inr ≫ l = s.inr := by
    have h_lift_desc : c.inr ≫ l =
        (s₁.r ≫ f') ≫ s.inl + g₁ ≫ (s₁.s ≫ s.inr) := by
      calc c.inr ≫ l
          = biprod.lift (s₁.r ≫ f') g₁ ≫ biprod.desc s.inl (s₁.s ≫ s.inr) := rfl
        _ = (s₁.r ≫ f') ≫ s.inl + g₁ ≫ (s₁.s ≫ s.inr) := by rw [biprod.lift_desc]
    calc c.inr ≫ l
        = (s₁.r ≫ f') ≫ s.inl + g₁ ≫ (s₁.s ≫ s.inr) := h_lift_desc
      _ = s₁.r ≫ (f' ≫ s.inl) + g₁ ≫ s₁.s ≫ s.inr := by simp only [Category.assoc]
      _ = s₁.r ≫ (f ≫ s.inr) + g₁ ≫ s₁.s ≫ s.inr := by rw [hcomm]
      _ = (s₁.r ≫ f + g₁ ≫ s₁.s) ≫ s.inr := by simp only [Category.assoc, add_comp]
      _ = s.inr := by rw [s₁.id]; simp
  refine ⟨l, hl_inl, hl_inr, ?_⟩
  intro m hm_inl hm_inr
  have h_s_inr' : s₁.s ≫ (splitMono_pushoutCocone s₁ f').inr = biprod.inr := by
    let inr' : Y ⟶ X' ⊞ Z₁ := (splitMono_pushoutCocone s₁ f').inr
    have hinr_def : inr' = biprod.lift (s₁.r ≫ f') g₁ := rfl
    have hpt : (splitMono_pushoutCocone s₁ f').pt = (X' ⊞ Z₁) := rfl
    apply biprod.hom_ext
    · calc (s₁.s ≫ inr') ≫ biprod.fst
          = s₁.s ≫ (inr' ≫ biprod.fst) := by rw [Category.assoc]
        _ = s₁.s ≫ (s₁.r ≫ f') := by
            calc s₁.s ≫ (inr' ≫ biprod.fst)
                = s₁.s ≫ (biprod.lift (s₁.r ≫ f') g₁ ≫ biprod.fst) := by rw [hinr_def]
              _ = s₁.s ≫ (s₁.r ≫ f') := by simp only [biprod.lift_fst]
        _ = (s₁.s ≫ s₁.r) ≫ f' := by rw [← Category.assoc]
        _ = 0 ≫ f' := by rw [s₁.s_r]
        _ = 0 := by simp
        _ = biprod.inr ≫ biprod.fst := by simp
    · calc (s₁.s ≫ inr') ≫ biprod.snd
          = s₁.s ≫ (inr' ≫ biprod.snd) := by rw [Category.assoc]
        _ = s₁.s ≫ g₁ := by
            calc s₁.s ≫ (inr' ≫ biprod.snd)
                = s₁.s ≫ (biprod.lift (s₁.r ≫ f') g₁ ≫ biprod.snd) := by rw [hinr_def]
              _ = s₁.s ≫ g₁ := by simp only [biprod.lift_snd]
        _ = 𝟙 Z₁ := s₁.s_g
        _ = biprod.inr ≫ biprod.snd := by simp
  have h_s_inr : s₁.s ≫ c.inr = biprod.inr := by
    dsimp only [c]
    exact h_s_inr'
  apply biprod.hom_ext'
  · calc biprod.inl ≫ m
        = c.inl ≫ m := rfl
      _ = s.inl := hm_inl
      _ = c.inl ≫ l := hl_inl.symm
      _ = biprod.inl ≫ l := rfl
  · calc biprod.inr ≫ m
        = (s₁.s ≫ c.inr) ≫ m := congrArg (· ≫ m) h_s_inr.symm
      _ = s₁.s ≫ (c.inr ≫ m) := by rw [Category.assoc]
      _ = s₁.s ≫ s.inr := by rw [hm_inr]
      _ = biprod.inr ≫ l := by simp only [l, biprod.inr_desc]

omit [HasZeroObject C] in
private lemma splitEpi_pullback_comm
    {X₁ Y Z : C}
    {f₁ : X₁ ⟶ Y} {g₁ : Y ⟶ Z} {w₁ : f₁ ≫ g₁ = 0}
    (s₁ : (ShortComplex.mk f₁ g₁ w₁).Splitting)
    {Z' : C} (g' : Z' ⟶ Z) :
    (biprod.snd : X₁ ⊞ Z' ⟶ Z') ≫ g' = biprod.desc f₁ (g' ≫ s₁.s) ≫ g₁ := by
  apply biprod.hom_ext'
  · calc biprod.inl ≫ (biprod.snd : X₁ ⊞ Z' ⟶ Z') ≫ g'
          = (biprod.inl ≫ biprod.snd) ≫ g' := by rw [Category.assoc]
        _ = 0 ≫ g' := by rw [biprod.inl_snd]
        _ = 0 := by simp
        _ = f₁ ≫ g₁ := w₁.symm
        _ = (biprod.inl ≫ biprod.desc f₁ (g' ≫ s₁.s)) ≫ g₁ := by
            simp only [biprod.inl_desc]
        _ = biprod.inl ≫ biprod.desc f₁ (g' ≫ s₁.s) ≫ g₁ := by
            rw [← Category.assoc]
  · calc biprod.inr ≫ (biprod.snd : X₁ ⊞ Z' ⟶ Z') ≫ g'
          = (biprod.inr ≫ biprod.snd) ≫ g' := by rw [Category.assoc]
        _ = g' := by simp
        _ = g' ≫ (s₁.s ≫ g₁) := by rw [s₁.s_g]; simp
        _ = (g' ≫ s₁.s) ≫ g₁ := by simp only [Category.assoc]
        _ = (biprod.inr ≫ biprod.desc f₁ (g' ≫ s₁.s)) ≫ g₁ := by
            simp only [biprod.inr_desc]
        _ = biprod.inr ≫ biprod.desc f₁ (g' ≫ s₁.s) ≫ g₁ := by
            rw [← Category.assoc]

omit [HasZeroObject C] in
private noncomputable abbrev splitEpi_pullbackCone
    {X₁ Y Z : C}
    {f₁ : X₁ ⟶ Y} {g₁ : Y ⟶ Z} {w₁ : f₁ ≫ g₁ = 0}
    (s₁ : (ShortComplex.mk f₁ g₁ w₁).Splitting)
    {Z' : C} (g' : Z' ⟶ Z) :
    PullbackCone g' g₁ :=
  PullbackCone.mk (biprod.snd : X₁ ⊞ Z' ⟶ Z')
    (biprod.desc f₁ (g' ≫ s₁.s) : X₁ ⊞ Z' ⟶ Y)
    (splitEpi_pullback_comm s₁ g')

omit [HasZeroObject C] in
private noncomputable def splitEpi_pullback_isLimit
    {X₁ Y Z : C}
    {f₁ : X₁ ⟶ Y} {g₁ : Y ⟶ Z} {w₁ : f₁ ≫ g₁ = 0}
    (s₁ : (ShortComplex.mk f₁ g₁ w₁).Splitting)
    {Z' : C} (g' : Z' ⟶ Z) :
    IsLimit (splitEpi_pullbackCone s₁ g') := by
  let c := splitEpi_pullbackCone s₁ g'
  have hc_fst : c.fst = (biprod.snd : X₁ ⊞ Z' ⟶ Z') := rfl
  have hc_snd : c.snd = biprod.desc f₁ (g' ≫ s₁.s) := rfl
  apply PullbackCone.isLimitAux' (t:=c)
  intro t
  have hcomm : t.fst ≫ g' = t.snd ≫ g₁ := t.condition
  let l : t.pt ⟶ c.pt := biprod.lift (t.snd ≫ s₁.r) t.fst
  have hl_fst : l ≫ c.fst = t.fst := by
    calc l ≫ c.fst
        = biprod.lift (t.snd ≫ s₁.r) t.fst ≫ c.fst := rfl
      _ = biprod.lift (t.snd ≫ s₁.r) t.fst ≫ biprod.snd := by rw [hc_fst]
      _ = t.fst := by rw [biprod.lift_snd]
  have hl_snd : l ≫ c.snd = t.snd := by
    calc l ≫ c.snd
        = biprod.lift (t.snd ≫ s₁.r) t.fst ≫ c.snd := rfl
      _ = biprod.lift (t.snd ≫ s₁.r) t.fst ≫ biprod.desc f₁ (g' ≫ s₁.s) := by
          rw [hc_snd]
      _ = (t.snd ≫ s₁.r) ≫ f₁ + t.fst ≫ (g' ≫ s₁.s) := by
          rw [biprod.lift_desc]
      _ = (t.snd ≫ s₁.r) ≫ f₁ + (t.fst ≫ g') ≫ s₁.s := by
          simp only [Category.assoc]
      _ = (t.snd ≫ s₁.r) ≫ f₁ + (t.snd ≫ g₁) ≫ s₁.s := by rw [hcomm]
      _ = t.snd ≫ (s₁.r ≫ f₁) + t.snd ≫ (g₁ ≫ s₁.s) := by
          simp only [Category.assoc]
      _ = t.snd ≫ (s₁.r ≫ f₁ + g₁ ≫ s₁.s) := by rw [← comp_add]
      _ = t.snd := by rw [s₁.id]; simp
  refine ⟨l, hl_fst, hl_snd, ?_⟩
  intro m hm_fst hm_snd
  have h_desc_r : c.snd ≫ s₁.r = (biprod.fst : c.pt ⟶ X₁) := by
    apply biprod.hom_ext'
    · calc biprod.inl ≫ (c.snd ≫ s₁.r)
          = f₁ ≫ s₁.r := by simp [hc_snd]
        _ = 𝟙 X₁ := s₁.f_r
        _ = biprod.inl ≫ (biprod.fst : c.pt ⟶ X₁) := by simp
    · calc biprod.inr ≫ (c.snd ≫ s₁.r)
          = (g' ≫ s₁.s) ≫ s₁.r := by simp [hc_snd]
        _ = g' ≫ (s₁.s ≫ s₁.r) := by simp only [Category.assoc]
        _ = g' ≫ 0 := by rw [s₁.s_r]
        _ = 0 := by simp
        _ = biprod.inr ≫ (biprod.fst : c.pt ⟶ X₁) := by simp
  have hl_fst' : l ≫ (biprod.fst : c.pt ⟶ X₁) = t.snd ≫ s₁.r := by
    calc l ≫ (biprod.fst : c.pt ⟶ X₁)
        = biprod.lift (t.snd ≫ s₁.r) t.fst ≫ (biprod.fst : c.pt ⟶ X₁) := rfl
      _ = t.snd ≫ s₁.r := by simp [biprod.lift_fst]
  have hl_snd' : l ≫ (biprod.snd : c.pt ⟶ Z') = t.fst := by
    calc l ≫ (biprod.snd : c.pt ⟶ Z')
        = biprod.lift (t.snd ≫ s₁.r) t.fst ≫ (biprod.snd : c.pt ⟶ Z') := rfl
      _ = t.fst := by simp [biprod.lift_snd]
  apply biprod.hom_ext
  · calc m ≫ (biprod.fst : c.pt ⟶ X₁)
        = m ≫ (c.snd ≫ s₁.r) := by rw [h_desc_r]
      _ = (m ≫ c.snd) ≫ s₁.r := by simp only [Category.assoc]
      _ = t.snd ≫ s₁.r := by rw [hm_snd]
      _ = l ≫ (biprod.fst : c.pt ⟶ X₁) := hl_fst'.symm
  · calc m ≫ (biprod.snd : c.pt ⟶ Z')
        = m ≫ c.fst := by rw [hc_fst]
      _ = t.fst := hm_fst
      _ = l ≫ c.fst := hl_fst.symm
      _ = l ≫ (biprod.snd : c.pt ⟶ Z') := by rw [hc_fst]

end PushoutPullback

section ExactStructure

/-- Any split short complex is admissible exact for the ambient exact structure. -/
theorem isAdmissibleExact_of_splitting {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {S : ShortComplex D} (s : S.Splitting) : IsAdmissibleExact S := by
  let iso₂ : S.X₂ ≅ S.X₁ ⊞ S.X₃ := s.isoBinaryBiproduct
  have h_f_lift : S.f ≫ iso₂.hom = biprod.inl := by
    calc S.f ≫ iso₂.hom
        = S.f ≫ biprod.lift s.r S.g := rfl
      _ = biprod.lift (S.f ≫ s.r) (S.f ≫ S.g) := by
          apply biprod.hom_ext <;> simp [biprod.lift_fst, biprod.lift_snd, Category.assoc]
      _ = biprod.lift (𝟙 S.X₁) 0 := by rw [s.f_r, S.zero]
      _ = biprod.inl := by
          apply biprod.hom_ext
          · simp [biprod.lift_fst]
          · simp [biprod.lift_snd]
  have h_comm₁₂ : (Iso.refl S.X₁).hom ≫ biprod.inl = S.f ≫ iso₂.hom := by
    simp [h_f_lift]
  have h_comm₂₃ : iso₂.hom ≫ biprod.snd = S.g ≫ (Iso.refl S.X₃).hom := by
    simp [iso₂]
  let e : S ≅ ShortComplex.mk (biprod.inl : S.X₁ ⟶ S.X₁ ⊞ S.X₃)
      biprod.snd (by simp) :=
    ShortComplex.isoMk (Iso.refl S.X₁) iso₂ (Iso.refl S.X₃) h_comm₁₂ h_comm₂₃
  have h_adm : IsAdmissibleExact
      (ShortComplex.mk (biprod.inl : S.X₁ ⟶ S.X₁ ⊞ S.X₃) biprod.snd (by simp)) :=
    isAdmissibleExact_split S.X₁ S.X₃
  exact isAdmissibleExact_of_iso e.symm h_adm

/-- The split exact structure on an additive category: a short complex is admissible exact
iff it splits. This is a `def`, not a global instance, so importing `Split` does not
silently equip every additive category with an `ExactCategory` instance. -/
@[instance_reducible]
def splitExactCategory : ExactCategory C where
  IsAdmissibleExact := isSplitAdmissibleExact
  shortExact_of_isAdmissibleExact S h := shortExact_of_isSplitAdmissibleExact h
  isLimit_kernelFork := by
    intro S h
    obtain ⟨s⟩ := h
    exact ⟨s.fIsKernel⟩
  isColimit_cokernelCofork := by
    intro S h
    obtain ⟨s⟩ := h
    exact ⟨s.gIsCokernel⟩
  isAdmissibleExact_of_iso S T e h := isSplitAdmissibleExact_of_iso e h
  isAdmissibleExact_split X Y := ⟨Splitting.ofHasBinaryBiproduct X Y⟩
  admissibleMono_comp := by
    constructor
    intro X Y Z f g hf hg
    obtain ⟨Z₁, g₁, w₁, ⟨s₁⟩⟩ := hf
    obtain ⟨Z₂, g₂, w₂, ⟨s₂⟩⟩ := hg
    exact ⟨Z₁ ⊞ Z₂, biprod.lift (s₂.r ≫ g₁) g₂,
      ShortComplex.Splitting.compLeft_zero (w₁ := w₁) s₂,
      ⟨ShortComplex.Splitting.compLeft s₁ s₂⟩⟩
  admissibleEpi_comp := by
    constructor
    intro X Y Z f g hf hg
    obtain ⟨X₁, f₁, w₁, ⟨s₁⟩⟩ := hf
    obtain ⟨X₂, f₂, w₂, ⟨s₂⟩⟩ := hg
    exact ⟨X₁ ⊞ X₂, biprod.desc f₁ (f₂ ≫ s₁.s), epiComp_desc_zero (w₂:=w₂) s₁,
      ⟨epiCompSplitting s₁ s₂⟩⟩
  admissibleMono_pushout := by
    intro X Y i hi X' f
    obtain ⟨Z₁, g₁, w₁, ⟨s₁⟩⟩ := hi
    let P := X' ⊞ Z₁
    let inl : X' ⟶ P := biprod.inl
    let inr : Y ⟶ P := biprod.lift (s₁.r ≫ f) g₁
    have hcomm : f ≫ inl = i ≫ inr := splitMono_pushout_comm s₁ f
    let sq : CommSq f i inl inr := ⟨hcomm⟩
    have hcolim : IsColimit sq.cocone :=
      splitMono_pushout_isColimit s₁ f
    refine ⟨P, inl, inr, IsPushout.of_isColimit' sq hcolim, ?_⟩
    exact ⟨Z₁, biprod.snd, biprod.inl_snd, ⟨Splitting.ofHasBinaryBiproduct X' Z₁⟩⟩
  admissibleEpi_pullback := by
    intro Y Z p hp Z' g
    obtain ⟨X₁, f₁, w₁, ⟨s₁⟩⟩ := hp
    let P := X₁ ⊞ Z'
    let fst : P ⟶ Z' := biprod.snd
    let snd : P ⟶ Y := biprod.desc f₁ (g ≫ s₁.s)
    have hcomm : fst ≫ g = snd ≫ p := splitEpi_pullback_comm s₁ g
    let sq : CommSq fst snd g p := ⟨hcomm⟩
    have hlim : IsLimit sq.cone :=
      splitEpi_pullback_isLimit s₁ g
    refine ⟨P, fst, snd, IsPullback.of_isLimit' sq hlim, ?_⟩
    exact ⟨X₁, biprod.inl, biprod.inl_snd, ⟨Splitting.ofHasBinaryBiproduct X₁ Z'⟩⟩

end ExactStructure

section Functoriality

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]
variable {F : C ⥤ D} [F.Additive]

omit [HasZeroObject C] [HasBinaryBiproducts C] [HasZeroObject D]
     [HasBinaryBiproducts D] in
/-- Additive functors preserve split admissible exactness. -/
theorem isSplitAdmissibleExact_map (S : ShortComplex C)
    (h : isSplitAdmissibleExact S) :
    isSplitAdmissibleExact (S.map F) := by
  obtain ⟨s⟩ := h
  exact ⟨s.map F⟩

/-- Local split instance for exactness results in this section. -/
local instance : ExactCategory C := splitExactCategory

/-- Every additive functor out of the split exact structure is exact. -/
theorem isExact_splitSource {E : Type u₃} [Category.{v₃} E] [Preadditive E]
    [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
    (F : C ⥤ E) [F.Additive] : F.IsExact :=
  { map_admissibleExact := fun S hS => by
      have hsplit : isSplitAdmissibleExact S := hS
      obtain ⟨s⟩ := isSplitAdmissibleExact_map (F:=F) S hsplit
      exact isAdmissibleExact_of_splitting s }

end Functoriality

end CategoryTheory.ExactCategory
