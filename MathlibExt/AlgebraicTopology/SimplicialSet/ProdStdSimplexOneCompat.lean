/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular

import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Gluing the standard simplices of `Δ[p] ⊗ Δ[1]`

This backport supplies the pushouts for the standard prism filtration, the resulting
existence and extensionality lemmas for maps out of the prism, and the face formulas for
its top-dimensional simplices. The enumeration and basic filtration are in Mathlib.

Source: Mathlib PR #42435 (`e09070f786c9fc0a688e6239d71230b618b045ff`),
`Mathlib/AlgebraicTopology/SimplicialSet/ProdStdSimplexOne.lean`,
blob `b7fe9406e4ca9716a2a74c7895222dc47a2f12d6`. The earlier compatibility extraction
and proof adaptations are by @toskua and Avocado. This port uses the Mathlib 4.36
Yoneda naturality and generated-subcomplex isomorphism APIs.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite CartesianMonoidalCategory

open scoped Simplicial

namespace SSet

namespace prodStdSimplex₁

variable {p : ℕ}

set_option backward.isDefEq.respectTransparency.types false in
lemma mem_range_objEquiv_nonDegenerateEquiv₀_iff (i x : Fin (p + 1)) :
    dsimp% (x, 0) ∈ Set.range (prodStdSimplex.objEquiv (nonDegenerateEquiv i).val) ↔ x ≤ i := by
  constructor
  · rintro ⟨y, hy⟩
    have hy₁ := congr_arg Prod.fst hy
    have hy₂ := congr_arg Prod.snd hy
    dsimp at hy₁ hy₂
    rw [stdSimplex.objMk₁_apply_eq_zero_iff, Fin.succ_castSucc,
      Fin.castSucc_lt_castSucc_iff] at hy₂
    rw [← hy₁, stdSimplex.objEquiv_symm_apply]
    change i.predAbove y ≤ i
    rw [Fin.predAbove_of_lt_succ _ _ hy₂, ← Fin.castSucc_le_castSucc_iff,
      Fin.castSucc_castPred, Fin.le_castSucc_iff]
    exact hy₂
  · refine fun hx ↦ ⟨x.castSucc, Prod.ext ?_ ?_⟩
    · change i.predAbove x.castSucc = x
      rw [Fin.predAbove_of_le_castSucc _ _ (by simpa), Fin.castPred_castSucc]
    · simpa [stdSimplex.objMk₁_apply_eq_zero_iff]

set_option backward.isDefEq.respectTransparency.types false in
lemma mem_range_objEquiv_nonDegenerateEquiv₁_iff (i x : Fin (p + 1)) :
    dsimp% (x, 1) ∈ Set.range (prodStdSimplex.objEquiv (nonDegenerateEquiv i).val) ↔ i ≤ x := by
  constructor
  · intro ⟨y, hy⟩
    have hy₁ := congr_arg Prod.fst hy
    have hy₂ := congr_arg Prod.snd hy
    dsimp at hy₁ hy₂
    rw [stdSimplex.objMk₁_apply_eq_one_iff, Fin.succ_castSucc, Fin.castSucc_le_castSucc_iff] at hy₂
    rw [← hy₁, stdSimplex.objEquiv_symm_apply]
    change i ≤ i.predAbove y
    rw [Fin.predAbove_of_succ_le _ _ hy₂, ← Fin.succ_le_succ_iff, Fin.succ_pred]
    exact hy₂
  · refine fun hx ↦ ⟨x.succ, Prod.ext ?_ ?_⟩
    · change i.predAbove x.succ = x
      rw [Fin.predAbove_of_succ_le _ _ (by simpa), Fin.pred_succ]
    · simpa [stdSimplex.objMk₁_apply_eq_one_iff]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma ofSimplex_codimOneSimplex (j : Fin p) :
    Subcomplex.ofSimplex (codimOneSimplex.{u} j.succ.castSucc).val =
      intersectionNondeg j.castSucc j.succ := by
  apply le_antisymm
  · dsimp [intersectionNondeg]
    simp only [le_inf_iff, Subcomplex.ofSimplex_le_iff,
      Subcomplex.mem_ofSimplex_obj_iff]
    constructor
    · refine ⟨SimplexCategory.δ j.succ.castSucc, ?_⟩
      rw [← Fin.succ_castSucc, ← δ_succ_nonDegenerateEquiv]
      rfl
    · refine ⟨SimplexCategory.δ j.succ.castSucc, ?_⟩
      rw [Fin.succ_castSucc, ← δ_castSucc_nonDegenerateEquiv]
      rfl
  · rintro ⟨⟨k⟩⟩ s hs
    obtain ⟨f, rfl⟩ := prodStdSimplex.objEquiv.symm.surjective s
    simp only [← Subcomplex.ofSimplex_le_iff, prodStdSimplex.ofSimplex_le_ofSimplex_iff,
      intersectionNondeg,
      Subfunctor.min_obj, Set.mem_inter_iff, Equiv.apply_symm_apply] at hs ⊢
    rintro ⟨x, y⟩ hxy
    refine ⟨x, Prod.ext rfl ?_⟩
    obtain ⟨x₁, h₁⟩ := hs.1 hxy
    obtain ⟨x₂, h₂⟩ := hs.2 hxy
    have h₁₁ := congr_arg Prod.fst h₁
    have h₁₂ := congr_arg Prod.snd h₁
    have h₂₁ := congr_arg Prod.fst h₂
    have h₂₂ := congr_arg Prod.snd h₂
    dsimp at h₁₁ h₁₂ h₂₁ h₂₂ ⊢
    change j.castSucc.predAbove x₁ = x at h₁₁
    change j.succ.predAbove x₂ = x at h₂₁
    fin_cases y
    · dsimp at h₁₂ h₂₂ ⊢
      simp only [stdSimplex.objMk₁_apply_eq_zero_iff, ← Fin.le_castSucc_iff,
        Fin.castSucc_le_castSucc_iff, Fin.castSucc_succ] at h₁₂ h₂₂ ⊢
      rw [Fin.predAbove_of_le_castSucc _ _ h₁₂] at h₁₁
      simpa [← h₁₁] using! h₁₂
    · dsimp at h₁₂ h₂₂ ⊢
      simp only [stdSimplex.objMk₁_apply_eq_one_iff, Fin.succ_le_castSucc_iff] at h₁₂ h₂₂ ⊢
      rw [Fin.predAbove_of_castSucc_lt _ _ h₂₂] at h₂₁
      rwa [← h₂₁, ← Fin.succ_lt_succ_iff, Fin.succ_pred]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma intersectionNondeg_le_intersectionNondeg (i j k : Fin (p + 1))
    (hij : i ≤ j) (hjk : j ≤ k) :
    intersectionNondeg.{u} i k ≤ intersectionNondeg j k := by
  rintro ⟨⟨k⟩⟩ x hx
  simp only [← Subcomplex.ofSimplex_le_iff, prodStdSimplex.ofSimplex_le_ofSimplex_iff,
      intersectionNondeg, Subfunctor.min_obj,
    Set.mem_inter_iff, ← Set.subset_inter_iff] at hx ⊢
  refine hx.trans (fun (x, y) hxy ↦ ?_)
  simp only [Set.mem_inter_iff] at hxy ⊢
  fin_cases y
  all_goals
  · dsimp at hxy ⊢
    simp only [mem_range_objEquiv_nonDegenerateEquiv₀_iff,
      mem_range_objEquiv_nonDegenerateEquiv₁_iff] at hxy ⊢
    lia

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma intersectionNondeg_le_intersectionNondeg' (i j k : Fin (p + 1))
    (hij : i ≤ j) (hjk : j ≤ k) :
    intersectionNondeg.{u} i k ≤ intersectionNondeg i j := by
  rintro ⟨⟨k⟩⟩ x hx
  simp only [← Subcomplex.ofSimplex_le_iff, prodStdSimplex.ofSimplex_le_ofSimplex_iff,
      intersectionNondeg, Subfunctor.min_obj,
    Set.mem_inter_iff, ← Set.subset_inter_iff] at hx ⊢
  refine hx.trans (fun (x, y) hxy ↦ ?_)
  simp only [Set.mem_inter_iff] at hxy ⊢
  fin_cases y
  all_goals
  · dsimp at hxy ⊢
    simp only [mem_range_objEquiv_nonDegenerateEquiv₀_iff,
      mem_range_objEquiv_nonDegenerateEquiv₁_iff] at hxy ⊢
    lia

lemma filtration.bicartSq (j : Fin p) :
    Subcomplex.BicartSq (Subcomplex.ofSimplex (codimOneSimplex.{u} j.succ.castSucc).1)
      (filtration.{u} j.castSucc) (.ofSimplex (nonDegenerateEquiv j.succ).1)
      (filtration.{u} j.succ) where
  inf_eq := by
    rw [ofSimplex_codimOneSimplex]
    apply le_antisymm
    · dsimp [filtration]
      rw [Subfunctor.iSup_min, iSup_le_iff, Subtype.forall]
      intro i hi
      exact intersectionNondeg_le_intersectionNondeg _ _ _ (Set.mem_Iic.mp hi) j.castSucc_le_succ
    · dsimp [intersectionNondeg]
      simp only [le_inf_iff, inf_le_right, and_true]
      exact inf_le_left.trans (ofSimplex_le_filtration (by rfl))
  sup_eq := by
    dsimp [filtration]
    refine le_antisymm ?_ ?_
    · rw [sup_le_iff, iSup_le_iff, Subtype.forall]
      refine ⟨fun i hi ↦ ?_, ?_⟩
      · exact ofSimplex_le_filtration ((Set.mem_Iic.mp hi).trans (j.castSucc_le_succ))
      · exact ofSimplex_le_filtration (by rfl)
    · rw [iSup_le_iff, Subtype.forall]
      intro i hi
      obtain hi | rfl := (Set.mem_Iic.mp hi).lt_or_eq
      · refine le_trans ?_ le_sup_left
        exact ofSimplex_le_filtration (Fin.le_castSucc_iff.2 hi)
      · exact le_sup_right

/-- Assuming the inequality `i ≤ j` in `Fin (p + 1)`, this is
the inclusion `Δ[p + 1] ⟶ filtration.{u} j` of the `i`th
non-degenerate `(p + 1)`-simplex in `Δ[p] ⊗ Δ[1]` of the
enumeration `nonDegenerateEquiv`. -/
noncomputable def filtration.ι {i j : Fin (p + 1)} (hi : i ≤ j) :
    Δ[p + 1] ⟶ filtration.{u} j :=
  Subcomplex.lift
    (yonedaEquiv.symm (nonDegenerateEquiv i)) (by
      rw [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]
      exact ofSimplex_le_filtration hi)

@[reassoc (attr := simp)]
lemma filtration.ι_ι (i j : Fin (p + 1)) (hi : i ≤ j) :
    filtration.ι.{u} hi ≫ (filtration j).ι =
      yonedaEquiv.symm (nonDegenerateEquiv i).val := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given `j : Fin p`, the subcomplex `filtration j.succ` of `Δ[p] ⊗ Δ[1]`
is the pushout of `filtration j` and of the inclusion
`filtration.ι j.succ : Δ[p + 1] ⟶ (filtration j.succ).toSSet`
along the `j.succ.castSucc`th face of `Δ[p + 1]`. -/
lemma filtration.isPushout (j : Fin p) :
    IsPushout
      (stdSimplex.{u}.δ j.succ.castSucc ≫ ι (le_refl j.castSucc))
      (stdSimplex.δ j.succ.castSucc)
      (Subcomplex.homOfLE (filtration_monotone j.castSucc_le_succ))
      (ι (le_refl j.succ)) := by
  fapply (filtration.bicartSq.{u} j).isPushout.of_iso'
    (Nonsingular.iso _ (codimOneSimplex j.succ.castSucc).property) (Iso.refl _)
    (Nonsingular.iso _ (nonDegenerateEquiv j.succ).property) (Iso.refl _)
  · rw [← cancel_mono (Subcomplex.ι (filtration j.castSucc))]
    simp only [Category.assoc, Category.comp_id, Iso.refl_hom,
      filtration.ι_ι]
    rw [Subcomplex.homOfLE_ι,
      Nonsingular.iso_hom, Subcomplex.toOfSimplex_ι]
    change yonedaEquiv.symm (codimOneSimplex j.succ.castSucc).val =
      (stdSimplex : SimplexCategory ⥤ SSet).map (SimplexCategory.δ j.succ.castSucc) ≫
        yonedaEquiv.symm (nonDegenerateEquiv j.castSucc).val
    rw [yonedaEquiv_symm_naturality_left (X := (Δ[p] ⊗ Δ[1] : SSet))
      (f := SimplexCategory.δ j.succ.castSucc)
      (g := (nonDegenerateEquiv j.castSucc).val)]
    rw [← Fin.succ_castSucc]
    rw [← δ_succ_nonDegenerateEquiv (j := j.castSucc)]
    simp only [SimplicialObject.δ]
  · rw [← cancel_mono (Subcomplex.ι (Subcomplex.ofSimplex (nonDegenerateEquiv j.succ).val))]
    simp only [Category.assoc, Subcomplex.homOfLE_ι,
      Nonsingular.iso_hom, Subcomplex.toOfSimplex_ι]
    change yonedaEquiv.symm (codimOneSimplex j.succ.castSucc).val =
      (stdSimplex : SimplexCategory ⥤ SSet).map (SimplexCategory.δ j.succ.castSucc) ≫
        yonedaEquiv.symm (nonDegenerateEquiv j.succ).val
    rw [yonedaEquiv_symm_naturality_left (X := (Δ[p] ⊗ Δ[1] : SSet))
      (f := SimplexCategory.δ j.succ.castSucc)
      (g := (nonDegenerateEquiv j.succ).val)]
    rw [← δ_castSucc_nonDegenerateEquiv (j := j.succ)]
    simp only [SimplicialObject.δ]
  · simp
  · cat_disch

lemma filtration.exists_desc
    {X : SSet.{u}} {j : Fin (p + 1)}
    (α : ∀ (i : Fin (p + 1)) (_ : i ≤ j), Δ[p + 1] ⟶ X)
    (hα : ∀ (i : Fin p) (hi : i.succ ≤ j),
      stdSimplex.δ i.succ.castSucc ≫
        α i.castSucc (i.castSucc_le_succ.trans hi) =
      stdSimplex.δ i.succ.castSucc ≫ α i.succ hi) :
    ∃ (φ : (filtration j : SSet.{u}) ⟶ X),
      ∀ (i : Fin (p + 1)) (hi : i ≤ j), ι hi ≫ φ = α i hi := by
  revert α hα
  induction j using Fin.induction with
  | zero =>
    intro α hα
    refine ⟨(Subcomplex.eqToIso (filtration_zero.{u} p)).hom ≫
      (Nonsingular.iso _ (nonDegenerateEquiv 0).property).inv ≫ α 0 (by rfl),
      fun i hi ↦ ?_⟩
    obtain rfl : i = 0 := le_antisymm hi bot_le
    trans 𝟙 _ ≫ α 0 (by rfl)
    · rw [← Category.assoc, ← Category.assoc]
      congr 1
      simp only [← cancel_mono (Nonsingular.iso _ (nonDegenerateEquiv 0).property).hom,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
      rfl
    · simp
  | succ j hj  =>
    intro α hα
    obtain ⟨β, hβ⟩ := hj (fun i hi ↦ α i (hi.trans j.castSucc_le_succ)) (fun _ _ ↦ hα _ _)
    obtain ⟨φ, hφ₁, hφ₂⟩ := (isPushout j).exists_desc β (α j.succ (by rfl))
      (by rw [Category.assoc, hβ, hα])
    refine ⟨φ, fun i hi ↦ ?_⟩
    obtain hi | rfl := hi.lt_or_eq
    · rw [← Fin.le_castSucc_iff] at hi
      rw [← hβ i hi, ← hφ₁]
      rfl
    · exact hφ₂

/-- For `i : Fin (p + 1)`, this is the inclusion `Δ[p + 1] ⟶ Δ[p] ⊗ Δ[1]`
of the `i`th nondegenerate `(p + 1)`-simplex of `Δ[p] ⊗ Δ[1]` in
the enumeration `nonDegenerateEquiv`. -/
noncomputable def ι (i : Fin (p + 1)) : (Δ[p + 1] : SSet.{u}) ⟶ Δ[p] ⊗ Δ[1] :=
  yonedaEquiv.symm (nonDegenerateEquiv i)

lemma ι_def (i : Fin (p + 1)) :
    ι.{u} i = yonedaEquiv.symm (nonDegenerateEquiv i) := rfl

@[reassoc (attr := simp)]
lemma ι_fst (i : Fin (p + 1)) :
    ι.{u} i ≫ fst _ _ = stdSimplex.σ i := rfl

@[reassoc (attr := simp)]
lemma ι_snd (i : Fin (p + 1)) :
    ι.{u} i ≫ snd _ _ = yonedaEquiv.symm (stdSimplex.objMk₁ i.castSucc.succ) := rfl

@[simp]
lemma yonedaEquiv_ι (i : Fin (p + 1)) :
    dsimp% yonedaEquiv (ι.{u} i) = nonDegenerateEquiv i := rfl

instance (i : Fin (p + 1)) : Mono (ι.{u} i) := Nonsingular.mono _

set_option backward.isDefEq.respectTransparency false in
@[ext]
lemma hom_ext {X : SSet.{u}} {f g : Δ[p] ⊗ Δ[1] ⟶ X}
    (h : ∀ (i : Fin (p + 1)), ι i ≫ f = ι i ≫ g) :
    f = g := by
  ext ⟨⟨m⟩⟩ x
  have hx : x ∈ (⊤ : SSet.Subcomplex _).obj _ := by simp
  simp only [← filtration_last.{u} p, filtration, Subfunctor.iSup_obj,
    Set.mem_iUnion, Subtype.exists, exists_prop,
    Subcomplex.mem_ofSimplex_obj_iff] at hx
  obtain ⟨i, _, ⟨s, rfl⟩⟩ := hx
  apply ConcreteCategory.congr_hom (NatTrans.congr_app (h i) (op ⦋m⦌))

lemma exists_desc
    {X : SSet.{u}} (α : Fin (p + 1) → (Δ[p + 1] ⟶ X))
    (hα : ∀ (i : Fin p),
      stdSimplex.δ i.succ.castSucc ≫ α i.castSucc =
        stdSimplex.δ i.succ.castSucc ≫ α i.succ) :
    ∃ (φ : Δ[p] ⊗ Δ[1] ⟶ X),
      ∀ (i : Fin (p + 1)), ι i ≫ φ = α i := by
  obtain ⟨ψ, hψ⟩ := filtration.exists_desc (fun i hi ↦ α i) (fun i _ ↦ hα i)
  exact ⟨(Subcomplex.topIso _).inv ≫ (Subcomplex.eqToIso (filtration_last p)).inv ≫ ψ,
    fun i ↦ by rw [← hψ i (Fin.le_last i)]; rfl⟩

@[reassoc]
lemma δ_ι_zero :
    stdSimplex.{u}.δ 0 ≫ ι (0 : Fin (p + 1)) = ι₁ :=
  yonedaEquiv.injective rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma δ_ι_last :
    stdSimplex.{u}.δ (Fin.last (p + 1)) ≫ ι (Fin.last p) = ι₀ := by
  apply yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  apply Prod.ext
  · exact stdSimplex.objEquiv.injective SimplexCategory.δ_comp_σ_succ
  · dsimp
    rw [stdSimplex.δ_objMk₁_of_le _ _ (by simp)]
    simp only [Fin.succ_castSucc, Fin.castPred_castSucc]
    ext k
    rw [stdSimplex.objMk₁_of_castSucc_lt _ _ (by simp)]
    exact congr_arg Fin.val (SSet.ι₀_app_snd_apply.{u} (yonedaEquiv (𝟙 Δ[p])) k).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma ι_δ_whiskerRight_of_le (i : Fin (p + 2)) (j : Fin (p + 1))
    (hij : i ≤ j.castSucc := by grind) :
    ι.{u} j ≫ stdSimplex.δ i ▷ Δ[1] = stdSimplex.δ i.castSucc ≫ ι j.succ := by
  apply CartesianMonoidalCategory.hom_ext
  · calc
      (ι j ≫ stdSimplex.δ i ▷ Δ[1]) ≫ fst _ _ =
          ι j ≫ (stdSimplex.δ i ▷ Δ[1] ≫ fst _ _) := by
        rw [Category.assoc]
      _ = ι j ≫ fst _ _ ≫ stdSimplex.δ i := by
        rw [CartesianMonoidalCategory.whiskerRight_fst]
      _ = stdSimplex.σ j ≫ stdSimplex.δ i := by
        with_unfolding_all rfl
      _ = stdSimplex.δ i.castSucc ≫ stdSimplex.σ j.succ := by
        rw [← stdSimplex.δ_comp_σ_of_le hij]
      _ = stdSimplex.δ i.castSucc ≫ (ι j.succ ≫ fst _ _) := by
        with_unfolding_all rfl
      _ = (stdSimplex.δ i.castSucc ≫ ι j.succ) ≫ fst _ _ := by
        rw [← Category.assoc]
  · calc
      (ι j ≫ stdSimplex.δ i ▷ Δ[1]) ≫ snd _ _ =
          ι j ≫ (stdSimplex.δ i ▷ Δ[1] ≫ snd _ _) := by
        rw [Category.assoc]
      _ = ι j ≫ snd _ _ := by
        rw [CartesianMonoidalCategory.whiskerRight_snd]
      _ = yonedaEquiv.symm (stdSimplex.objMk₁.{u} (j.castSucc.succ)) := by
        rw [ι_snd]
      _ = yonedaEquiv.symm
          (Δ[1].δ i.castSucc (stdSimplex.objMk₁.{u} (j.succ).castSucc.succ)) := by
        congr 1
        have hlt : (i.castSucc.castSucc : Fin (p + 4)) < (j.succ).castSucc.succ := by
          grind
        calc
          stdSimplex.objMk₁.{u} (j.castSucc.succ)
              = stdSimplex.objMk₁
                (((j.succ).castSucc.succ).pred (Fin.ne_zero_of_lt hlt)) := by
                have hpred : (((j.succ).castSucc.succ).pred (Fin.ne_zero_of_lt hlt)) =
                    j.castSucc.succ := by
                  ext
                  grind
                rw [hpred]
          _ = Δ[1].δ i.castSucc (stdSimplex.objMk₁.{u} (j.succ).castSucc.succ) := by
                rw [← stdSimplex.δ_objMk₁_of_lt _ _ hlt]
      _ = stdSimplex.δ i.castSucc ≫ yonedaEquiv.symm
          (stdSimplex.objMk₁.{u} (j.succ).castSucc.succ) := by
        rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      _ = stdSimplex.δ i.castSucc ≫ (ι j.succ ≫ snd _ _) := by
        rw [ι_snd]
      _ = (stdSimplex.δ i.castSucc ≫ ι j.succ) ≫ snd _ _ := by
        rw [← Category.assoc]

@[reassoc]
lemma δ_ι_of_lt (i : Fin (p + 3)) (j : Fin (p + 2)) (hij : i < j.castSucc := by grind) :
    stdSimplex.{u}.δ i ≫ ι j = ι (j.pred (by grind)) ≫
      stdSimplex.δ (i.castPred (by grind)) ▷ Δ[1] := by
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by simpa using Fin.ne_zero_of_lt hij)
  obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hij)
  rw [Fin.pred_succ, Fin.castPred_castSucc, ι_δ_whiskerRight_of_le ..]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma ι_δ_whiskerRight_of_gt (i : Fin (p + 2)) (j : Fin (p + 1))
    (hij : j.castSucc < i := by grind) :
    ι.{u} j ≫ stdSimplex.δ i ▷ Δ[1] = stdSimplex.δ i.succ ≫ ι j.castSucc := by
  apply CartesianMonoidalCategory.hom_ext
  · calc
      (ι j ≫ stdSimplex.δ i ▷ Δ[1]) ≫ fst _ _ =
          ι j ≫ (stdSimplex.δ i ▷ Δ[1] ≫ fst _ _) := by
        rw [Category.assoc]
      _ = ι j ≫ fst _ _ ≫ stdSimplex.δ i := by
        rw [CartesianMonoidalCategory.whiskerRight_fst]
      _ = stdSimplex.σ j ≫ stdSimplex.δ i := by
        with_unfolding_all rfl
      _ = stdSimplex.δ i.succ ≫ stdSimplex.σ j.castSucc := by
        rw [← stdSimplex.δ_comp_σ_of_gt hij]
      _ = stdSimplex.δ i.succ ≫ (ι j.castSucc ≫ fst _ _) := by
        with_unfolding_all rfl
      _ = (stdSimplex.δ i.succ ≫ ι j.castSucc) ≫ fst _ _ := by
        rw [← Category.assoc]
  · calc
      (ι j ≫ stdSimplex.δ i ▷ Δ[1]) ≫ snd _ _ =
          ι j ≫ (stdSimplex.δ i ▷ Δ[1] ≫ snd _ _) := by
        rw [Category.assoc]
      _ = ι j ≫ snd _ _ := by
        rw [CartesianMonoidalCategory.whiskerRight_snd]
      _ = yonedaEquiv.symm (stdSimplex.objMk₁.{u} (j.castSucc.succ)) := by
        rw [ι_snd]
      _ = yonedaEquiv.symm
          (Δ[1].δ i.succ (stdSimplex.objMk₁.{u} ((j.castSucc).castSucc.succ))) := by
        congr 1
        have hle : ((j.castSucc).castSucc.succ : Fin (p + 4)) ≤ (i.succ).castSucc := by
          grind
        have hpred : ((j.castSucc).castSucc.succ : Fin (p + 4)).castPred
            (Fin.ne_last_of_lt (lt_of_le_of_lt hle (i.succ).castSucc_lt_succ)) =
            j.castSucc.succ := by
          ext
          simp
        calc
          stdSimplex.objMk₁.{u} (j.castSucc.succ)
              = stdSimplex.objMk₁
                (((j.castSucc).castSucc.succ : Fin (p + 4)).castPred
                  (Fin.ne_last_of_lt (lt_of_le_of_lt hle (i.succ).castSucc_lt_succ))) := by
                rw [hpred]
          _ = Δ[1].δ i.succ (stdSimplex.objMk₁.{u} ((j.castSucc).castSucc.succ)) := by
                rw [← stdSimplex.δ_objMk₁_of_le _ _ hle]
      _ = stdSimplex.δ i.succ ≫ yonedaEquiv.symm
          (stdSimplex.objMk₁.{u} ((j.castSucc).castSucc.succ)) := by
        rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      _ = stdSimplex.δ i.succ ≫ (ι j.castSucc ≫ snd _ _) := by
        rw [ι_snd]
      _ = (stdSimplex.δ i.succ ≫ ι j.castSucc) ≫ snd _ _ := by
        rw [← Category.assoc]

@[reassoc]
lemma δ_ι_of_gt (i : Fin (p + 3)) (j : Fin (p + 2)) (hij : j.succ < i := by grind) :
    stdSimplex.{u}.δ i ≫ ι j = ι (j.castPred (by grind)) ≫
      stdSimplex.δ (i.pred (by grind)) ▷ Δ[1] := by
  rw [ι_δ_whiskerRight_of_gt _ _
    (by rwa [← Fin.succ_lt_succ_iff, Fin.castSucc_castPred, Fin.succ_pred])]
  simp

@[reassoc]
lemma δ_succ_castSucc_ι_succ (i : Fin p) :
    stdSimplex.{u}.δ i.castSucc.succ ≫ prodStdSimplex₁.ι i.succ =
    stdSimplex.δ i.castSucc.succ ≫ prodStdSimplex₁.ι i.castSucc := by
  simp only [ι_def, stdSimplex.δ_comp_yonedaEquiv_symm]
  rw [Fin.succ_castSucc, δ_castSucc_nonDegenerateEquiv, ← Fin.succ_castSucc,
    δ_succ_nonDegenerateEquiv]

end prodStdSimplex₁

end SSet
