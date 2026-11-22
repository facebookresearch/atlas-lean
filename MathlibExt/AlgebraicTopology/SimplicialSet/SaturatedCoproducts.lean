/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetCoproducts
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Coproduct closure from cobase change and transfinite composition

A morphism property of simplicial sets that consists of monomorphisms,
respects isomorphisms, and is stable under cobase change and transfinite
composition is stable under coproducts indexed in the same universe.

The proof well-orders the original family and replaces one source component
by its target at each successor. The union at a limit stage is the colimit;
coproduct disjointness identifies each successor as a pushout of the original
component map. The entire coproduct map is a transfinite composition of these
pushouts, after identifying its source with its image.

This supplies the coproduct closure implicit in the definition of saturated
classes in the appendix of Joyal–Tierney, *Quasi-categories vs Segal spaces*,
arXiv math/0607820v2, used in Lemma 3.7. Composition and retract stability
are unnecessary for this result.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MorphismProperty
open scoped Simplicial

universe u

namespace SSet.coproductClosure

variable {J : Type u} {A B : J → SSet.{u}}

private abbrev ord (J : Type u) : Ordinal := (Cardinal.mk J).ord

private noncomputable def indexEquiv (J : Type u) : (ord J).ToType ≃ J :=
  Nonempty.some (Cardinal.eq.mp (by simp [ord]))

private abbrev StageIndex (J : Type u) := (Order.succ (ord J)).ToType

private noncomputable local instance (J : Type u) : OrderBot (StageIndex J) :=
  WellFoundedLT.toOrderBot _

private noncomputable def indexSeg (J : Type u) :
    (ord J).ToType <i StageIndex J :=
  Classical.choice (Ordinal.type_lt_iff.mp (by
    simpa only [Ordinal.type_toType] using Order.lt_succ (ord J)))

private lemma indexSeg_top (J : Type u) :
    (indexSeg J).top = (⊤ : StageIndex J) := by
  apply (Ordinal.typein (· < · : StageIndex J → StageIndex J → Prop)).injective
  rw [Ordinal.typein_top, Ordinal.type_toType]
  change ord J = Ordinal.typein (α := StageIndex J) (· < ·)
    (Ordinal.enum (α := StageIndex J) (· < ·) ⟨ord J, _⟩)
  exact (Ordinal.typein_enum (· < · : StageIndex J → StageIndex J → Prop)
    (o := ord J) (by simpa only [Ordinal.type_toType] using Order.lt_succ (ord J))).symm

private noncomputable def position (j : J) : StageIndex J :=
  indexSeg J ((indexEquiv J).symm j)

private lemma position_injective : Function.Injective (position (J := J)) := by
  intro i j h
  exact (indexEquiv J).symm.injective ((indexSeg J).injective h)

private lemma exists_position_eq (β : StageIndex J) (hβ : ¬ IsMax β) :
    ∃ j : J, position j = β := by
  have hne : β ≠ ⊤ := by
    rintro rfl
    exact hβ isMax_top
  have hlt : β < (indexSeg J).top := by
    rw [indexSeg_top]
    exact lt_top_iff_ne_top.mpr hne
  obtain ⟨a, rfl⟩ := (indexSeg J).mem_range_of_rel_top hlt
  exact ⟨indexEquiv J a, by simp only [position, Equiv.symm_apply_apply]⟩

private noncomputable def targetRange (j : J) : (∐ B : SSet.{u}).Subcomplex :=
  Subcomplex.range (Sigma.ι B j)

private noncomputable def sourceRange (f : ∀ j, A j ⟶ B j) :
    (∐ B : SSet.{u}).Subcomplex :=
  Subcomplex.range (Limits.Sigma.map f)

private noncomputable def stage (f : ∀ j, A j ⟶ B j)
    (β : StageIndex J) : (∐ B : SSet.{u}).Subcomplex :=
  sourceRange f ⊔ ⨆ j : J, if position j < β then targetRange j else ⊥

private lemma sourceRange_le_targetRange (f : ∀ j, A j ⟶ B j) (j : J) :
    Subcomplex.range (Sigma.ι A j ≫ Limits.Sigma.map f) ≤ targetRange j := by
  rw [Limits.Sigma.ι_map, Subcomplex.range_comp]
  exact Subcomplex.image_le_range _ _

private lemma stage_mono (f : ∀ j, A j ⟶ B j) : Monotone (stage f) := by
  intro β γ hβγ
  apply sup_le_sup_left
  exact iSup_mono fun j => by
    by_cases hj : position j < β
    · simp only [hj, ite_true]
      rw [ite_eq_left (hj.trans_le hβγ)]
    · simp only [hj, ite_false, bot_le]

private lemma stage_bot (f : ∀ j, A j ⟶ B j) :
    stage f (⊥ : StageIndex J) = sourceRange f := by
  simp [stage]

private lemma position_lt_top (j : J) : position j < (⊤ : StageIndex J) := by
  simpa only [position, indexSeg_top] using
    (indexSeg J).lt_top ((indexEquiv J).symm j)

private lemma stage_succ (f : ∀ j, A j ⟶ B j) (j : J) :
    stage f (Order.succ (position j)) = stage f (position j) ⊔ targetRange j := by
  have hj : ¬ IsMax (position j) := not_isMax_of_lt (position_lt_top j)
  apply le_antisymm
  · apply sup_le
    · exact le_sup_of_le_left le_sup_left
    · apply iSup_le
      intro i
      by_cases hi : position i < Order.succ (position j)
      · rw [ite_eq_left hi]
        obtain hij | hij := lt_or_eq_of_le ((Order.lt_succ_iff_of_not_isMax hj).1 hi)
        · exact le_sup_of_le_left
            (le_sup_of_le_right (le_iSup_of_le i (by rw [ite_eq_left hij])))
        · obtain rfl := position_injective hij
          exact le_sup_right
      · rw [ite_eq_right hi]
        exact bot_le
  · apply sup_le
    · exact stage_mono f (Order.le_succ _)
    · apply le_sup_of_le_right
      apply le_iSup_of_le j
      rw [ite_eq_left (Order.lt_succ_of_not_isMax hj)]

private noncomputable def sourceComponent (f : ∀ j, A j ⟶ B j) (j : J) :
    (∐ B : SSet.{u}).Subcomplex :=
  Subcomplex.range (Sigma.ι A j ≫ Limits.Sigma.map f)

private lemma sourceComponent_le_sourceRange (f : ∀ j, A j ⟶ B j) (j : J) :
    sourceComponent f j ≤ sourceRange f := by
  rw [sourceComponent, Subcomplex.range_comp]
  exact Subcomplex.image_le_range _ _

private lemma sourceRange_inf_targetRange (f : ∀ j, A j ⟶ B j) (j : J) :
    sourceRange f ⊓ targetRange j = sourceComponent f j := by
  apply le_antisymm
  · intro n x hx
    obtain ⟨a, ha⟩ := hx.1
    obtain ⟨b, hb⟩ := hx.2
    let E := (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
    obtain ⟨z, hza, _⟩ := Types.exists_of_isPullback
      ((SSet.isPullback_sigma_ι_sigmaMap f j).map E) a b (ha.trans hb.symm)
    change (Sigma.ι A j).app n z = a at hza
    refine ⟨z, ?_⟩
    simpa only [NatTrans.comp_app, types_comp_apply, hza] using ha
  · exact le_inf (sourceComponent_le_sourceRange f j)
      (sourceRange_le_targetRange f j)

private lemma targetRange_inf_eq_bot (i j : J) (hij : i ≠ j) :
    targetRange (B := B) i ⊓ targetRange j = ⊥ := by
  apply le_antisymm _ bot_le
  intro n x hx
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = op ⦋k⦌ := ⟨n.unop.len, by simp⟩
  obtain ⟨a, ha⟩ := hx.1
  obtain ⟨b, hb⟩ := hx.2
  exact hij (SSet.eq_of_sigma_ι_app_eq (ha.trans hb.symm))

private lemma stage_inf_targetRange (f : ∀ j, A j ⟶ B j) (j : J) :
    stage f (position j) ⊓ targetRange j = sourceComponent f j := by
  apply le_antisymm
  · intro n x hx
    change (x ∈ (sourceRange f).obj n ∨
      x ∈ (⨆ i : J, if position i < position j then targetRange i else ⊥).obj n) ∧
      x ∈ (targetRange j).obj n at hx
    rcases hx.1 with hxsource | hxold
    · exact (sourceRange_inf_targetRange f j).le n ⟨hxsource, hx.2⟩
    · rw [Subfunctor.iSup_obj] at hxold
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxold
      by_cases hi : position i < position j
      · rw [ite_eq_left hi] at hxi
        have hij : i ≠ j := by
          rintro rfl
          exact lt_irrefl _ hi
        exact False.elim ((targetRange_inf_eq_bot (B := B) i j hij).le n ⟨hxi, hx.2⟩)
      · rw [ite_eq_right hi] at hxi
        exact False.elim hxi
  · exact le_inf ((sourceComponent_le_sourceRange f j).trans le_sup_left)
      (sourceRange_le_targetRange f j)

private noncomputable def sourceLift (f : ∀ j, A j ⟶ B j) (j : J) :
    A j ⟶ (stage f (position j) : SSet.{u}) :=
  Subcomplex.lift (Sigma.ι A j ≫ Limits.Sigma.map f)
    ((sourceComponent_le_sourceRange f j).trans le_sup_left)

private noncomputable def targetLift (f : ∀ j, A j ⟶ B j) (j : J) :
    B j ⟶ (stage f (Order.succ (position j)) : SSet.{u}) :=
  Subcomplex.lift (Sigma.ι B j) (by rw [stage_succ]; exact le_sup_right)

private theorem stageSuccessor_isPushout (f : ∀ j, A j ⟶ B j)
    (hfmono : ∀ j, Mono (f j)) (j : J) :
    IsPushout (sourceLift f j) (f j)
      (Subcomplex.homOfLE (stage_mono f (Order.le_succ (position j))))
      (targetLift f j) := by
  let : Mono (Sigma.ι B j) := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = op ⦋k⦌ := ⟨n.unop.len, by simp⟩
    exact SSet.injective_sigma_ι_app k j
  let : Mono (f j) := hfmono j
  let : Mono (Sigma.ι A j ≫ Limits.Sigma.map f) := by
    rw [Sigma.ι_map]
    infer_instance
  let qa : A j ⟶ (sourceComponent f j : SSet.{u}) :=
    Subcomplex.toRange (Sigma.ι A j ≫ Limits.Sigma.map f)
  let qb : B j ⟶ (targetRange j : SSet.{u}) := Subcomplex.toRange (Sigma.ι B j)
  let : IsIso qa := by
    dsimp only [qa, sourceComponent]
    infer_instance
  let : IsIso qb := by
    dsimp only [qb, targetRange]
    infer_instance
  let sq : Subcomplex.BicartSq (sourceComponent f j) (stage f (position j))
      (targetRange j) (stage f (Order.succ (position j))) :=
    { inf_eq := stage_inf_targetRange f j
      sup_eq := (stage_succ f j).symm }
  refine sq.isPushout.of_iso' (asIso qa) (Iso.refl _) (asIso qb) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · change qa ≫ Subcomplex.homOfLE sq.le₁₂ = sourceLift f j ≫ 𝟙 _
    rfl
  · change qa ≫ Subcomplex.homOfLE sq.le₁₃ = f j ≫ qb
    apply (cancel_mono (targetRange j).ι).mp
    change Sigma.ι A j ≫ Limits.Sigma.map f = f j ≫ Sigma.ι B j
    exact Sigma.ι_map f j
  · rfl
  · rfl

private lemma stage_top (f : ∀ j, A j ⟶ B j) :
    stage f (⊤ : StageIndex J) = ⊤ := by
  rw [stage]
  simp only [position_lt_top, ite_true]
  have h : (⨆ j : J, targetRange j) = (⊤ : (∐ B : SSet.{u}).Subcomplex) := by
    rw [← Subcomplex.range_eq_top (𝟙 (∐ B : SSet.{u})),
      SSet.range_eq_iSup_sigma_ι]
    simp [targetRange]
  rw [h]
  exact sup_eq_right.mpr le_top

private lemma iSup_stage_lt (f : ∀ j, A j ⟶ B j)
    (β : StageIndex J) (hβ : Order.IsSuccLimit β) :
    (⨆ γ : Set.Iio β, stage f γ.1) = stage f β := by
  apply le_antisymm
  · exact iSup_le fun γ => stage_mono f γ.2.le
  · apply sup_le
    · exact le_trans (le_sup_left : sourceRange f ≤ stage f ⊥)
        (le_iSup (fun γ : Set.Iio β => stage f γ.1) ⟨⊥, hβ.bot_lt⟩)
    · apply iSup_le
      intro j
      by_cases hj : position j < β
      · simp only [hj, ite_true]
        let γ : Set.Iio β := ⟨Order.succ (position j), (hβ.succ_lt_iff).2 hj⟩
        apply le_trans _ (le_iSup (fun γ : Set.Iio β => stage f γ.1) γ)
        apply le_sup_of_le_right
        apply le_iSup_of_le j
        rw [ite_eq_left (Order.lt_succ_of_not_isMax (not_isMax_of_lt hj))]
      · simp only [hj, ite_false]
        exact bot_le

private noncomputable def stageFunctor (f : ∀ j, A j ⟶ B j) :
    StageIndex J ⥤ SSet.{u} :=
  (stage_mono f).functor ⋙ Subcomplex.toSSetFunctor

private noncomputable local instance (f : ∀ j, A j ⟶ B j) :
    (stageFunctor f).IsWellOrderContinuous where
  nonempty_isColimit β hβ := ⟨by
    let G := (stage_mono f).functor
    have hLUB : IsLUB
        (Set.range ((Set.principalSegIio β).monotone.functor ⋙ G).obj)
        (stage f β) := by
      constructor
      · rintro _ ⟨γ, rfl⟩
        exact stage_mono f γ.2.le
      · intro Z hZ
        rw [← iSup_stage_lt f β hβ]
        exact iSup_le fun γ => hZ ⟨γ, rfl⟩
    have hsub : IsColimit ((Set.principalSegIio β).cocone G) :=
      Preorder.isColimitOfIsLUB _ _ hLUB
    exact isColimitOfPreserves Subcomplex.toSSetFunctor hsub⟩

private noncomputable def stageIncl (f : ∀ j, A j ⟶ B j) :
    stageFunctor f ⟶ (Functor.const _).obj (∐ B : SSet.{u}) where
  app β := (stage f β).ι
  naturality β γ h := by
    change Subcomplex.homOfLE (stage_mono f (leOfHom h)) ≫
      (stage f γ).ι = (stage f β).ι
    exact Subcomplex.homOfLE_ι (stage_mono f (leOfHom h))

private noncomputable def stageTopIso (f : ∀ j, A j ⟶ B j) :
    (stageFunctor f).obj (⊤ : StageIndex J) ≅ (∐ B : SSet.{u}) :=
  Subcomplex.eqToIso (stage_top f) ≪≫ Subcomplex.topIso _

private noncomputable def stageIsColimit (f : ∀ j, A j ⟶ B j) :
    IsColimit (Cocone.mk (∐ B : SSet.{u}) (stageIncl f)) := by
  apply IsColimit.ofIsoColimit
    (colimitOfDiagramTerminal (isTerminalTop : IsTerminal (⊤ : StageIndex J))
      (stageFunctor f))
  refine Cocone.ext (stageTopIso f) ?_
  intro β
  change Subcomplex.homOfLE (stage_mono f (leOfHom (isTerminalTop.from β))) ≫
    (stage f ⊤).ι = (stage f β).ι
  exact Subcomplex.homOfLE_ι _

private noncomputable def rangeInclusionTransfinite
    (P : MorphismProperty SSet.{u}) (f : ∀ j, A j ⟶ B j)
    (hsucc : ∀ (β : StageIndex J) (_ : ¬ IsMax β),
      P (Subcomplex.homOfLE (stage_mono f (Order.le_succ β)))) :
    P.TransfiniteCompositionOfShape (StageIndex J) (sourceRange f).ι where
  F := stageFunctor f
  isoBot := Subcomplex.eqToIso (stage_bot f)
  incl := stageIncl f
  isColimit := stageIsColimit f
  fac := by
    change Subcomplex.homOfLE (stage_bot f).symm.le ≫
      (stage f ⊥).ι = (sourceRange f).ι
    exact Subcomplex.homOfLE_ι (stage_bot f).symm.le
  map_mem β hβ := by
    change P (Subcomplex.homOfLE (stage_mono f (Order.le_succ β)))
    exact hsucc β hβ

private theorem sigmaMap_mem_of_stageSucc
    (P : MorphismProperty SSet.{u}) [P.RespectsIso]
    [P.IsStableUnderTransfiniteComposition.{u}]
    (f : ∀ j, A j ⟶ B j) (hfmono : ∀ j, Mono (f j))
    (hsucc : ∀ (β : StageIndex J) (_ : ¬ IsMax β),
      P (Subcomplex.homOfLE (stage_mono f (Order.le_succ β)))) :
    P (Limits.Sigma.map f) := by
  let : ∀ j, Mono (f j) := hfmono
  let : Mono (Limits.Sigma.map f) := SSet.mono_sigmaMap f hfmono
  let q : (∐ A : SSet.{u}) ⟶ (sourceRange f : SSet.{u}) :=
    Subcomplex.toRange (Limits.Sigma.map f)
  let : IsIso q := by
    dsimp only [q, sourceRange]
    infer_instance
  have hrange : P (sourceRange f).ι :=
    P.transfiniteCompositionsOfShape_le (StageIndex J) _
      ⟨rangeInclusionTransfinite P f hsucc⟩
  let e₀ : (∐ A : SSet.{u}) ≅ (sourceRange f : SSet.{u}) :=
    asIso q
  let e : Arrow.mk (Limits.Sigma.map f) ≅ Arrow.mk (sourceRange f).ι :=
    Arrow.isoMk e₀ (Iso.refl _) (by
      change q ≫ (sourceRange f).ι = Limits.Sigma.map f ≫ 𝟙 _
      rfl)
  exact (P.arrow_mk_iso_iff e).2 hrange

private theorem sigmaMap_mem
    (P : MorphismProperty SSet.{u}) [P.RespectsIso]
    [P.IsStableUnderCobaseChange] [P.IsStableUnderTransfiniteComposition.{u}]
    (f : ∀ j, A j ⟶ B j) (hfmono : ∀ j, Mono (f j)) (hf : ∀ j, P (f j)) :
    P (Limits.Sigma.map f) := by
  apply sigmaMap_mem_of_stageSucc P f hfmono
  intro β hβ
  obtain ⟨j, rfl⟩ := exists_position_eq β hβ
  exact P.of_isPushout (stageSuccessor_isPushout f hfmono j) (hf j)

end SSet.coproductClosure

/-- A property of monomorphisms of simplicial sets that respects isomorphisms
and is stable under cobase change and transfinite composition is stable under
coproducts indexed in the same universe. -/
theorem SSet.isStableUnderCoproducts_of_le_monomorphisms
    (P : MorphismProperty SSet.{u}) [P.RespectsIso]
    [P.IsStableUnderCobaseChange] [P.IsStableUnderTransfiniteComposition.{u}]
    (hP : P ≤ MorphismProperty.monomorphisms SSet.{u}) :
    P.IsStableUnderCoproducts.{u} where
  isStableUnderCoproductsOfShape J := by
    apply IsStableUnderCoproductsOfShape.mk
    intro A B _ _ f hf
    exact SSet.coproductClosure.sigmaMap_mem P f (fun j => hP (f j) (hf j)) hf

end
