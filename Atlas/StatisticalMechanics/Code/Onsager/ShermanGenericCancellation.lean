/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.ShermanListSeries
import Code.Onsager.ShermanReroot









namespace StatMech.Onsager

open Matrix BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

def ons_validRootedList (e r : E) (w : List E) : Prop :=
  w.head? = some e ∧ w.getLast? = some e ∧ ∀ x ∈ w, x ≠ r

def ons_validFactorList (e r : E) (ss : List (List E)) : Prop :=
  ∀ s ∈ ss, ons_isFirstReturnSegment e s ∧ ∀ x ∈ s, x ≠ r

private theorem mem_glue_of_mem_segment (e : E) (ss : List (List E))
    (hfirst : ∀ s ∈ ss, ons_isFirstReturnSegment e s)
    {s : List E} (hs : s ∈ ss) {x : E} (hx : x ∈ s) :
    x ∈ ons_glue e ss := by
  induction ss generalizing s x with
  | nil => simp at hs
  | cons t ts ih =>
      have ht := hfirst t (by simp)
      have hfirst' : ∀ u ∈ ts, ons_isFirstReturnSegment e u := by
        intro u hu
        exact hfirst u (by simp [hu])
      simp only [List.mem_cons] at hs
      rw [ons_glue_cons]
      rw [List.mem_append]
      rcases hs with hst | hs
      · rw [hst] at hx
        obtain ⟨interior, htform, _⟩ := ht
        have hdl : t.dropLast = e :: interior := by
          rw [htform, show e :: interior ++ [e] = (e :: interior) ++ [e] from rfl]
          exact List.dropLast_concat
        rw [hdl]
        rw [htform,
          show e :: interior ++ [e] = (e :: interior) ++ [e] from rfl,
          List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hxe
        · exact Or.inl hx
        · right
          rw [hxe]
          have hhead : ∀ u ∈ ts, u.head? = some e := by
            intro u hu
            exact ons_firstReturnSegment_head (hfirst' u hu)
          obtain ⟨tail, htail⟩ := ons_glue_head e ts hhead
          rw [htail]
          simp
      · exact Or.inr (ih hfirst' hs hx)

private theorem glue_getLast (e : E) (ss : List (List E)) :
    (ons_glue e ss).getLast? = some e := by
  induction ss with
  | nil => simp [ons_glue]
  | cons s ss ih =>
      rw [ons_glue_cons]
      have hne : ons_glue e ss ≠ [] := by
        intro h
        rw [h] at ih
        simp at ih
      rw [List.getLast?_append_of_ne_nil _ hne, ih]

private theorem avoids_glue (e r : E) (her : e ≠ r) (ss : List (List E))
    (hvalid : ons_validFactorList e r ss) :
    ∀ x ∈ ons_glue e ss, x ≠ r := by
  induction ss with
  | nil => simpa [ons_glue] using her
  | cons s ss ih =>
      rw [ons_glue_cons]
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hvalid s (by simp)).2 x (List.mem_of_mem_dropLast hx)
      · apply ih
        · intro t ht
          exact hvalid t (by simp [ht])
        · exact hx

private theorem firstReturnFactors_valid (e r : E) (w : List E)
    (hw : ons_validRootedList e r w) :
    ons_validFactorList e r (ons_firstReturnFactors e w) := by
  have hspec := ons_firstReturnFactors_spec e w hw.1 hw.2.1
  intro s hs
  refine ⟨hspec.2.1 s hs, ?_⟩
  intro x hx
  apply hw.2.2 x
  rw [← hspec.2.2]
  exact mem_glue_of_mem_segment e _ hspec.2.1 hs hx



def ons_rootedFactorEquiv (e r : E) (her : e ≠ r) :
    {w : List E // ons_validRootedList e r w} ≃
      {ss : List (List E) // ons_validFactorList e r ss} where
  toFun w := ⟨ons_firstReturnFactors e w.1,
    firstReturnFactors_valid e r w.1 w.2⟩
  invFun ss := ⟨ons_glue e ss.1, by
    have hfirst : ∀ s ∈ ss.1, ons_isFirstReturnSegment e s :=
      fun s hs => (ss.2 s hs).1
    have hhead : ∀ s ∈ ss.1, s.head? = some e :=
      fun s hs => ons_firstReturnSegment_head (hfirst s hs)
    have hlast : ∀ s ∈ ss.1, s.getLast? = some e :=
      fun s hs => ons_firstReturnSegment_last (hfirst s hs)
    refine ⟨?_, ?_, avoids_glue e r her ss.1 ss.2⟩
    · obtain ⟨tail, htail⟩ := ons_glue_head e ss.1 hhead
      rw [htail]
      simp
    · exact glue_getLast e ss.1⟩
  left_inv w := by
    apply Subtype.ext
    exact (ons_firstReturnFactors_spec e w.1 w.2.1 w.2.2.1).2.2
  right_inv ss := by
    apply Subtype.ext
    have hfirst : ∀ s ∈ ss.1, ons_isFirstReturnSegment e s :=
      fun s hs => (ss.2 s hs).1
    change ons_firstReturnFactors e (ons_glue e ss.1) = ss.1
    unfold ons_firstReturnFactors
    rw [ons_firstReturnSplit_glue e ss.1 hfirst]
    simp

noncomputable def ons_firstReturnWeight (Lambda : Matrix E E ℂ) (e r : E)
    (s : List E) : ℂ := by
  classical
  exact if ons_isFirstReturnSegment e s ∧ (∀ x ∈ s, x ≠ r) then
      ons_edgeWeight Lambda s
    else 0

private theorem listSeriesTerm_eq_zero_of_invalid (Lambda : Matrix E E ℂ) (e r : E)
    (ss : List (List E)) (hbad : ¬ ons_validFactorList e r ss) :
    ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) ss = 0 := by
  classical
  unfold ons_validFactorList at hbad
  push Not at hbad
  obtain ⟨s, hs, hsinvalid⟩ := hbad
  have hinvalid : ¬ (ons_isFirstReturnSegment e s ∧ ∀ x ∈ s, x ≠ r) := by
    rintro ⟨hfirst, havoid⟩
    obtain ⟨x, hx, hxr⟩ := hsinvalid hfirst
    exact havoid x hx hxr
  unfold ons_listSeriesTerm
  split_ifs with hempty
  · rfl
  · apply (div_eq_zero_iff).2
    left
    rw [List.prod_eq_zero_iff]
    exact List.mem_map.mpr ⟨s, hs, by simp [ons_firstReturnWeight, hinvalid]⟩

private theorem listSeriesTerm_valid (Lambda : Matrix E E ℂ) (e r : E)
    (ss : List (List E)) (hvalid : ons_validFactorList e r ss) :
    ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) ss =
      if ss = [] then 0 else
        (ss.map (ons_edgeWeight Lambda)).prod / (ss.length : ℂ) := by
  classical
  unfold ons_listSeriesTerm
  by_cases hempty : ss = []
  · simp [hempty]
  · rw [dif_neg hempty, if_neg hempty]
    congr 1
    have hprod : ∀ xs : List (List E), ons_validFactorList e r xs →
        (xs.map (ons_firstReturnWeight Lambda e r)).prod =
          (xs.map (ons_edgeWeight Lambda)).prod := by
      intro xs hxs
      induction xs with
      | nil => rfl
      | cons s xs ih =>
          rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
          have hsvalid := hxs s (by simp)
          rw [show ons_firstReturnWeight Lambda e r s = ons_edgeWeight Lambda s by
            simp only [ons_firstReturnWeight, if_pos hsvalid]]
          congr 1
          apply ih
          intro t ht
          exact hxs t (by simp [ht])
    exact hprod ss hvalid

noncomputable def ons_rootedListTerm (Lambda : Matrix E E ℂ) (e : E)
    (w : List E) : ℂ :=
  ons_edgeWeight Lambda w / ((ons_firstReturnFactors e w).length : ℂ)

private theorem rootedListTerm_glue (Lambda : Matrix E E ℂ) (e r : E)
    (ss : {ss : List (List E) // ons_validFactorList e r ss}) :
    ons_rootedListTerm Lambda e (ons_glue e ss.1) =
      ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) ss.1 := by
  have hfirst : ∀ s ∈ ss.1, ons_isFirstReturnSegment e s :=
    fun s hs => (ss.2 s hs).1
  have hhead : ∀ s ∈ ss.1, s.head? = some e :=
    fun s hs => ons_firstReturnSegment_head (hfirst s hs)
  have hlast : ∀ s ∈ ss.1, s.getLast? = some e :=
    fun s hs => ons_firstReturnSegment_last (hfirst s hs)
  unfold ons_rootedListTerm
  have hfactors : ons_firstReturnFactors e (ons_glue e ss.1) = ss.1 := by
    unfold ons_firstReturnFactors
    rw [ons_firstReturnSplit_glue e ss.1 hfirst]
    simp
  rw [hfactors, ons_edgeWeight_glue Lambda e ss.1 hhead hlast,
    listSeriesTerm_valid Lambda e r ss.1 ss.2]
  split_ifs with h
  · rw [h]
    simp
  · rfl



theorem ons_summable_rootedListTerm (Lambda : Matrix E E ℂ) (e r : E)
    (her : e ≠ r)
    (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
    (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
    Summable fun w : {w : List E // ons_validRootedList e r w} =>
      ons_rootedListTerm Lambda e w.1 := by
  let eqv := ons_rootedFactorEquiv e r her
  have hall := ons_summable_listSeriesTerm
    (ons_firstReturnWeight Lambda e r) hsum hsmall
  have hfactor := hall.subtype (ons_validFactorList e r)
  have heqv : Summable fun w : {w : List E // ons_validRootedList e r w} =>
      ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) (eqv w).1 := by
    simpa only [Function.comp_apply] using (eqv.summable_iff.mpr hfactor)
  apply heqv.congr
  intro w
  have hinv := congrArg Subtype.val (eqv.left_inv w)
  change ons_glue e (eqv w).1 = w.1 at hinv
  rw [← hinv]
  exact (rootedListTerm_glue Lambda e r (eqv w)).symm


theorem ons_rootedListSeries_eq_geometric (Lambda : Matrix E E ℂ) (e r : E)
    (her : e ≠ r)
    (hsum : Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖)
    (hsmall : ∑' s, ‖ons_firstReturnWeight Lambda e r s‖ < 1) :
    (∑' w : {w : List E // ons_validRootedList e r w}, ons_rootedListTerm Lambda e w.1) =
      ∑' k : ℕ, (∑' s, ons_firstReturnWeight Lambda e r s) ^ (k + 1) / (k + 1) := by
  let eqv := ons_rootedFactorEquiv e r her
  calc
    (∑' w : {w : List E // ons_validRootedList e r w}, ons_rootedListTerm Lambda e w.1) =
        ∑' ss : {ss : List (List E) // ons_validFactorList e r ss},
          ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) ss.1 := by
            rw [← eqv.tsum_eq]
            apply tsum_congr
            intro w
            have hinv := congrArg Subtype.val (eqv.left_inv w)
            change ons_glue e (eqv w).1 = w.1 at hinv
            change ons_rootedListTerm Lambda e w.1 =
              ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) (eqv w).1
            rw [← hinv]
            exact rootedListTerm_glue Lambda e r (eqv w)
    _ = ∑' ss : List (List E),
          ons_listSeriesTerm (ons_firstReturnWeight Lambda e r) ss := by
            have hsub := tsum_subtype
              {ss : List (List E) | ons_validFactorList e r ss}
              (ons_listSeriesTerm (ons_firstReturnWeight Lambda e r))
            change (∑' ss : {ss : List (List E) // ons_validFactorList e r ss},
                ons_listSeriesTerm
              (ons_firstReturnWeight Lambda e r) ss.1) = _ at hsub
            rw [hsub]
            apply tsum_congr
            intro ss
            by_cases hvalid : ons_validFactorList e r ss
            · simp [Set.indicator, hvalid]
            · simp [Set.indicator, hvalid,
                listSeriesTerm_eq_zero_of_invalid Lambda e r ss hvalid]
    _ = _ := ons_tsum_listSeriesTerm _ hsum hsmall

end StatMech.Onsager
