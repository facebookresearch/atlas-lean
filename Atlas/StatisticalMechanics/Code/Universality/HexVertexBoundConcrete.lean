/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Code.Universality.HexConcreteRegion

namespace StatMech.Universality

open Complex
open Function
open HexWalk
open scoped BigOperators













theorem hexVBC_vertexBound_false (a : ℂ) (h0 : ℤ) :
    ¬ (∀ W : HexWalk,
        (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
        ∀ x ∈ W.vertices,
          x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) := by
  intro hclosure
  set W : HexWalk := ⟨a, h0 + 1, []⟩ with hW
  have hmids : W.mids = [a] := by unfold HexWalk.mids; simp [hW]
  have hverts : W.vertices = [a + halfStep (h0 + 1)] := by
    unfold HexWalk.vertices; simp [hW]
  have hmem : ∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ) := by
    rw [hmids]; intro m hm; simp only [List.mem_singleton] at hm; rw [hm]; simp
  have hconc := hclosure W hmem (a + halfStep (h0 + 1)) (by rw [hverts]; simp)
  have heq : a + halfStep (h0 + 1) = a + (((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
    rw [hexConcrete_halfStep_add, hexConcrete_omega_cubic]; push_cast; ring
  rw [heq] at hconc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hconc
  have hs : halfStep h0 ≠ 0 := hexConcrete_halfStep_ne h0
  rcases hconc with h | h | h
  · rw [hexConcrete_v0_canon] at h
    exact hexConcrete_mid_ne a (halfStep h0) hs 1 1 1 0 (by norm_num) h
  · rw [hexConcrete_vq_canon] at h
    exact hexConcrete_mid_ne a (halfStep h0) hs 1 1 1 (-2) (by norm_num) h
  · rw [hexConcrete_vr_canon] at h
    exact hexConcrete_mid_ne a (halfStep h0) hs 1 1 3 2 (by norm_num) h










theorem hexVBC_vert_eq_mid_plus_step (m : ℂ) (h : ℤ) (ts : List ℤ) :
    ∀ x ∈ verticesAux m h ts, ∃ mm ∈ midsAux m h ts, ∃ hh : ℤ, x = mm + halfStep hh := by
  induction ts generalizing m h with
  | nil =>
    intro x hx
    simp only [verticesAux_nil, List.mem_singleton] at hx
    exact ⟨m, by simp, h, hx⟩
  | cons t ts ih =>
    intro x hx
    rw [verticesAux_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · exact ⟨m, by simp, h, hx⟩
    · obtain ⟨mm, hmm, hh, hxe⟩ := ih (m + halfStep h + halfStep (h + t)) (h + t) x hx
      exact ⟨mm, by rw [midsAux_cons, List.mem_cons]; exact Or.inr hmm, hh, hxe⟩



theorem hexVBC_halfStep_add6 (h : ℤ) : halfStep (h + 6) = halfStep h := by
  unfold halfStep
  rw [show (h + 6 : ℤ) = (h + 3) + 3 by ring, hexUnit_add_three, hexUnit_add_three]; ring


theorem hexVBC_step0 (h0 : ℤ) :
    halfStep (h0 + 0) = (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  push_cast; ring

theorem hexVBC_step1 (h0 : ℤ) :
    halfStep (h0 + 1) = (((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [hexConcrete_halfStep_add, hexConcrete_omega_cubic]; push_cast; ring

theorem hexVBC_step2 (h0 : ℤ) :
    halfStep (h0 + 2) = (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [hexConcrete_halfStep_add2]; push_cast; ring

theorem hexVBC_step3 (h0 : ℤ) :
    halfStep (h0 + 3) = (((-1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  unfold halfStep; rw [hexUnit_add_three]; push_cast; ring

theorem hexVBC_step4 (h0 : ℤ) :
    halfStep (h0 + 4) = (((-1 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  have h1 : halfStep (h0 + 1) = (((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * halfStep h0 :=
    hexVBC_step1 h0
  unfold halfStep at h1 ⊢
  rw [show (h0 + 4 : ℤ) = (h0 + 1) + 3 by ring, hexUnit_add_three]
  rw [show ((1 : ℂ) / 2) * -hexUnit (h0 + 1) = -((1 / 2) * hexUnit (h0 + 1)) by ring, h1]
  push_cast; ring

theorem hexVBC_step5 (h0 : ℤ) :
    halfStep (h0 + 5) = (((0 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  rw [show (h0 + 5 : ℤ) = (h0 - 1) + 6 by ring, hexVBC_halfStep_add6, hexConcrete_halfStep_sub]
  push_cast; ring





theorem hexVBC_halfStep_classify (h0 h : ℤ) :
    ∃ α β : ℝ, halfStep h = ((α : ℂ) + (β : ℂ) * hexOmega) * halfStep h0 ∧
      ((α, β) = ((1 : ℝ), (0 : ℝ)) ∨ (α, β) = (1, 1) ∨ (α, β) = (0, 1) ∨
       (α, β) = (-1, 0) ∨ (α, β) = (-1, -1) ∨ (α, β) = (0, -1)) := by
  set d := h - h0 with hd
  have hh : h = h0 + d := by rw [hd]; ring
  set r := d % 6 with hr
  have hrange : 0 ≤ r ∧ r < 6 :=
    ⟨Int.emod_nonneg d (by norm_num), Int.emod_lt_of_pos d (by norm_num)⟩
  have hdec : d = 6 * (d / 6) + r := by rw [hr]; omega
  have hper6 : ∀ (x : ℤ) (k : ℤ), halfStep (x + 6 * k) = halfStep x := by
    intro x k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
        rw [show x + 6 * ((n : ℤ) + 1) = (x + 6 * (n : ℤ)) + 6 by ring, hexVBC_halfStep_add6]
        exact ih
    | pred n ih =>
        have hstep : halfStep ((x + 6 * (-(n : ℤ) - 1)) + 6) = halfStep (x + 6 * (-(n : ℤ) - 1)) :=
          hexVBC_halfStep_add6 _
        rw [show (x + 6 * (-(n : ℤ) - 1)) + 6 = x + 6 * (-(n : ℤ)) by ring] at hstep
        rw [← hstep]; exact ih
  have hperiod : halfStep h = halfStep (h0 + r) := by
    rw [hh, hdec, show h0 + (6 * (d / 6) + r) = (h0 + r) + 6 * (d / 6) by ring, hper6]
  obtain ⟨hr0, hr6⟩ := hrange
  interval_cases r
  · exact ⟨1, 0, by rw [hperiod, hexVBC_step0], by tauto⟩
  · exact ⟨1, 1, by rw [hperiod, hexVBC_step1], by tauto⟩
  · exact ⟨0, 1, by rw [hperiod, hexVBC_step2], by tauto⟩
  · exact ⟨-1, 0, by rw [hperiod, hexVBC_step3], by tauto⟩
  · exact ⟨-1, -1, by rw [hperiod, hexVBC_step4], by tauto⟩
  · exact ⟨0, -1, by rw [hperiod, hexVBC_step5], by tauto⟩



noncomputable def hexVBC_star (m s : ℂ) : Finset ℂ :=
  { m + (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * s,
    m + (((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * s,
    m + (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * hexOmega) * s,
    m + (((-1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * s,
    m + (((-1 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * s,
    m + (((0 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * hexOmega) * s }



theorem hexVBC_star_mem (m s : ℂ) (α β : ℝ)
    (hin : (α, β) = ((1 : ℝ), (0 : ℝ)) ∨ (α, β) = (1, 1) ∨ (α, β) = (0, 1) ∨
       (α, β) = (-1, 0) ∨ (α, β) = (-1, -1) ∨ (α, β) = (0, -1)) :
    m + ((α : ℂ) + (β : ℂ) * hexOmega) * s ∈ hexVBC_star m s := by
  unfold hexVBC_star
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hin with h | h | h | h | h | h <;>
    (rw [Prod.ext_iff] at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; push_cast; tauto)




noncomputable def hexVBC_adjClosure (a : ℂ) (h0 : ℤ) : Finset ℂ :=
  hexVBC_star a (halfStep h0) ∪ hexVBC_star (hexConcreteQ a h0) (halfStep h0)
    ∪ hexVBC_star (hexConcreteR a h0) (halfStep h0)





theorem hexVBC_vertexBound (a : ℂ) (h0 : ℤ) (W : HexWalk)
    (hmids : ∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) :
    ∀ x ∈ W.vertices, x ∈ hexVBC_adjClosure a h0 := by
  intro x hx
  obtain ⟨mm, hmm, hh, hxe⟩ :=
    hexVBC_vert_eq_mid_plus_step W.startMid W.h0 W.turns x (by rw [← HexWalk.vertices]; exact hx)
  have hmmem : mm ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ) :=
    hmids mm (by rw [HexWalk.mids]; exact hmm)
  obtain ⟨α, β, hstep, hin⟩ := hexVBC_halfStep_classify h0 hh
  rw [hxe, hstep]
  unfold hexVBC_adjClosure
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmmem
  rcases hmmem with h | h | h <;> subst h
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hexVBC_star_mem _ _ α β hin))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hexVBC_star_mem _ _ α β hin))
  · exact Finset.mem_union_right _ (hexVBC_star_mem _ _ α β hin)







noncomputable def hexVBCRegion (a : ℂ) (h0 : ℤ) : HexFiniteRegion where
  verts := hexVBC_adjClosure a h0
  mids := {a, hexConcreteQ a h0, hexConcreteR a h0}
  start := a
  start_mem := by simp
  vertexBound := hexVBC_vertexBound a h0


theorem hexVBC_inRegion_iff (a : ℂ) (h0 : ℤ) (z : ℂ) :
    (hexVBCRegion a h0).inRegion z ↔ (z = a ∨ z = hexConcreteQ a h0 ∨ z = hexConcreteR a h0) := by
  unfold HexFiniteRegion.inRegion hexVBCRegion
  simp [Finset.mem_insert]










theorem hexVBC_region_stay_short (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hturns : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hstay : ∀ m ∈ (ofTurns a h0 ts).mids,
      m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) :
    ts.length ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  have hcon' : 2 ≤ ts.length := hcon
  match ts, hcon' with
  | t1 :: t2 :: rest, _ =>
    have ht1 : t1 = 1 ∨ t1 = -1 := hturns t1 (by simp)
    have ht2 : t2 = 1 ∨ t2 = -1 := hturns t2 (by simp)
    have hm2mem : (ofTurns a h0 [t1, t2]).endMid ∈ (ofTurns a h0 (t1 :: t2 :: rest)).mids := by
      rw [hexConcrete_endMid_two]
      show a + halfStep h0 + halfStep (h0 + t1) + halfStep (h0 + t1) + halfStep (h0 + t1 + t2)
        ∈ midsAux a h0 (t1 :: t2 :: rest)
      rw [midsAux_cons, midsAux_cons]
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      rw [show a + halfStep h0 + halfStep (h0 + t1) + halfStep (h0 + t1) + halfStep (h0 + t1 + t2)
          = (a + halfStep h0 + halfStep (h0 + t1)) + halfStep (h0 + t1) + halfStep (h0 + t1 + t2) by
        ring]
      cases rest with
      | nil => simp [midsAux]
      | cons s ss => rw [midsAux_cons]; exact List.mem_cons_self
    have hreg := hstay _ hm2mem
    obtain ⟨hna, hnq, hnr⟩ := hexConcrete_len2_endMid_not_mid a h0 t1 t2 ht1 ht2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hreg
    rcases hreg with h | h | h
    · exact hna h
    · exact hnq h
    · exact hnr h



theorem hexVBC_support_classify (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hstay : (ofTurns a h0 ts).StaysIn (hexVBCRegion a h0).inRegion) :
    ts = [] ∨ ts = [-1] ∨ ts = [1] := by
  have hstay' : ∀ m ∈ (ofTurns a h0 ts).mids,
      m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ) := by
    intro m hm
    have := hstay m hm
    rw [hexVBC_inRegion_iff] at this
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact this
  have hlen : ts.length ≤ 1 := hexVBC_region_stay_short a h0 ts hlegal.1 hstay'
  interval_cases hl : ts.length
  · exact Or.inl (List.length_eq_zero_iff.mp hl)
  · obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
      match ts, hl with
      | [t], _ => exact ⟨t, rfl⟩
    rcases hlegal.1 t (by simp) with rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)




theorem hexVBC_staysIn_p (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 []).StaysIn (hexVBCRegion a h0).inRegion := by
  intro m hm
  rw [hexVBC_inRegion_iff]
  have : (ofTurns a h0 []).mids = [a] := by
    show (trivialWalk a h0).mids = [a]; unfold HexWalk.mids; simp [trivialWalk]
  rw [this] at hm
  simp only [List.mem_singleton] at hm
  exact Or.inl hm


theorem hexVBC_staysIn_q (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [-1]).StaysIn (hexVBCRegion a h0).inRegion := by
  intro m hm
  rw [hexVBC_inRegion_iff, hexConcrete_mids_qext] at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)


theorem hexVBC_staysIn_r (a : ℂ) (h0 : ℤ) :
    (ofTurns a h0 [1]).StaysIn (hexVBCRegion a h0).inRegion := by
  intro m hm
  rw [hexVBC_inRegion_iff, hexConcrete_mids_rext] at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)




private theorem hexVBC_support_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0))) :
    (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn (hexVBCRegion a h0).inRegion :=
  (hexVBCRegion a h0).support_isLegalSAW_staysIn (hexConcreteDu_ne a h0) ts hsupp


theorem hexVBC_covering_p (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0)))
    (hp : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexConcreteDu a h0)) :
    ts = [] := by
  obtain ⟨hlegal, hstay⟩ := hexVBC_support_legal a h0 ts hsupp
  rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
  · exact h
  · exfalso; rw [h] at hp
    have hq := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hp hq; rw [hexConcrete_p_eq] at hp
    exact hexConcrete_a_ne_q a h0 (hp.symm.trans hq)
  · exfalso; rw [h] at hp
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hp hr; rw [hexConcrete_p_eq] at hp
    exact hexConcrete_a_ne_r a h0 (hp.symm.trans hr)


theorem hexVBC_covering_q (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0)))
    (hq : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0)) :
    ts = [-1] := by
  obtain ⟨hlegal, hstay⟩ := hexVBC_support_legal a h0 ts hsupp
  have hqdef : hexConcreteV a h0 + hexOmega * hexConcreteDu a h0 = hexConcreteQ a h0 := rfl
  rw [hqdef] at hq
  rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
  · exfalso; rw [h] at hq
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]; show (trivialWalk a h0).endMid = a; exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hq hpe
    exact hexConcrete_a_ne_q a h0 (hpe.symm.trans hq)
  · exact h
  · exfalso; rw [h] at hq
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hq hr
    exact hexConcrete_q_ne_r a h0 (hq.symm.trans hr)


theorem hexVBC_covering_r (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsupp : ts ∈ Function.support
      (combinedSummand (hexVBCRegion a h0).inRegion a h0 (hexConcreteV a h0) (hexConcreteDu a h0)))
    (hr : (ofTurns a h0 ts).EndsAt (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0)) :
    ts = [1] := by
  obtain ⟨hlegal, hstay⟩ := hexVBC_support_legal a h0 ts hsupp
  have hrdef : hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0 = hexConcreteR a h0 := rfl
  rw [hrdef] at hr
  rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
  · exfalso; rw [h] at hr
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]; show (trivialWalk a h0).endMid = a; exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hr hpe
    exact hexConcrete_a_ne_r a h0 (hpe.symm.trans hr)
  · exfalso; rw [h] at hr
    have hqe := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hr hqe
    exact hexConcrete_q_ne_r a h0 (hqe.symm.trans hr)
  · exact h



private theorem hexVBC_paraf_guard (a : ℂ) (h0 : ℤ) (z : ℂ) (ts : List ℤ)
    (hne : parafSummand (hexVBCRegion a h0).inRegion a h0 z (5/8) hexChi ts ≠ 0) :
    (ofTurns a h0 ts).IsLegalSAW
      ∧ (ofTurns a h0 ts).StaysIn (hexVBCRegion a h0).inRegion
      ∧ (ofTurns a h0 ts).EndsAt z := by
  by_contra hcon
  apply hne; unfold parafSummand; rw [if_neg hcon]


theorem hexVBC_summable (a : ℂ) (h0 : ℤ) (z : ℂ) :
    Summable fun ts => parafSummand (hexVBCRegion a h0).inRegion a h0 z (5/8) hexChi ts := by
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (s := {ts : List ℤ | ts = [] ∨ ts = [-1] ∨ ts = [1]})
  · have : {ts : List ℤ | ts = [] ∨ ts = [-1] ∨ ts = [1]} = ({[], [-1], [1]} : Finset (List ℤ)) := by
      ext ts; simp
    rw [this]; exact Finset.finite_toSet _
  · intro ts hts
    simp only [Function.mem_support] at hts
    obtain ⟨hlegal, hstay, _⟩ := hexVBC_paraf_guard a h0 z ts hts
    exact hexVBC_support_classify a h0 ts hlegal hstay


theorem hexVBC_obs_p (a : ℂ) (h0 : ℤ) :
    parafObservable (hexVBCRegion a h0).inRegion a h0
        (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi
      = parafSummand (hexVBCRegion a h0).inRegion a h0
        (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi [] := by
  unfold parafObservable
  apply tsum_eq_single
  intro ts hts
  by_contra hne
  obtain ⟨hlegal, hstay, hend⟩ := hexVBC_paraf_guard a h0 _ ts hne
  rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
  · exact hts h
  · rw [h] at hend
    have hq := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hend hq; rw [hexConcrete_p_eq] at hend
    exact hexConcrete_a_ne_q a h0 (hend.symm.trans hq)
  · rw [h] at hend
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hend hr; rw [hexConcrete_p_eq] at hend
    exact hexConcrete_a_ne_r a h0 (hend.symm.trans hr)


theorem hexVBC_obs_q (a : ℂ) (h0 : ℤ) :
    parafObservable (hexVBCRegion a h0).inRegion a h0
        (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi
      = parafSummand (hexVBCRegion a h0).inRegion a h0
        (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi [-1] := by
  unfold parafObservable
  apply tsum_eq_single
  intro ts hts
  by_contra hne
  obtain ⟨hlegal, hstay, hend⟩ := hexVBC_paraf_guard a h0 _ ts hne
  have hqdef : hexConcreteV a h0 + hexOmega * hexConcreteDu a h0 = hexConcreteQ a h0 := rfl
  rw [hqdef] at hend
  rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
  · rw [h] at hend
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]; show (trivialWalk a h0).endMid = a; exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hend hpe
    exact hexConcrete_a_ne_q a h0 (hpe.symm.trans hend)
  · exact hts h
  · rw [h] at hend
    have hr := hexConcrete_endsAt_r a h0
    rw [HexWalk.EndsAt] at hend hr
    exact hexConcrete_q_ne_r a h0 (hend.symm.trans hr)


theorem hexVBC_obs_r (a : ℂ) (h0 : ℤ) :
    parafObservable (hexVBCRegion a h0).inRegion a h0
        (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi
      = parafSummand (hexVBCRegion a h0).inRegion a h0
        (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi [1] := by
  unfold parafObservable
  apply tsum_eq_single
  intro ts hts
  by_contra hne
  obtain ⟨hlegal, hstay, hend⟩ := hexVBC_paraf_guard a h0 _ ts hne
  have hrdef : hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0 = hexConcreteR a h0 := rfl
  rw [hrdef] at hend
  rcases hexVBC_support_classify a h0 ts hlegal hstay with h | h | h
  · rw [h] at hend
    have hpe : (ofTurns a h0 []).EndsAt a := by
      rw [HexWalk.EndsAt]; show (trivialWalk a h0).endMid = a; exact trivialWalk_endMid a h0
    rw [HexWalk.EndsAt] at hend hpe
    exact hexConcrete_a_ne_r a h0 (hpe.symm.trans hend)
  · rw [h] at hend
    have hq := hexConcrete_endsAt_q a h0
    rw [HexWalk.EndsAt] at hend hq
    exact hexConcrete_q_ne_r a h0 (hq.symm.trans hend)
  · exact hts h











theorem hexVBC_vertex_relation_unconditional (a : ℂ) (h0 : ℤ) :
    ((hexConcreteV a h0 + hexConcreteDu a h0) - hexConcreteV a h0)
        * parafObservable (hexVBCRegion a h0).inRegion a h0
            (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi
      + ((hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) - hexConcreteV a h0)
          * parafObservable (hexVBCRegion a h0).inRegion a h0
              (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi
      + ((hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) - hexConcreteV a h0)
          * parafObservable (hexVBCRegion a h0).inRegion a h0
              (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi = 0 := by
  refine hexClass_vertex_relation_singleTriplet (hexVBCRegion a h0).inRegion a h0
    (hexConcreteV a h0) (hexConcreteDu a h0) [] (hexConcreteDu_ne a h0)
    (hexVBC_summable a h0 _) (hexVBC_summable a h0 _) (hexVBC_summable a h0 _)
    ⟨(hexConcrete_atoms a h0).1.1, hexVBC_staysIn_p a h0, (hexConcrete_atoms a h0).1.2⟩
    (by simpa using ⟨(hexConcrete_atoms a h0).2.1.1, hexVBC_staysIn_q a h0,
        (hexConcrete_atoms a h0).2.1.2⟩)
    (by simpa using ⟨(hexConcrete_atoms a h0).2.2.1.1, hexVBC_staysIn_r a h0,
        (hexConcrete_atoms a h0).2.2.1.2⟩)
    (by simpa using (hexConcrete_atoms a h0).2.2.2.1)
    (by simpa using (hexConcrete_atoms a h0).2.2.2.2)
    ?_ ?_ ?_ ?_
  · intro ts hts hp
    exact (hexVBC_covering_p a h0 ts hts hp).symm
  · intro ts hts hq
    have := hexVBC_covering_q a h0 ts hts (by simpa using hq)
    simpa using this.symm
  · intro ts hts hr
    have := hexVBC_covering_r a h0 ts hts (by simpa using hr)
    simpa using this.symm
  · rw [hexVBC_obs_p a h0, hexVBC_obs_q a h0, hexVBC_obs_r a h0]; simp

end StatMech.Universality
