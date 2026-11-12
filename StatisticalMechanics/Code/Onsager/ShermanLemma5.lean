/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.ShermanLoop


























namespace StatMech.Onsager

open Matrix BigOperators










theorem ons_sum_zero_of_sign_involution {E} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Fin n → E)) (g : (Fin n → E) → (Fin n → E))
    (hmaps : ∀ v ∈ S, g v ∈ S)
    (hsign : ∀ v ∈ S, ons_loopWeight Λ (g v) = - ons_loopWeight Λ v)
    (hinv : ∀ v ∈ S, g (g v) = v) (hne : ∀ v ∈ S, g v ≠ v) :
    ∑ v ∈ S, ons_loopWeight Λ v = 0 := by
  refine Finset.sum_involution (fun v _ => g v) ?_ ?_ ?_ ?_
  · 
    intro v hv
    rw [hsign v hv, add_neg_cancel]
  · 
    intro v hv _
    exact hne v hv
  · 
    intro v hv
    exact hmaps v hv
  · 
    intro v hv
    exact hinv v hv



noncomputable def ons_loopSetBoth {E} [Fintype E] [DecidableEq E] {n : ℕ}
    (a b : E) : Finset (Fin n → E) :=
  {v ∈ (Finset.univ : Finset (Fin n → E)) | (∃ i, v i = a) ∧ (∃ j, v j = b)}


theorem ons_mem_loopSetBoth {E} [Fintype E] [DecidableEq E] {n : ℕ}
    (a b : E) (v : Fin n → E) :
    v ∈ ons_loopSetBoth (n := n) a b ↔ (∃ i, v i = a) ∧ (∃ j, v j = b) := by
  unfold ons_loopSetBoth
  simp








theorem ons_lemma5_of_involution {E} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (g : (Fin n → E) → (Fin n → E))
    (hmaps : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e), g v ∈ ons_loopSetBoth (n := n) e (rev e))
    (hsign : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e),
      ons_loopWeight Λ (g v) = - ons_loopWeight Λ v)
    (hinv : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e), g (g v) = v)
    (hne : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e), g v ≠ v) :
    ∑ v ∈ ons_loopSetBoth (n := n) e (rev e), ons_loopWeight Λ v = 0 :=
  ons_sum_zero_of_sign_involution Λ (ons_loopSetBoth (n := n) e (rev e)) g hmaps hsign hinv hne














def ons_mir {n : ℕ} [NeZero n] (l m k : Fin n) : Fin n :=
  ⟨min (l.val + m.val - k.val) (n - 1), by have := NeZero.pos n; omega⟩


theorem ons_mir_val {n : ℕ} [NeZero n] {l m k : Fin n} (hlk : l ≤ k) (hkm : k ≤ m) :
    (ons_mir l m k).val = l.val + m.val - k.val := by
  have hml : m.val < n := m.isLt
  have hlk' : l.val ≤ k.val := hlk
  have hkm' : k.val ≤ m.val := hkm
  unfold ons_mir
  simp only []
  omega


theorem ons_mir_mem {n : ℕ} [NeZero n] {l m k : Fin n} (hlk : l ≤ k) (hkm : k ≤ m) :
    l ≤ ons_mir l m k ∧ ons_mir l m k ≤ m := by
  have hv := ons_mir_val hlk hkm
  have hlk' : l.val ≤ k.val := hlk
  have hkm' : k.val ≤ m.val := hkm
  constructor
  · show l.val ≤ (ons_mir l m k).val; omega
  · show (ons_mir l m k).val ≤ m.val; omega


theorem ons_mir_mir {n : ℕ} [NeZero n] {l m k : Fin n} (hlk : l ≤ k) (hkm : k ≤ m) :
    ons_mir l m (ons_mir l m k) = k := by
  obtain ⟨h1, h2⟩ := ons_mir_mem hlk hkm
  have hv := ons_mir_val hlk hkm
  have hv2 := ons_mir_val h1 h2
  have hlk' : l.val ≤ k.val := hlk
  have hkm' : k.val ≤ m.val := hkm
  have hkn : k.val < n := k.isLt
  apply Fin.ext
  rw [hv2, hv]
  omega


theorem ons_mir_l {n : ℕ} [NeZero n] {l m : Fin n} (hlm : l ≤ m) :
    ons_mir l m l = m := by
  have hv := ons_mir_val (le_refl l) hlm
  apply Fin.ext; rw [hv]; have : l.val ≤ m.val := hlm; omega


theorem ons_mir_m {n : ℕ} [NeZero n] {l m : Fin n} (hlm : l ≤ m) :
    ons_mir l m m = l := by
  have hv := ons_mir_val hlm (le_refl m)
  apply Fin.ext; rw [hv]; have : l.val ≤ m.val := hlm; omega




def ons_revSeg {E} {n : ℕ} [NeZero n] (rev : E → E) (l m : Fin n) (v : Fin n → E) :
    Fin n → E :=
  fun k => if l ≤ k ∧ k ≤ m then rev (v (ons_mir l m k)) else v k


theorem ons_revSeg_outside {E} {n : ℕ} [NeZero n] (rev : E → E) {l m : Fin n}
    (v : Fin n → E) {k : Fin n} (h : ¬ (l ≤ k ∧ k ≤ m)) :
    ons_revSeg rev l m v k = v k := by
  unfold ons_revSeg; rw [if_neg h]


theorem ons_revSeg_inside {E} {n : ℕ} [NeZero n] (rev : E → E) {l m : Fin n}
    (v : Fin n → E) {k : Fin n} (hlk : l ≤ k) (hkm : k ≤ m) :
    ons_revSeg rev l m v k = rev (v (ons_mir l m k)) := by
  unfold ons_revSeg; rw [if_pos ⟨hlk, hkm⟩]




theorem ons_revSeg_involutive {E} {n : ℕ} [NeZero n] {rev : E → E}
    (hrev : Function.Involutive rev) {l m : Fin n} (v : Fin n → E) :
    ons_revSeg rev l m (ons_revSeg rev l m v) = v := by
  funext k
  by_cases hk : l ≤ k ∧ k ≤ m
  · obtain ⟨hlk, hkm⟩ := hk
    rw [ons_revSeg_inside rev _ hlk hkm]
    obtain ⟨h1, h2⟩ := ons_mir_mem hlk hkm
    rw [ons_revSeg_inside rev _ h1 h2, ons_mir_mir hlk hkm, hrev]
  · rw [ons_revSeg_outside rev _ hk, ons_revSeg_outside rev _ hk]










noncomputable def ons_hitSet {E} [DecidableEq E] {n : ℕ} (e : E) (rev : E → E)
    (v : Fin n → E) : Finset (Fin n) :=
  {k | v k = e ∨ v k = rev e}

theorem ons_mem_hitSet {E} [DecidableEq E] {n : ℕ} (e : E) (rev : E → E)
    (v : Fin n → E) (k : Fin n) :
    k ∈ ons_hitSet e rev v ↔ v k = e ∨ v k = rev e := by
  unfold ons_hitSet; simp



noncomputable def ons_l {E} [DecidableEq E] {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (v : Fin n → E) : Fin n :=
  if h : (ons_hitSet e rev v).Nonempty then (ons_hitSet e rev v).min' h else 0


noncomputable def ons_mSet {E} [DecidableEq E] {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (v : Fin n → E) : Finset (Fin n) :=
  {j | v j = rev (v (ons_l e rev v))}

theorem ons_mem_mSet {E} [DecidableEq E] {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (v : Fin n → E) (j : Fin n) :
    j ∈ ons_mSet e rev v ↔ v j = rev (v (ons_l e rev v)) := by
  unfold ons_mSet; simp



noncomputable def ons_m {E} [DecidableEq E] {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (v : Fin n → E) : Fin n :=
  if h : (ons_mSet e rev v).Nonempty then (ons_mSet e rev v).max' h else 0




noncomputable def ons_surgery {E} [DecidableEq E] {n : ℕ} [NeZero n] (e : E) (rev : E → E)
    (v : Fin n → E) : Fin n → E :=
  if (∃ i, v i = e) ∧ (∃ j, v j = rev e) then
    ons_revSeg rev (ons_l e rev v) (ons_m e rev v) v
  else v


theorem ons_hitSet_nonempty {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    {v : Fin n → E} (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    (ons_hitSet e rev v).Nonempty := by
  obtain ⟨⟨i, hi⟩, _⟩ := h
  exact ⟨i, (ons_mem_hitSet e rev v i).2 (Or.inl hi)⟩


theorem ons_l_eq {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    {v : Fin n → E} (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    ons_l e rev v = (ons_hitSet e rev v).min' (ons_hitSet_nonempty h) := by
  unfold ons_l; rw [dif_pos (ons_hitSet_nonempty h)]


theorem ons_v_l_mem {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    {v : Fin n → E} (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    v (ons_l e rev v) = e ∨ v (ons_l e rev v) = rev e := by
  rw [ons_l_eq h]
  exact (ons_mem_hitSet e rev v _).1 (Finset.min'_mem _ _)



theorem ons_mSet_nonempty {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    (hrev : Function.Involutive rev) {v : Fin n → E}
    (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    (ons_mSet e rev v).Nonempty := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
  rcases ons_v_l_mem ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ with hl | hl
  · 
    refine ⟨j, (ons_mem_mSet e rev v j).2 ?_⟩
    rw [hl, hj]
  · 
    refine ⟨i, (ons_mem_mSet e rev v i).2 ?_⟩
    rw [hl, hrev, hi]


theorem ons_m_eq {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    (hrev : Function.Involutive rev) {v : Fin n → E}
    (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    ons_m e rev v = (ons_mSet e rev v).max' (ons_mSet_nonempty hrev h) := by
  unfold ons_m; rw [dif_pos (ons_mSet_nonempty hrev h)]


theorem ons_v_m {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    (hrev : Function.Involutive rev) {v : Fin n → E}
    (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    v (ons_m e rev v) = rev (v (ons_l e rev v)) := by
  rw [ons_m_eq hrev h]
  exact (ons_mem_mSet e rev v _).1 (Finset.max'_mem _ _)



theorem ons_l_le_m {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    (hrev : Function.Involutive rev) {v : Fin n → E}
    (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    ons_l e rev v ≤ ons_m e rev v := by
  
  
  
  rw [ons_l_eq h, ons_m_eq hrev h]
  
  
  have hsub : ons_mSet e rev v ⊆ ons_hitSet e rev v := by
    intro j hj
    rw [ons_mem_mSet] at hj
    rw [ons_mem_hitSet]
    rcases ons_v_l_mem h with hl | hl
    · right; rw [hj, hl]
    · left; rw [hj, hl, hrev]
  have hmem : (ons_mSet e rev v).max' (ons_mSet_nonempty hrev h) ∈ ons_hitSet e rev v :=
    hsub (Finset.max'_mem _ _)
  exact Finset.min'_le _ _ hmem


theorem ons_surgery_eq_revSeg {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    {v : Fin n → E} (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    ons_surgery e rev v = ons_revSeg rev (ons_l e rev v) (ons_m e rev v) v := by
  unfold ons_surgery; rw [if_pos h]



theorem ons_surgery_hits_iff {E} [DecidableEq E] {n : ℕ} [NeZero n]
    {e : E} {rev : E → E}
    (S : Finset E) (hS : ∀ x, rev x ∈ S ↔ x ∈ S)
    {v : Fin n → E}
    (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    (∃ k, ons_surgery e rev v k ∈ S) ↔ ∃ k, v k ∈ S := by
  rw [ons_surgery_eq_revSeg h]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hin : ons_l e rev v ≤ k ∧ k ≤ ons_m e rev v
    · rw [ons_revSeg_inside rev v hin.1 hin.2] at hk
      exact ⟨ons_mir (ons_l e rev v) (ons_m e rev v) k,
        (hS _).mp hk⟩
    · rw [ons_revSeg_outside rev v hin] at hk
      exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    by_cases hin : ons_l e rev v ≤ k ∧ k ≤ ons_m e rev v
    · obtain ⟨hj1, hj2⟩ := ons_mir_mem hin.1 hin.2
      refine ⟨ons_mir (ons_l e rev v) (ons_m e rev v) k, ?_⟩
      rw [ons_revSeg_inside rev v hj1 hj2,
        ons_mir_mir hin.1 hin.2]
      exact (hS _).mpr hk
    · refine ⟨k, ?_⟩
      rwa [ons_revSeg_outside rev v hin]


theorem ons_surgery_l {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    (hrev : Function.Involutive rev) {v : Fin n → E}
    (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    ons_surgery e rev v (ons_l e rev v) = v (ons_l e rev v) := by
  rw [ons_surgery_eq_revSeg h]
  have hlm := ons_l_le_m hrev h
  rw [ons_revSeg_inside rev _ (le_refl _) hlm, ons_mir_l hlm, ons_v_m hrev h, hrev]


theorem ons_surgery_m {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    (hrev : Function.Involutive rev) {v : Fin n → E}
    (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    ons_surgery e rev v (ons_m e rev v) = v (ons_m e rev v) := by
  rw [ons_surgery_eq_revSeg h]
  have hlm := ons_l_le_m hrev h
  rw [ons_revSeg_inside rev _ hlm (le_refl _), ons_mir_m hlm, ons_v_m hrev h]


theorem ons_surgery_visitsBoth {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    (hrev : Function.Involutive rev) (hrne : rev e ≠ e) {v : Fin n → E}
    (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    (∃ i, ons_surgery e rev v i = e) ∧ (∃ j, ons_surgery e rev v j = rev e) := by
  have hl := ons_surgery_l hrev h
  have hm := ons_surgery_m hrev h
  have hvm := ons_v_m hrev h
  rcases ons_v_l_mem h with hvl | hvl
  · refine ⟨⟨ons_l e rev v, ?_⟩, ⟨ons_m e rev v, ?_⟩⟩
    · rw [hl, hvl]
    · rw [hm, hvm, hvl]
  · refine ⟨⟨ons_m e rev v, ?_⟩, ⟨ons_l e rev v, ?_⟩⟩
    · rw [hm, hvm, hvl, hrev]
    · rw [hl, hvl]




theorem ons_l_surgery {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    (hrev : Function.Involutive rev) (hrne : rev e ≠ e) {v : Fin n → E}
    (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    ons_l e rev (ons_surgery e rev v) = ons_l e rev v := by
  have hwboth := ons_surgery_visitsBoth hrev hrne h
  have hwl : ons_surgery e rev v (ons_l e rev v) = v (ons_l e rev v) := ons_surgery_l hrev h
  have hlin : ons_l e rev v ∈ ons_hitSet e rev (ons_surgery e rev v) := by
    rw [ons_mem_hitSet, hwl]; exact ons_v_l_mem h
  have hlb : ∀ k ∈ ons_hitSet e rev (ons_surgery e rev v), ons_l e rev v ≤ k := by
    intro k hk
    by_contra hlt
    rw [not_le] at hlt
    have hout : ¬ (ons_l e rev v ≤ k ∧ k ≤ ons_m e rev v) := by
      rintro ⟨hlk, _⟩; exact absurd hlk (not_le.2 hlt)
    have hwk : ons_surgery e rev v k = v k := by
      rw [ons_surgery_eq_revSeg h]; exact ons_revSeg_outside rev v hout
    rw [ons_mem_hitSet, hwk] at hk
    have hkv : k ∈ ons_hitSet e rev v := (ons_mem_hitSet e rev v k).2 hk
    have hle : ons_l e rev v ≤ k := by
      rw [ons_l_eq h]; exact Finset.min'_le _ _ hkv
    exact absurd hle (not_le.2 hlt)
  rw [ons_l_eq hwboth]
  exact le_antisymm (Finset.min'_le _ _ hlin) (Finset.le_min' _ _ _ hlb)




theorem ons_m_surgery {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    (hrev : Function.Involutive rev) (hrne : rev e ≠ e) {v : Fin n → E}
    (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    ons_m e rev (ons_surgery e rev v) = ons_m e rev v := by
  have hwboth := ons_surgery_visitsBoth hrev hrne h
  have hlpres := ons_l_surgery hrev hrne h
  have hwl : ons_surgery e rev v (ons_l e rev v) = v (ons_l e rev v) := ons_surgery_l hrev h
  have hwm : ons_surgery e rev v (ons_m e rev v) = v (ons_m e rev v) := ons_surgery_m hrev h
  have hvm : v (ons_m e rev v) = rev (v (ons_l e rev v)) := ons_v_m hrev h
  have hmin : ons_m e rev v ∈ ons_mSet e rev (ons_surgery e rev v) := by
    rw [ons_mem_mSet, hlpres, hwl, hwm, hvm]
  have hub : ∀ j ∈ ons_mSet e rev (ons_surgery e rev v), j ≤ ons_m e rev v := by
    intro j hj
    rw [ons_mem_mSet, hlpres, hwl] at hj
    by_contra hgt
    rw [not_le] at hgt
    have hout : ¬ (ons_l e rev v ≤ j ∧ j ≤ ons_m e rev v) := by
      rintro ⟨_, hjm⟩; exact absurd hjm (not_le.2 hgt)
    have hwj : ons_surgery e rev v j = v j := by
      rw [ons_surgery_eq_revSeg h]; exact ons_revSeg_outside rev v hout
    rw [hwj] at hj
    have hjv : j ∈ ons_mSet e rev v := (ons_mem_mSet e rev v j).2 hj
    have hle : j ≤ ons_m e rev v := by
      rw [ons_m_eq hrev h]; exact Finset.le_max' _ _ hjv
    exact absurd hle (not_le.2 hgt)
  rw [ons_m_eq hrev hwboth]
  exact le_antisymm (Finset.max'_le _ _ _ hub) (Finset.le_max' _ _ hmin)





theorem ons_surgery_involutive {E} [DecidableEq E] {n : ℕ} [NeZero n] {e : E} {rev : E → E}
    (hrev : Function.Involutive rev) (hrne : rev e ≠ e) {v : Fin n → E}
    (h : (∃ i, v i = e) ∧ (∃ j, v j = rev e)) :
    ons_surgery e rev (ons_surgery e rev v) = v := by
  have hwboth := ons_surgery_visitsBoth hrev hrne h
  rw [ons_surgery_eq_revSeg hwboth, ons_l_surgery hrev hrne h, ons_m_surgery hrev hrne h,
    ons_surgery_eq_revSeg h]
  exact ons_revSeg_involutive hrev v







theorem ons_sum_zero_of_sign_involution' {E} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Fin n → E)) (g : (Fin n → E) → (Fin n → E))
    (hmaps : ∀ v ∈ S, g v ∈ S)
    (hsign : ∀ v ∈ S, ons_loopWeight Λ (g v) = - ons_loopWeight Λ v)
    (hinv : ∀ v ∈ S, g (g v) = v) :
    ∑ v ∈ S, ons_loopWeight Λ v = 0 := by
  refine Finset.sum_involution (fun v _ => g v) ?_ ?_ ?_ ?_
  · intro v hv; rw [hsign v hv, add_neg_cancel]
  · intro v hv hfv hcontra
    apply hfv
    have hc : g v = v := hcontra
    have hsgn := hsign v hv
    rw [hc] at hsgn
    linear_combination hsgn / 2
  · intro v hv; exact hmaps v hv
  · intro v hv; exact hinv v hv









theorem ons_lemma5 {E} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (e : E) (rev : E → E) (hrev : Function.Involutive rev)
    (hrne : rev e ≠ e)
    (hsign : ∀ v ∈ ons_loopSetBoth (n := n) e (rev e),
      ons_loopWeight Λ (ons_surgery e rev v) = - ons_loopWeight Λ v) :
    ∑ v ∈ ons_loopSetBoth (n := n) e (rev e), ons_loopWeight Λ v = 0 := by
  refine ons_sum_zero_of_sign_involution' Λ _ (ons_surgery e rev) ?_ hsign ?_
  · intro v hv
    rw [ons_mem_loopSetBoth] at hv ⊢
    exact ons_surgery_visitsBoth hrev hrne hv
  · intro v hv
    rw [ons_mem_loopSetBoth] at hv
    exact ons_surgery_involutive hrev hrne hv

end StatMech.Onsager
