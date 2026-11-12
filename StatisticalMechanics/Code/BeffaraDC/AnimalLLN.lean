/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib

namespace StatMech

namespace BeffaraDC

open Finset Filter Topology
open scoped Topology

variable {V : Type*} [DecidableEq V] [Fintype V]















noncomputable def animalsLE (o : V) (n : ℕ) : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter (fun S => o ∈ S ∧ S.card ≤ n)


lemma mem_animalsLE {o : V} {n : ℕ} {S : Finset V} :
    S ∈ animalsLE o n ↔ o ∈ S ∧ S.card ≤ n := by
  simp [animalsLE]



lemma animalsLE_nonempty (o : V) {n : ℕ} (hn : 1 ≤ n) : (animalsLE o n).Nonempty :=
  ⟨{o}, by rw [mem_animalsLE]; exact ⟨mem_singleton_self o, by simpa using hn⟩⟩



lemma animalsLE_mono (o : V) {m n : ℕ} (h : m ≤ n) : animalsLE o m ⊆ animalsLE o n := by
  intro S hS
  rw [mem_animalsLE] at hS ⊢
  exact ⟨hS.1, hS.2.trans h⟩












noncomputable def greedyAnimalValue (w : V → ℝ) (o : V) (n : ℕ) : ℝ :=
  if h : (animalsLE o n).Nonempty then
    (animalsLE o n).sup' h (fun S => ∑ v ∈ S, w v)
  else 0



lemma greedyAnimalValue_eq_sum (w : V → ℝ) (o : V) {n : ℕ} (hn : 1 ≤ n) :
    ∃ S ∈ animalsLE o n, greedyAnimalValue w o n = ∑ v ∈ S, w v := by
  rw [greedyAnimalValue, dif_pos (animalsLE_nonempty o hn)]
  obtain ⟨S, hS, hSeq⟩ :=
    Finset.exists_mem_eq_sup' (animalsLE_nonempty o hn) (fun S => ∑ v ∈ S, w v)
  exact ⟨S, hS, hSeq⟩



lemma greedyAnimalValue_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (o : V) (n : ℕ) :
    0 ≤ greedyAnimalValue w o n := by
  rw [greedyAnimalValue]
  split
  · rename_i h
    obtain ⟨S, _, hSeq⟩ := Finset.exists_mem_eq_sup' h (fun S => ∑ v ∈ S, w v)
    rw [hSeq]
    exact Finset.sum_nonneg (fun v _ => hw v)
  · exact le_refl 0




lemma greedyAnimalValue_ge_root {w : V → ℝ} (o : V) {n : ℕ} (hn : 1 ≤ n) :
    w o ≤ greedyAnimalValue w o n := by
  rw [greedyAnimalValue, dif_pos (animalsLE_nonempty o hn)]
  have hmem : ({o} : Finset V) ∈ animalsLE o n := by
    rw [mem_animalsLE]; exact ⟨mem_singleton_self o, by simpa using hn⟩
  calc w o = ∑ v ∈ ({o} : Finset V), w v := by simp
    _ ≤ _ := Finset.le_sup' (fun S => ∑ v ∈ S, w v) hmem



lemma greedyAnimalValue_mono {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (o : V) {m n : ℕ}
    (hmn : m ≤ n) : greedyAnimalValue w o m ≤ greedyAnimalValue w o n := by
  rw [greedyAnimalValue]
  split
  · rename_i hm
    refine Finset.sup'_le hm _ (fun S hS => ?_)
    rw [greedyAnimalValue, dif_pos (hm.mono (animalsLE_mono o hmn))]
    exact Finset.le_sup' (fun S => ∑ v ∈ S, w v) (animalsLE_mono o hmn hS)
  · exact greedyAnimalValue_nonneg hw o n













lemma greedyAnimalValue_le_card_mul {w : V → ℝ} {M : ℝ} (hM : ∀ v, w v ≤ M)
    (hM0 : 0 ≤ M) (o : V) (n : ℕ) : greedyAnimalValue w o n ≤ M * n := by
  rw [greedyAnimalValue]
  split
  · rename_i h
    refine Finset.sup'_le h _ (fun S hS => ?_)
    rw [mem_animalsLE] at hS
    calc ∑ v ∈ S, w v ≤ ∑ _v ∈ S, M := Finset.sum_le_sum (fun v _ => hM v)
      _ = S.card * M := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * M := by gcongr; exact_mod_cast hS.2
      _ = M * n := by ring
  · positivity

















lemma greedyAnimalValue_split {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (o : V) (m n : ℕ)
    {S : Finset V} (hoS : o ∈ S) (hcard : S.card ≤ m + n + 1) :
    ∑ v ∈ S, w v ≤ greedyAnimalValue w o (m + 1) + greedyAnimalValue w o (n + 1) := by
  classical
  
  have hT : (S \ {o}).card ≤ m + n := by
    rw [card_sdiff_of_subset (by simpa using hoS), card_singleton]
    have : 1 ≤ S.card := card_pos.2 ⟨o, hoS⟩
    omega
  
  obtain ⟨P, hPsub, hPcard⟩ : ∃ P ⊆ S \ {o}, P.card = min m (S \ {o}).card :=
    Finset.exists_subset_card_eq (min_le_right _ _)
  set Q := (S \ {o}) \ P with hQ
  have hPQ : P ∪ Q = S \ {o} := by rw [hQ]; exact Finset.union_sdiff_of_subset hPsub
  have hdisj : Disjoint P Q := by rw [hQ]; exact Finset.disjoint_sdiff
  set A := insert o P with hA
  set B := insert o Q with hB
  have hoP : o ∉ P := fun h => by have := hPsub h; simp at this
  have hoQ : o ∉ Q := fun h => by
    rw [hQ] at h; have := (Finset.mem_sdiff.1 h).1; simp at this
  
  have hPm : P.card ≤ m := by rw [hPcard]; exact min_le_left _ _
  have hAcard : A.card ≤ m + 1 := by rw [hA, card_insert_of_notMem hoP]; omega
  have hQcard : Q.card ≤ n := by
    have hq : Q.card = (S \ {o}).card - P.card := by rw [hQ, card_sdiff_of_subset hPsub]
    rw [hq, hPcard]; omega
  have hBcard : B.card ≤ n + 1 := by rw [hB, card_insert_of_notMem hoQ]; omega
  
  have hsumS : ∑ v ∈ S, w v = w o + ∑ v ∈ S \ {o}, w v := by
    rw [← Finset.sum_insert (by simp), Finset.insert_eq,
        Finset.union_sdiff_of_subset (by simpa using hoS)]
  have hsumPQ : ∑ v ∈ S \ {o}, w v = ∑ v ∈ P, w v + ∑ v ∈ Q, w v := by
    rw [← hPQ, Finset.sum_union hdisj]
  have hsumA : ∑ v ∈ A, w v = w o + ∑ v ∈ P, w v := by rw [hA, Finset.sum_insert hoP]
  have hsumB : ∑ v ∈ B, w v = w o + ∑ v ∈ Q, w v := by rw [hB, Finset.sum_insert hoQ]
  
  have hAanimal : A ∈ animalsLE o (m + 1) := by
    rw [mem_animalsLE]; exact ⟨by rw [hA]; exact mem_insert_self _ _, hAcard⟩
  have hBanimal : B ∈ animalsLE o (n + 1) := by
    rw [mem_animalsLE]; exact ⟨by rw [hB]; exact mem_insert_self _ _, hBcard⟩
  have hgA : ∑ v ∈ A, w v ≤ greedyAnimalValue w o (m + 1) := by
    rw [greedyAnimalValue, dif_pos (animalsLE_nonempty o (by omega))]
    exact Finset.le_sup' (fun S => ∑ v ∈ S, w v) hAanimal
  have hgB : ∑ v ∈ B, w v ≤ greedyAnimalValue w o (n + 1) := by
    rw [greedyAnimalValue, dif_pos (animalsLE_nonempty o (by omega))]
    exact Finset.le_sup' (fun S => ∑ v ∈ S, w v) hBanimal
  calc ∑ v ∈ S, w v = w o + (∑ v ∈ P, w v + ∑ v ∈ Q, w v) := by rw [hsumS, hsumPQ]
    _ ≤ (w o + ∑ v ∈ P, w v) + (w o + ∑ v ∈ Q, w v) := by nlinarith [hw o]
    _ = ∑ v ∈ A, w v + ∑ v ∈ B, w v := by rw [hsumA, hsumB]
    _ ≤ greedyAnimalValue w o (m + 1) + greedyAnimalValue w o (n + 1) := by gcongr





lemma greedyAnimalValue_succ_subadditive {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (o : V) :
    Subadditive (fun n => greedyAnimalValue w o (n + 1)) := by
  intro m n
  simp only []
  obtain ⟨S, hS, hSeq⟩ := greedyAnimalValue_eq_sum w o (n := m + n + 1) (by omega)
  rw [show m + n + 1 = (m + n) + 1 from rfl] at hSeq
  rw [hSeq]
  rw [mem_animalsLE] at hS
  exact greedyAnimalValue_split hw o m n hS.1 hS.2










lemma greedyAnimalValue_bddBelow {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (o : V) :
    BddBelow (Set.range fun n => greedyAnimalValue w o (n + 1) / n) := by
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  exact div_nonneg (greedyAnimalValue_nonneg hw o _) (Nat.cast_nonneg n)







theorem greedyAnimalValue_lln {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (o : V) :
    Tendsto (fun n => greedyAnimalValue w o (n + 1) / n) atTop
      (𝓝 (greedyAnimalValue_succ_subadditive hw o).lim) :=
  (greedyAnimalValue_succ_subadditive hw o).tendsto_lim (greedyAnimalValue_bddBelow hw o)



theorem greedyAnimalValue_lln_eq_iInf {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (o : V) :
    (greedyAnimalValue_succ_subadditive hw o).lim
      = sInf ((fun n : ℕ => greedyAnimalValue w o (n + 1) / n) '' Set.Ici 1) := by
  rw [Subadditive.lim]



theorem greedyAnimalValue_lln_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (o : V) {n : ℕ}
    (hn : n ≠ 0) :
    (greedyAnimalValue_succ_subadditive hw o).lim ≤ greedyAnimalValue w o (n + 1) / n :=
  (greedyAnimalValue_succ_subadditive hw o).lim_le_div (greedyAnimalValue_bddBelow hw o) hn






theorem greedyAnimalValue_lln_le_bound {w : V → ℝ} {M : ℝ} (hw : ∀ v, 0 ≤ w v)
    (hM : ∀ v, w v ≤ M) (hM0 : 0 ≤ M) (o : V) :
    (greedyAnimalValue_succ_subadditive hw o).lim ≤ M := by
  
  set L := (greedyAnimalValue_succ_subadditive hw o).lim with hLdef
  
  have hcmp : Tendsto (fun n : ℕ => M * (n + 1) / n) atTop (𝓝 M) := by
    have h0 : Tendsto (fun n : ℕ => M * (1 + (n : ℝ)⁻¹)) atTop (𝓝 (M * (1 + 0))) :=
      Tendsto.const_mul _ (tendsto_const_nhds.add tendsto_inv_atTop_nhds_zero_nat)
    rw [show M * (1 + 0) = M from by ring] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  
  refine ge_of_tendsto hcmp ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : L ≤ greedyAnimalValue w o (n + 1) / n := greedyAnimalValue_lln_le hw o hn.ne'
  refine hL.trans ?_
  have hbd : greedyAnimalValue w o (n + 1) ≤ M * ((n : ℝ) + 1) := by
    have := greedyAnimalValue_le_card_mul hM hM0 o (n + 1)
    push_cast at this
    linarith
  exact (div_le_div_iff_of_pos_right hn').mpr hbd














noncomputable def subGreedyAnimalValue (𝒜 : ℕ → Finset (Finset V)) (w : V → ℝ) (n : ℕ) :
    ℝ :=
  if h : (𝒜 n).Nonempty then (𝒜 n).sup' h (fun S => ∑ v ∈ S, w v) else 0






theorem subGreedyAnimalValue_le {𝒜 : ℕ → Finset (Finset V)} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (o : V) (hsub : ∀ n, 𝒜 n ⊆ animalsLE o n) (n : ℕ) :
    subGreedyAnimalValue 𝒜 w n ≤ greedyAnimalValue w o n := by
  rw [subGreedyAnimalValue]
  split
  · rename_i h
    refine Finset.sup'_le h _ (fun S hS => ?_)
    rw [greedyAnimalValue, dif_pos (h.mono (hsub n))]
    exact Finset.le_sup' (fun S => ∑ v ∈ S, w v) (hsub n hS)
  · exact greedyAnimalValue_nonneg hw o n





theorem subGreedyAnimalValue_le_card_mul {𝒜 : ℕ → Finset (Finset V)} {w : V → ℝ}
    {M : ℝ} (hw : ∀ v, 0 ≤ w v) (hM : ∀ v, w v ≤ M) (hM0 : 0 ≤ M) (o : V)
    (hsub : ∀ n, 𝒜 n ⊆ animalsLE o n) (n : ℕ) :
    subGreedyAnimalValue 𝒜 w n ≤ M * n :=
  (subGreedyAnimalValue_le hw o hsub n).trans (greedyAnimalValue_le_card_mul hM hM0 o n)

end BeffaraDC

end StatMech
