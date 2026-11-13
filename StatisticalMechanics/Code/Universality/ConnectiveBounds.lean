/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































import Mathlib
import Code.Universality.SAW

namespace StatMech.Universality

open Filter Topology Finset
open scoped Topology
open Classical










abbrev ZdSite (d : ℕ) : Type := Fin d → ℤ



abbrev ZdStep (d : ℕ) : Type := Fin d × Bool



def zdStepVec {d : ℕ} (s : ZdStep d) : ZdSite d :=
  fun j => if j = s.1 then (if s.2 then 1 else -1) else 0


def zdReverse {d : ℕ} (s : ZdStep d) : ZdStep d := (s.1, !s.2)



def zdStepN {d n : ℕ} (w : Fin n → ZdStep d) (i : ℕ) : ZdSite d :=
  if h : i < n then zdStepVec (w ⟨i, h⟩) else 0



def zdPos {d n : ℕ} (w : Fin n → ZdStep d) (k : ℕ) : ZdSite d :=
  ∑ i ∈ Finset.range k, zdStepN w i



def ZdIsSAW {d n : ℕ} (w : Fin n → ZdStep d) : Prop :=
  ∀ k1 k2 : ℕ, k1 ≤ n → k2 ≤ n → zdPos w k1 = zdPos w k2 → k1 = k2



def ZdIsNB {d n : ℕ} (w : Fin n → ZdStep d) : Prop :=
  ∀ i : Fin n, ∀ (h : (i : ℕ) + 1 < n), w ⟨(i : ℕ) + 1, h⟩ ≠ zdReverse (w i)


noncomputable def zdSAWWalks (d n : ℕ) : Finset (Fin n → ZdStep d) :=
  Finset.univ.filter (fun w => ZdIsSAW w)


noncomputable def zdNBWalks (d n : ℕ) : Finset (Fin n → ZdStep d) :=
  Finset.univ.filter (fun w => ZdIsNB w)



noncomputable def zdSAWCount (d n : ℕ) : ℕ := (zdSAWWalks d n).card


noncomputable def zdNBCount (d n : ℕ) : ℕ := (zdNBWalks d n).card

@[simp] lemma zd_mem_sawWalks {d n : ℕ} {w : Fin n → ZdStep d} :
    w ∈ zdSAWWalks d n ↔ ZdIsSAW w := by simp [zdSAWWalks]

@[simp] lemma zd_mem_nbWalks {d n : ℕ} {w : Fin n → ZdStep d} :
    w ∈ zdNBWalks d n ↔ ZdIsNB w := by simp [zdNBWalks]





lemma zdStepVec_reverse {d : ℕ} (s : ZdStep d) :
    zdStepVec (zdReverse s) = - zdStepVec s := by
  funext j; unfold zdStepVec zdReverse
  by_cases hj : j = s.1
  · simp only [hj]; cases s.2 <;> simp
  · simp [hj]


lemma zdPos_succ {d n : ℕ} (w : Fin n → ZdStep d) (k : ℕ) :
    zdPos w (k + 1) = zdPos w k + zdStepN w k := by
  unfold zdPos; rw [Finset.sum_range_succ]


lemma zd_card_step (d : ℕ) : Fintype.card (ZdStep d) = 2 * d := by
  simp only [ZdStep, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring


lemma zd_card_ne (d : ℕ) (t : ZdStep d) :
    (Finset.univ.filter (fun s : ZdStep d => s ≠ t)).card = 2 * d - 1 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ t),
    Finset.card_univ, zd_card_step]











def zdWOf {d n : ℕ} (σ : Fin n → Fin d) : Fin n → ZdStep d := fun i => (σ i, true)


lemma zd_sum_stepVec_pos {d : ℕ} (i : Fin d) :
    ∑ j : Fin d, zdStepVec ((i, true) : ZdStep d) j = 1 := by
  unfold zdStepVec; simp



lemma zd_totalSum_wOf {d n : ℕ} (σ : Fin n → Fin d) (k : ℕ) (hk : k ≤ n) :
    ∑ j : Fin d, (zdPos (zdWOf σ) k) j = (k : ℤ) := by
  unfold zdPos zdStepN zdWOf
  simp_rw [Finset.sum_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl
    (fun i hi => by
      have : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
      rw [dif_pos this]
      exact zd_sum_stepVec_pos (σ ⟨i, this⟩))]
  simp


lemma zd_isSAW_wOf {d n : ℕ} (σ : Fin n → Fin d) : ZdIsSAW (zdWOf σ) := by
  intro k1 k2 h1 h2 h
  have : (∑ j : Fin d, (zdPos (zdWOf σ) k1) j) = (∑ j : Fin d, (zdPos (zdWOf σ) k2) j) := by
    rw [h]
  rw [zd_totalSum_wOf σ k1 h1, zd_totalSum_wOf σ k2 h2] at this
  exact_mod_cast this


lemma zd_wOf_injective {d n : ℕ} : Function.Injective (zdWOf : (Fin n → Fin d) → _) := by
  intro σ1 σ2 h
  funext i
  have := congrFun h i
  simp only [zdWOf, Prod.mk.injEq] at this
  exact this.1



theorem zd_pow_le_sawCount {d n : ℕ} : d ^ n ≤ zdSAWCount d n := by
  unfold zdSAWCount
  have himg : (Finset.univ : Finset (Fin n → Fin d)).image zdWOf ⊆ zdSAWWalks d n := by
    intro w hw
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨σ, rfl⟩ := hw
    exact zd_mem_sawWalks.mpr (zd_isSAW_wOf σ)
  calc d ^ n = (Finset.univ : Finset (Fin n → Fin d)).card := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    _ = ((Finset.univ : Finset (Fin n → Fin d)).image zdWOf).card := by
          rw [Finset.card_image_of_injective _ zd_wOf_injective]
    _ ≤ _ := Finset.card_le_card himg










lemma zd_isSAW_isNB {d n : ℕ} {w : Fin n → ZdStep d} (hw : ZdIsSAW w) : ZdIsNB w := by
  intro i h hcon
  set m := (i : ℕ) with hmdef
  have hm1 : m < n := i.2
  have hm2 : m + 1 < n := h
  have step1 : zdPos w (m + 1) = zdPos w m + zdStepN w m := zdPos_succ w m
  have step2 : zdPos w (m + 1 + 1) = zdPos w (m + 1) + zdStepN w (m + 1) := zdPos_succ w (m + 1)
  have hwm : w ⟨m + 1, hm2⟩ = zdReverse (w ⟨m, hm1⟩) := by
    have hc : w ⟨(i : ℕ) + 1, h⟩ = zdReverse (w i) := hcon
    simpa [hmdef] using hc
  have hstepm : zdStepN w m = zdStepVec (w ⟨m, hm1⟩) := by unfold zdStepN; rw [dif_pos hm1]
  have hstepm1 : zdStepN w (m + 1) = zdStepVec (w ⟨m + 1, hm2⟩) := by
    unfold zdStepN; rw [dif_pos hm2]
  have hpe : zdPos w (m + 1 + 1) = zdPos w m := by
    rw [step2, step1, hstepm, hstepm1, hwm, zdStepVec_reverse]; abel
  have heq := hw (m + 1 + 1) m (by omega) (by omega) hpe
  omega


lemma zd_sawWalks_subset_nbWalks {d n : ℕ} : zdSAWWalks d n ⊆ zdNBWalks d n := by
  intro w hw
  exact zd_mem_nbWalks.mpr (zd_isSAW_isNB (zd_mem_sawWalks.mp hw))


def zdDropLast {d n : ℕ} (w : Fin (n + 1) → ZdStep d) : Fin n → ZdStep d :=
  fun i => w i.castSucc



lemma zd_dropLast_isNB {d n : ℕ} {w : Fin (n + 1) → ZdStep d} (hw : ZdIsNB w) :
    ZdIsNB (zdDropLast w) := by
  intro i h
  have h' : ((i.castSucc : Fin (n + 1)) : ℕ) + 1 < n + 1 := by simp only [Fin.val_castSucc]; omega
  have key := hw i.castSucc h'
  show w (Fin.castSucc ⟨(i : ℕ) + 1, h⟩) ≠ zdReverse (w i.castSucc)
  have e1 : (Fin.castSucc (⟨(i : ℕ) + 1, h⟩ : Fin n))
      = (⟨((i.castSucc : Fin (n + 1)) : ℕ) + 1, h'⟩ : Fin (n + 1)) := by
    apply Fin.ext; simp
  rw [e1]; exact key




lemma zd_fiber_card_le {d n : ℕ} (hn : 1 ≤ n) (v : Fin n → ZdStep d) :
    ({w ∈ zdNBWalks d (n + 1) | zdDropLast w = v}).card ≤ 2 * d - 1 := by
  set prev : ZdStep d := v ⟨n - 1, by omega⟩ with hprev
  rw [← zd_card_ne d (zdReverse prev)]
  apply Finset.card_le_card_of_injOn (fun w => w (Fin.last n))
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, zd_mem_nbWalks] at hw
    obtain ⟨hnb, hdrop⟩ := hw
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    have hidx : ((⟨n - 1, by omega⟩ : Fin n) : ℕ) + 1 < n + 1 := by omega
    have hnb2 := hnb ⟨n - 1, by omega⟩ hidx
    have eL : (⟨((⟨n - 1, by omega⟩ : Fin n) : ℕ) + 1, hidx⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext; simp; omega
    rw [eL] at hnb2
    have e2 : (⟨n - 1, by omega⟩ : Fin (n + 1)) = Fin.castSucc (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext; simp
    rw [e2] at hnb2
    have ev : w (Fin.castSucc ⟨n - 1, by omega⟩) = prev := by
      have hh : zdDropLast w ⟨n - 1, by omega⟩ = v ⟨n - 1, by omega⟩ := by rw [hdrop]
      simpa [zdDropLast, hprev] using hh
    rw [ev] at hnb2
    exact hnb2
  · intro w1 hw1 w2 hw2 hval
    simp only [Finset.coe_filter, Set.mem_setOf_eq, zd_mem_nbWalks] at hw1 hw2
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h1 := congrFun hw1.2 j
      have h2 := congrFun hw2.2 j
      simp only [zdDropLast] at h1 h2
      rw [h1, h2]
    · exact hval



lemma zd_nbCount_succ_le {d n : ℕ} (hn : 1 ≤ n) :
    zdNBCount d (n + 1) ≤ (2 * d - 1) * zdNBCount d n := by
  unfold zdNBCount
  have hmap : ∀ b ∈ (zdNBWalks d (n + 1)).image zdDropLast,
      ({w ∈ zdNBWalks d (n + 1) | zdDropLast w = b}).card ≤ 2 * d - 1 :=
    fun b _ => zd_fiber_card_le hn b
  have h1 := Finset.card_le_mul_card_image (zdNBWalks d (n + 1)) (2 * d - 1) hmap
  have himg : (zdNBWalks d (n + 1)).image zdDropLast ⊆ zdNBWalks d n := by
    intro v hv
    simp only [Finset.mem_image] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact zd_mem_nbWalks.mpr (zd_dropLast_isNB (zd_mem_nbWalks.mp hw))
  calc (zdNBWalks d (n + 1)).card
        ≤ (2 * d - 1) * ((zdNBWalks d (n + 1)).image zdDropLast).card := h1
    _ ≤ (2 * d - 1) * (zdNBWalks d n).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card himg)



lemma zd_nbCount_one (d : ℕ) : zdNBCount d 1 = 2 * d := by
  unfold zdNBCount zdNBWalks
  have : (Finset.univ.filter (fun w : Fin 1 → ZdStep d => ZdIsNB w)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro w _ i h
    exact absurd h (by omega)
  rw [this, Finset.card_univ, Fintype.card_fun, zd_card_step, Fintype.card_fin]
  ring



lemma zd_nbCount_bound (d n : ℕ) : zdNBCount d (n + 1) ≤ 2 * d * (2 * d - 1) ^ n := by
  induction n with
  | zero => simp [zd_nbCount_one]
  | succ k ih =>
    calc zdNBCount d (k + 1 + 1) ≤ (2 * d - 1) * zdNBCount d (k + 1) :=
            zd_nbCount_succ_le (by omega)
      _ ≤ (2 * d - 1) * (2 * d * (2 * d - 1) ^ k) := Nat.mul_le_mul_left _ ih
      _ = 2 * d * (2 * d - 1) ^ (k + 1) := by ring




theorem zd_sawCount_le {d n : ℕ} (hn : 1 ≤ n) :
    zdSAWCount d n ≤ 2 * d * (2 * d - 1) ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  
  have hk : 0 + k + 1 - 1 = k := by omega
  rw [hk]
  calc zdSAWCount d (0 + k + 1) ≤ zdNBCount d (0 + k + 1) :=
        Finset.card_le_card zd_sawWalks_subset_nbWalks
    _ ≤ 2 * d * (2 * d - 1) ^ k := by
          have := zd_nbCount_bound d k
          simpa [Nat.zero_add] using this









def zdPart1 {d m n : ℕ} (w : Fin (m + n) → ZdStep d) : Fin m → ZdStep d :=
  fun i => w ⟨i, by omega⟩


def zdPart2 {d m n : ℕ} (w : Fin (m + n) → ZdStep d) : Fin n → ZdStep d :=
  fun i => w ⟨m + i, by omega⟩

lemma zd_stepN_part1 {d m n : ℕ} (w : Fin (m + n) → ZdStep d) (i : ℕ) (hi : i < m) :
    zdStepN (zdPart1 (n := n) w) i = zdStepN w i := by
  unfold zdStepN zdPart1; rw [dif_pos hi, dif_pos (by omega)]

lemma zd_posN_part1 {d m n : ℕ} (w : Fin (m + n) → ZdStep d) (k : ℕ) (hk : k ≤ m) :
    zdPos (zdPart1 (n := n) w) k = zdPos w k := by
  unfold zdPos; apply Finset.sum_congr rfl; intro i hi
  exact zd_stepN_part1 w i (by have := Finset.mem_range.mp hi; omega)

lemma zd_stepN_part2 {d m n : ℕ} (w : Fin (m + n) → ZdStep d) (i : ℕ) :
    zdStepN (zdPart2 (m := m) w) i = zdStepN w (m + i) := by
  unfold zdStepN zdPart2
  by_cases hi : i < n
  · rw [dif_pos hi, dif_pos (by omega)]
  · rw [dif_neg hi, dif_neg (by omega)]

lemma zd_posN_part2 {d m n : ℕ} (w : Fin (m + n) → ZdStep d) (k : ℕ) :
    zdPos (zdPart2 (m := m) w) k = zdPos w (m + k) - zdPos w m := by
  unfold zdPos
  rw [eq_sub_iff_add_eq, add_comm, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  exact zd_stepN_part2 w i


lemma zd_part1_isSAW {d m n : ℕ} {w : Fin (m + n) → ZdStep d} (hw : ZdIsSAW w) :
    ZdIsSAW (zdPart1 (n := n) w) := by
  intro k1 k2 h1 h2 heq
  rw [zd_posN_part1 w k1 h1, zd_posN_part1 w k2 h2] at heq
  exact hw k1 k2 (by omega) (by omega) heq


lemma zd_part2_isSAW {d m n : ℕ} {w : Fin (m + n) → ZdStep d} (hw : ZdIsSAW w) :
    ZdIsSAW (zdPart2 (m := m) w) := by
  intro k1 k2 h1 h2 heq
  rw [zd_posN_part2 w k1, zd_posN_part2 w k2] at heq
  have hpe : zdPos w (m + k1) = zdPos w (m + k2) := sub_left_injective heq
  have := hw (m + k1) (m + k2) (by omega) (by omega) hpe
  omega


lemma zd_part_injective {d m n : ℕ} :
    Function.Injective
      (fun w : Fin (m + n) → ZdStep d => (zdPart1 (n := n) w, zdPart2 (m := m) w)) := by
  intro w1 w2 h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  funext i
  by_cases hi : (i : ℕ) < m
  · have := congrFun h1 ⟨i, hi⟩
    simpa [zdPart1] using this
  · have hi2 : (i : ℕ) - m < n := by omega
    have hc := congrFun h2 ⟨(i : ℕ) - m, hi2⟩
    simp only [zdPart2] at hc
    have e : (⟨m + ((i : ℕ) - m), by omega⟩ : Fin (m + n)) = i := by apply Fin.ext; simp; omega
    rw [e] at hc; exact hc



theorem zd_sawCount_submult (d m n : ℕ) :
    zdSAWCount d (m + n) ≤ zdSAWCount d m * zdSAWCount d n := by
  unfold zdSAWCount
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn
    (fun w => (zdPart1 (n := n) w, zdPart2 (m := m) w))
  · intro w hw
    rw [Finset.mem_coe, zd_mem_sawWalks] at hw
    exact Finset.mem_coe.mpr (Finset.mk_mem_product
      (zd_mem_sawWalks.mpr (zd_part1_isSAW hw))
      (zd_mem_sawWalks.mpr (zd_part2_isSAW hw)))
  · intro w1 _ w2 _ h; exact zd_part_injective h


lemma zd_one_le_sawCount {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : 1 ≤ zdSAWCount d n := by
  calc 1 = d ^ 0 := by simp
    _ ≤ d ^ n := Nat.pow_le_pow_right hd (Nat.zero_le n)
    _ ≤ zdSAWCount d n := by
        calc d ^ n ≤ d ^ n := le_refl _
          _ ≤ _ := zd_pow_le_sawCount









noncomputable def zdSAWCountR (d n : ℕ) : ℝ := (zdSAWCount d n : ℝ)

lemma zd_one_le_sawCountR {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : 1 ≤ zdSAWCountR d n := by
  unfold zdSAWCountR; exact_mod_cast zd_one_le_sawCount hd n

lemma zd_sawCountR_submult (d : ℕ) : Submultiplicative (zdSAWCountR d) := by
  intro m n
  unfold zdSAWCountR
  have := zd_sawCount_submult d m n
  exact_mod_cast this



theorem zd_connectiveConstant_exists {d : ℕ} (hd : 1 ≤ d) :
    ∃ μ : ℝ, 0 < μ ∧
      Tendsto (fun n => (zdSAWCountR d n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) :=
  connectiveConstant_tendsto (zd_one_le_sawCountR hd) (zd_sawCountR_submult d)








theorem zd_le_connectiveConstant {d : ℕ} {μ : ℝ}
    (hμ : Tendsto (fun n => (zdSAWCountR d n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ)) :
    (d : ℝ) ≤ μ := by
  refine ge_of_tendsto hμ ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  
  have hdn : ((d : ℝ) ^ n) ≤ zdSAWCountR d n := by
    unfold zdSAWCountR; exact_mod_cast (zd_pow_le_sawCount (d := d) (n := n))
  have hbase : (0 : ℝ) ≤ (d : ℝ) ^ n := by positivity
  have hmono : ((d : ℝ) ^ n) ^ ((n : ℝ)⁻¹) ≤ (zdSAWCountR d n) ^ ((n : ℝ)⁻¹) :=
    Real.rpow_le_rpow hbase hdn (by positivity)
  have hpow : ((d : ℝ) ^ n) ^ ((n : ℝ)⁻¹) = (d : ℝ) := by
    rw [← Real.rpow_natCast (d : ℝ) n, ← Real.rpow_mul (by positivity)]
    rw [mul_inv_cancel₀ (ne_of_gt hnR), Real.rpow_one]
  rw [hpow] at hmono
  exact hmono



lemma zd_upperSeq_tendsto {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun n : ℕ => ((2 * (d : ℝ)) * (2 * (d : ℝ) - 1) ^ (n - 1)) ^ ((n : ℝ)⁻¹))
      atTop (𝓝 (2 * (d : ℝ) - 1)) := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h2d1 : (0 : ℝ) < 2 * (d : ℝ) - 1 := by linarith
  set A := Real.log (2 * (d : ℝ))
  set L := Real.log (2 * (d : ℝ) - 1)
  have hlog : Tendsto (fun n : ℕ => (A + ((n : ℝ) - 1) * L) / n) atTop (𝓝 L) := by
    have heq : (fun n : ℕ => (A + ((n : ℝ) - 1) * L) / n)
        =ᶠ[atTop] (fun n : ℕ => (A - L) / n + L) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp; ring
    rw [tendsto_congr' heq]
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (A - L)).add (tendsto_const_nhds (x := L))
  have hexp : Tendsto (fun n : ℕ => Real.exp ((A + ((n : ℝ) - 1) * L) / n)) atTop
      (𝓝 (Real.exp L)) := (Real.continuous_exp.tendsto L).comp hlog
  rw [Real.exp_log h2d1] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by
    have : 0 < n := hn; exact_mod_cast this.ne'
  rw [Real.rpow_def_of_pos (by positivity), Real.exp_eq_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  congr 1
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; push_cast; ring
  rw [hcast]



theorem zd_connectiveConstant_le {d : ℕ} (hd : 1 ≤ d) {μ : ℝ}
    (hμ : Tendsto (fun n => (zdSAWCountR d n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ)) :
    μ ≤ 2 * (d : ℝ) - 1 := by
  refine le_of_tendsto_of_tendsto hμ (zd_upperSeq_tendsto hd) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  
  have hub : zdSAWCountR d n ≤ (2 * (d : ℝ)) * (2 * (d : ℝ) - 1) ^ (n - 1) := by
    unfold zdSAWCountR
    have := zd_sawCount_le (d := d) (n := n) hn
    have hcast : ((2 * d * (2 * d - 1) ^ (n - 1) : ℕ) : ℝ)
        = (2 * (d : ℝ)) * (2 * (d : ℝ) - 1) ^ (n - 1) := by
      have hdge : 1 ≤ 2 * d := by omega
      push_cast [Nat.cast_sub hdge]
      ring
    calc (zdSAWCount d n : ℝ) ≤ ((2 * d * (2 * d - 1) ^ (n - 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = (2 * (d : ℝ)) * (2 * (d : ℝ) - 1) ^ (n - 1) := hcast
  exact Real.rpow_le_rpow (by unfold zdSAWCountR; positivity) hub (by positivity)





theorem zd_connectiveConstant_bounds {d : ℕ} (hd : 1 ≤ d) :
    ∃ μ : ℝ, 0 < μ ∧
      Tendsto (fun n => (zdSAWCountR d n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) ∧
      (d : ℝ) ≤ μ ∧ μ ≤ 2 * (d : ℝ) - 1 := by
  obtain ⟨μ, hμpos, hμtend⟩ := zd_connectiveConstant_exists hd
  exact ⟨μ, hμpos, hμtend, zd_le_connectiveConstant hμtend, zd_connectiveConstant_le hd hμtend⟩

end StatMech.Universality
