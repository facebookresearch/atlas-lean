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












abbrev TriSite : Type := Fin 2 → ℤ



abbrev TriStep : Type := Fin 6




def triStepVec (s : TriStep) : TriSite :=
  fun j =>
    match s, j with
    | 0, 0 => 1  | 0, 1 => 0
    | 1, 0 => -1 | 1, 1 => 0
    | 2, 0 => 0  | 2, 1 => 1
    | 3, 0 => 0  | 3, 1 => -1
    | 4, 0 => 1  | 4, 1 => -1
    | 5, 0 => -1 | 5, 1 => 1


def triReverse (s : TriStep) : TriStep :=
  match s with
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4



def triStepN {n : ℕ} (w : Fin n → TriStep) (i : ℕ) : TriSite :=
  if h : i < n then triStepVec (w ⟨i, h⟩) else 0



def triPos {n : ℕ} (w : Fin n → TriStep) (k : ℕ) : TriSite :=
  ∑ i ∈ Finset.range k, triStepN w i



def TriIsSAW {n : ℕ} (w : Fin n → TriStep) : Prop :=
  ∀ k1 k2 : ℕ, k1 ≤ n → k2 ≤ n → triPos w k1 = triPos w k2 → k1 = k2



def TriIsNB {n : ℕ} (w : Fin n → TriStep) : Prop :=
  ∀ i : Fin n, ∀ (h : (i : ℕ) + 1 < n), w ⟨(i : ℕ) + 1, h⟩ ≠ triReverse (w i)


noncomputable def triSAWWalks (n : ℕ) : Finset (Fin n → TriStep) :=
  Finset.univ.filter (fun w => TriIsSAW w)


noncomputable def triNBWalks (n : ℕ) : Finset (Fin n → TriStep) :=
  Finset.univ.filter (fun w => TriIsNB w)



noncomputable def triSAWCount (n : ℕ) : ℕ := (triSAWWalks n).card


noncomputable def triNBCount (n : ℕ) : ℕ := (triNBWalks n).card

@[simp] lemma tri_mem_sawWalks {n : ℕ} {w : Fin n → TriStep} :
    w ∈ triSAWWalks n ↔ TriIsSAW w := by simp [triSAWWalks]

@[simp] lemma tri_mem_nbWalks {n : ℕ} {w : Fin n → TriStep} :
    w ∈ triNBWalks n ↔ TriIsNB w := by simp [triNBWalks]





lemma triStepVec_reverse (s : TriStep) :
    triStepVec (triReverse s) = - triStepVec s := by
  funext j
  fin_cases s <;> fin_cases j <;> rfl


lemma triReverse_reverse (s : TriStep) : triReverse (triReverse s) = s := by
  fin_cases s <;> rfl



lemma triReverse_ne (s : TriStep) : triReverse s ≠ s := by
  fin_cases s <;> decide


lemma triPos_succ {n : ℕ} (w : Fin n → TriStep) (k : ℕ) :
    triPos w (k + 1) = triPos w k + triStepN w k := by
  unfold triPos; rw [Finset.sum_range_succ]


lemma tri_card_step : Fintype.card TriStep = 6 := by
  simp [TriStep]


lemma tri_card_ne (t : TriStep) :
    (Finset.univ.filter (fun s : TriStep => s ≠ t)).card = 5 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ t),
    Finset.card_univ, tri_card_step]

















def triPosStep (c : Fin 3) : TriStep :=
  match c with
  | 0 => 0 | 1 => 2 | 2 => 4


def triPhi (p : TriSite) : ℤ := 2 * p 0 + p 1



lemma tri_phi_posStep (c : Fin 3) : 1 ≤ triPhi (triStepVec (triPosStep c)) := by
  fin_cases c <;> decide


lemma triPhi_add (p q : TriSite) : triPhi (p + q) = triPhi p + triPhi q := by
  unfold triPhi; simp [Pi.add_apply]; ring


lemma triPhi_zero : triPhi (0 : TriSite) = 0 := by simp [triPhi]



def triWOf {n : ℕ} (σ : Fin n → Fin 3) : Fin n → TriStep := fun i => triPosStep (σ i)



lemma tri_phi_pos_wOf {n : ℕ} (σ : Fin n → Fin 3) (k : ℕ) (hk : k ≤ n) :
    (k : ℤ) ≤ triPhi (triPos (triWOf σ) k) := by
  induction k with
  | zero => simp [triPos, triPhi_zero]
  | succ j ih =>
    have hj : j ≤ n := by omega
    have hjn : j < n := by omega
    have hstep : triStepN (triWOf σ) j = triStepVec (triPosStep (σ ⟨j, hjn⟩)) := by
      unfold triStepN triWOf; rw [dif_pos hjn]
    rw [triPos_succ, triPhi_add, hstep]
    have h1 := tri_phi_posStep (σ ⟨j, hjn⟩)
    have h2 := ih hj
    push_cast
    linarith



lemma tri_phi_pos_strictMono {n : ℕ} (σ : Fin n → Fin 3) {k1 k2 : ℕ}
    (h12 : k1 < k2) (hk2 : k2 ≤ n) :
    triPhi (triPos (triWOf σ) k1) < triPhi (triPos (triWOf σ) k2) := by
  
  
  induction k2 with
  | zero => omega
  | succ j ih =>
    have hjn : j < n := by omega
    have hstep : triStepN (triWOf σ) j = triStepVec (triPosStep (σ ⟨j, hjn⟩)) := by
      unfold triStepN triWOf; rw [dif_pos hjn]
    have hpos : 1 ≤ triPhi (triStepVec (triPosStep (σ ⟨j, hjn⟩))) := tri_phi_posStep _
    rw [triPos_succ, triPhi_add, hstep]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h12 with hlt | heq
    · have := ih hlt (by omega)
      linarith
    · subst heq
      linarith


lemma tri_isSAW_wOf {n : ℕ} (σ : Fin n → Fin 3) : TriIsSAW (triWOf σ) := by
  intro k1 k2 h1 h2 h
  by_contra hne
  rcases Nat.lt_or_ge k1 k2 with hlt | hge
  · have := tri_phi_pos_strictMono σ hlt h2
    rw [h] at this; exact lt_irrefl _ this
  · have hlt : k2 < k1 := lt_of_le_of_ne hge (by omega)
    have := tri_phi_pos_strictMono σ hlt h1
    rw [h] at this; exact lt_irrefl _ this



lemma tri_posStep_injective : Function.Injective triPosStep := by
  decide


lemma tri_wOf_injective {n : ℕ} : Function.Injective (triWOf : (Fin n → Fin 3) → _) := by
  intro σ1 σ2 h
  funext i
  have := congrFun h i
  simp only [triWOf] at this
  exact tri_posStep_injective this



theorem tri_pow_le_sawCount {n : ℕ} : 3 ^ n ≤ triSAWCount n := by
  unfold triSAWCount
  have himg : (Finset.univ : Finset (Fin n → Fin 3)).image triWOf ⊆ triSAWWalks n := by
    intro w hw
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨σ, rfl⟩ := hw
    exact tri_mem_sawWalks.mpr (tri_isSAW_wOf σ)
  calc 3 ^ n = (Finset.univ : Finset (Fin n → Fin 3)).card := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    _ = ((Finset.univ : Finset (Fin n → Fin 3)).image triWOf).card := by
          rw [Finset.card_image_of_injective _ tri_wOf_injective]
    _ ≤ _ := Finset.card_le_card himg









lemma tri_isSAW_isNB {n : ℕ} {w : Fin n → TriStep} (hw : TriIsSAW w) : TriIsNB w := by
  intro i h hcon
  set m := (i : ℕ) with hmdef
  have hm1 : m < n := i.2
  have hm2 : m + 1 < n := h
  have step1 : triPos w (m + 1) = triPos w m + triStepN w m := triPos_succ w m
  have step2 : triPos w (m + 1 + 1) = triPos w (m + 1) + triStepN w (m + 1) :=
    triPos_succ w (m + 1)
  have hwm : w ⟨m + 1, hm2⟩ = triReverse (w ⟨m, hm1⟩) := by
    have hc : w ⟨(i : ℕ) + 1, h⟩ = triReverse (w i) := hcon
    simpa [hmdef] using hc
  have hstepm : triStepN w m = triStepVec (w ⟨m, hm1⟩) := by
    unfold triStepN; rw [dif_pos hm1]
  have hstepm1 : triStepN w (m + 1) = triStepVec (w ⟨m + 1, hm2⟩) := by
    unfold triStepN; rw [dif_pos hm2]
  have hpe : triPos w (m + 1 + 1) = triPos w m := by
    rw [step2, step1, hstepm, hstepm1, hwm, triStepVec_reverse]; abel
  have heq := hw (m + 1 + 1) m (by omega) (by omega) hpe
  omega


lemma tri_sawWalks_subset_nbWalks {n : ℕ} : triSAWWalks n ⊆ triNBWalks n := by
  intro w hw
  exact tri_mem_nbWalks.mpr (tri_isSAW_isNB (tri_mem_sawWalks.mp hw))


def triDropLast {n : ℕ} (w : Fin (n + 1) → TriStep) : Fin n → TriStep :=
  fun i => w i.castSucc



lemma tri_dropLast_isNB {n : ℕ} {w : Fin (n + 1) → TriStep} (hw : TriIsNB w) :
    TriIsNB (triDropLast w) := by
  intro i h
  have h' : ((i.castSucc : Fin (n + 1)) : ℕ) + 1 < n + 1 := by
    simp only [Fin.val_castSucc]; omega
  have key := hw i.castSucc h'
  show w (Fin.castSucc ⟨(i : ℕ) + 1, h⟩) ≠ triReverse (w i.castSucc)
  have e1 : (Fin.castSucc (⟨(i : ℕ) + 1, h⟩ : Fin n))
      = (⟨((i.castSucc : Fin (n + 1)) : ℕ) + 1, h'⟩ : Fin (n + 1)) := by
    apply Fin.ext; simp
  rw [e1]; exact key




lemma tri_fiber_card_le {n : ℕ} (hn : 1 ≤ n) (v : Fin n → TriStep) :
    ({w ∈ triNBWalks (n + 1) | triDropLast w = v}).card ≤ 5 := by
  set prev : TriStep := v ⟨n - 1, by omega⟩ with hprev
  rw [← tri_card_ne (triReverse prev)]
  apply Finset.card_le_card_of_injOn (fun w => w (Fin.last n))
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, tri_mem_nbWalks] at hw
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
      have hh : triDropLast w ⟨n - 1, by omega⟩ = v ⟨n - 1, by omega⟩ := by rw [hdrop]
      simpa [triDropLast, hprev] using hh
    rw [ev] at hnb2
    exact hnb2
  · intro w1 hw1 w2 hw2 hval
    simp only [Finset.coe_filter, Set.mem_setOf_eq, tri_mem_nbWalks] at hw1 hw2
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h1 := congrFun hw1.2 j
      have h2 := congrFun hw2.2 j
      simp only [triDropLast] at h1 h2
      rw [h1, h2]
    · exact hval



lemma tri_nbCount_succ_le {n : ℕ} (hn : 1 ≤ n) :
    triNBCount (n + 1) ≤ 5 * triNBCount n := by
  unfold triNBCount
  have hmap : ∀ b ∈ (triNBWalks (n + 1)).image triDropLast,
      ({w ∈ triNBWalks (n + 1) | triDropLast w = b}).card ≤ 5 :=
    fun b _ => tri_fiber_card_le hn b
  have h1 := Finset.card_le_mul_card_image (triNBWalks (n + 1)) 5 hmap
  have himg : (triNBWalks (n + 1)).image triDropLast ⊆ triNBWalks n := by
    intro v hv
    simp only [Finset.mem_image] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact tri_mem_nbWalks.mpr (tri_dropLast_isNB (tri_mem_nbWalks.mp hw))
  calc (triNBWalks (n + 1)).card
        ≤ 5 * ((triNBWalks (n + 1)).image triDropLast).card := h1
    _ ≤ 5 * (triNBWalks n).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card himg)



lemma tri_nbCount_one : triNBCount 1 = 6 := by
  unfold triNBCount triNBWalks
  have : (Finset.univ.filter (fun w : Fin 1 → TriStep => TriIsNB w)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro w _ i h
    exact absurd h (by omega)
  rw [this, Finset.card_univ, Fintype.card_fun, tri_card_step, Fintype.card_fin]
  norm_num


lemma tri_nbCount_bound (n : ℕ) : triNBCount (n + 1) ≤ 6 * 5 ^ n := by
  induction n with
  | zero => simp [tri_nbCount_one]
  | succ k ih =>
    calc triNBCount (k + 1 + 1) ≤ 5 * triNBCount (k + 1) :=
            tri_nbCount_succ_le (by omega)
      _ ≤ 5 * (6 * 5 ^ k) := Nat.mul_le_mul_left _ ih
      _ = 6 * 5 ^ (k + 1) := by ring




theorem tri_sawCount_le {n : ℕ} (hn : 1 ≤ n) :
    triSAWCount n ≤ 6 * 5 ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  have hk : 0 + k + 1 - 1 = k := by omega
  rw [hk]
  calc triSAWCount (0 + k + 1) ≤ triNBCount (0 + k + 1) :=
        Finset.card_le_card tri_sawWalks_subset_nbWalks
    _ ≤ 6 * 5 ^ k := by
          have := tri_nbCount_bound k
          simpa [Nat.zero_add] using this









def triPart1 {m n : ℕ} (w : Fin (m + n) → TriStep) : Fin m → TriStep :=
  fun i => w ⟨i, by omega⟩


def triPart2 {m n : ℕ} (w : Fin (m + n) → TriStep) : Fin n → TriStep :=
  fun i => w ⟨m + i, by omega⟩

lemma tri_stepN_part1 {m n : ℕ} (w : Fin (m + n) → TriStep) (i : ℕ) (hi : i < m) :
    triStepN (triPart1 (n := n) w) i = triStepN w i := by
  unfold triStepN triPart1; rw [dif_pos hi, dif_pos (by omega)]

lemma tri_posN_part1 {m n : ℕ} (w : Fin (m + n) → TriStep) (k : ℕ) (hk : k ≤ m) :
    triPos (triPart1 (n := n) w) k = triPos w k := by
  unfold triPos; apply Finset.sum_congr rfl; intro i hi
  exact tri_stepN_part1 w i (by have := Finset.mem_range.mp hi; omega)

lemma tri_stepN_part2 {m n : ℕ} (w : Fin (m + n) → TriStep) (i : ℕ) :
    triStepN (triPart2 (m := m) w) i = triStepN w (m + i) := by
  unfold triStepN triPart2
  by_cases hi : i < n
  · rw [dif_pos hi, dif_pos (by omega)]
  · rw [dif_neg hi, dif_neg (by omega)]

lemma tri_posN_part2 {m n : ℕ} (w : Fin (m + n) → TriStep) (k : ℕ) :
    triPos (triPart2 (m := m) w) k = triPos w (m + k) - triPos w m := by
  unfold triPos
  rw [eq_sub_iff_add_eq, add_comm, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  exact tri_stepN_part2 w i


lemma tri_part1_isSAW {m n : ℕ} {w : Fin (m + n) → TriStep} (hw : TriIsSAW w) :
    TriIsSAW (triPart1 (n := n) w) := by
  intro k1 k2 h1 h2 heq
  rw [tri_posN_part1 w k1 h1, tri_posN_part1 w k2 h2] at heq
  exact hw k1 k2 (by omega) (by omega) heq


lemma tri_part2_isSAW {m n : ℕ} {w : Fin (m + n) → TriStep} (hw : TriIsSAW w) :
    TriIsSAW (triPart2 (m := m) w) := by
  intro k1 k2 h1 h2 heq
  rw [tri_posN_part2 w k1, tri_posN_part2 w k2] at heq
  have hpe : triPos w (m + k1) = triPos w (m + k2) := sub_left_injective heq
  have := hw (m + k1) (m + k2) (by omega) (by omega) hpe
  omega


lemma tri_part_injective {m n : ℕ} :
    Function.Injective
      (fun w : Fin (m + n) → TriStep => (triPart1 (n := n) w, triPart2 (m := m) w)) := by
  intro w1 w2 h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  funext i
  by_cases hi : (i : ℕ) < m
  · have := congrFun h1 ⟨i, hi⟩
    simpa [triPart1] using this
  · have hi2 : (i : ℕ) - m < n := by omega
    have hc := congrFun h2 ⟨(i : ℕ) - m, hi2⟩
    simp only [triPart2] at hc
    have e : (⟨m + ((i : ℕ) - m), by omega⟩ : Fin (m + n)) = i := by apply Fin.ext; simp; omega
    rw [e] at hc; exact hc



theorem tri_sawCount_submult (m n : ℕ) :
    triSAWCount (m + n) ≤ triSAWCount m * triSAWCount n := by
  unfold triSAWCount
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn
    (fun w => (triPart1 (n := n) w, triPart2 (m := m) w))
  · intro w hw
    rw [Finset.mem_coe, tri_mem_sawWalks] at hw
    exact Finset.mem_coe.mpr (Finset.mk_mem_product
      (tri_mem_sawWalks.mpr (tri_part1_isSAW hw))
      (tri_mem_sawWalks.mpr (tri_part2_isSAW hw)))
  · intro w1 _ w2 _ h; exact tri_part_injective h


lemma tri_one_le_sawCount (n : ℕ) : 1 ≤ triSAWCount n := by
  calc 1 = 3 ^ 0 := by simp
    _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.zero_le n)
    _ ≤ triSAWCount n := tri_pow_le_sawCount









noncomputable def triSAWCountR (n : ℕ) : ℝ := (triSAWCount n : ℝ)

lemma tri_one_le_sawCountR (n : ℕ) : 1 ≤ triSAWCountR n := by
  unfold triSAWCountR; exact_mod_cast tri_one_le_sawCount n

lemma tri_sawCountR_submult : Submultiplicative triSAWCountR := by
  intro m n
  unfold triSAWCountR
  have := tri_sawCount_submult m n
  exact_mod_cast this



theorem tri_connectiveConstant_exists :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun n => (triSAWCountR n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ) :=
  connectiveConstant_tendsto tri_one_le_sawCountR tri_sawCountR_submult








theorem tri_le_connectiveConstant {κ : ℝ}
    (hκ : Tendsto (fun n => (triSAWCountR n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ)) :
    (3 : ℝ) ≤ κ := by
  refine ge_of_tendsto hκ ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdn : ((3 : ℝ) ^ n) ≤ triSAWCountR n := by
    unfold triSAWCountR; exact_mod_cast (tri_pow_le_sawCount (n := n))
  have hbase : (0 : ℝ) ≤ (3 : ℝ) ^ n := by positivity
  have hmono : ((3 : ℝ) ^ n) ^ ((n : ℝ)⁻¹) ≤ (triSAWCountR n) ^ ((n : ℝ)⁻¹) :=
    Real.rpow_le_rpow hbase hdn (by positivity)
  have hpow : ((3 : ℝ) ^ n) ^ ((n : ℝ)⁻¹) = (3 : ℝ) := by
    rw [← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_mul (by positivity)]
    rw [mul_inv_cancel₀ (ne_of_gt hnR), Real.rpow_one]
  rw [hpow] at hmono
  exact hmono


lemma tri_upperSeq_tendsto :
    Tendsto (fun n : ℕ => ((6 : ℝ) * (5 : ℝ) ^ (n - 1)) ^ ((n : ℝ)⁻¹))
      atTop (𝓝 5) := by
  set A := Real.log 6
  set L := Real.log 5
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
  have h5 : Real.exp L = 5 := by simp [L, Real.exp_log]
  rw [h5] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by
    have : 0 < n := hn; exact_mod_cast this.ne'
  rw [Real.rpow_def_of_pos (by positivity), Real.exp_eq_exp,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  congr 1
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; push_cast; ring
  rw [hcast]



theorem tri_connectiveConstant_le {κ : ℝ}
    (hκ : Tendsto (fun n => (triSAWCountR n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ)) :
    κ ≤ 5 := by
  refine le_of_tendsto_of_tendsto hκ tri_upperSeq_tendsto ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hub : triSAWCountR n ≤ (6 : ℝ) * (5 : ℝ) ^ (n - 1) := by
    unfold triSAWCountR
    have := tri_sawCount_le (n := n) hn
    have hcast : ((6 * 5 ^ (n - 1) : ℕ) : ℝ) = (6 : ℝ) * (5 : ℝ) ^ (n - 1) := by
      push_cast; ring
    calc (triSAWCount n : ℝ) ≤ ((6 * 5 ^ (n - 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = (6 : ℝ) * (5 : ℝ) ^ (n - 1) := hcast
  exact Real.rpow_le_rpow (by unfold triSAWCountR; positivity) hub (by positivity)






theorem tri_connectiveConstant_bounds :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun n => (triSAWCountR n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ) ∧
      (3 : ℝ) ≤ κ ∧ κ ≤ 5 := by
  obtain ⟨κ, hκpos, hκtend⟩ := tri_connectiveConstant_exists
  exact ⟨κ, hκpos, hκtend, tri_le_connectiveConstant hκtend, tri_connectiveConstant_le hκtend⟩

end StatMech.Universality
