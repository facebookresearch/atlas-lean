/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.FK.BoxFeketePerVolume
import Code.FK.FKInterfaceSubadd

open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice SimpleGraph

variable {d : ℕ}




noncomputable def bxt_u (d : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  - Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2)


noncomputable def bxt_E (d n : ℕ) : ℝ := ((boxGraph d n).edgeFinset.card : ℝ)



theorem bxt_g_eq (d : ℕ) (t : ℝ) (n : ℕ) :
    ivp2_tiltFreeEnergy (boxGraph d n) 2 t
      = - (bxt_u d t n / bxt_E d n) + Real.log (1 + Real.exp t) := by
  unfold ivp2_tiltFreeEnergy bxt_u bxt_E
  ring


theorem bxt_E_nonneg (d n : ℕ) : 0 ≤ bxt_E d n := by
  unfold bxt_E; positivity















theorem bxt_perVolume_doubling_step
    {a A e E K c i : ℝ} (he : 0 < e) (hE : 0 < E) (hc : 0 ≤ c) (hi : 0 ≤ i)
    (hA : A ≤ K * a + i * c) (hedge : |K * e - E| ≤ i) :
    - (a / e) - (|a| / e + c) * (i / E) ≤ - (A / E) := by
  have hmain : A / E - a / e ≤ (|a| / e + c) * (i / E) := by
    have hstep1 : A / E ≤ (K * a + i * c) / E := (div_le_div_iff_of_pos_right hE).mpr hA
    have hkey : (K * a + i * c) / E - a / e = a * (K * e - E) / (e * E) + i * c / E := by
      field_simp; ring
    have hbound : a * (K * e - E) / (e * E) ≤ (|a| / e) * (i / E) := by
      rw [div_mul_div_comm]
      apply (div_le_div_iff_of_pos_right (by positivity)).mpr
      calc a * (K * e - E) ≤ |a * (K * e - E)| := le_abs_self _
        _ = |a| * |K * e - E| := by rw [abs_mul]
        _ ≤ |a| * i := by apply mul_le_mul_of_nonneg_left hedge (abs_nonneg a)
    have hicE : i * c / E = c * (i / E) := by ring
    calc A / E - a / e ≤ (K * a + i * c) / E - a / e := by linarith
      _ = a * (K * e - E) / (e * E) + i * c / E := hkey
      _ ≤ (|a| / e) * (i / E) + c * (i / E) := by rw [hicE]; linarith [hbound]
      _ = (|a| / e + c) * (i / E) := by ring
  linarith














def bxt_NegLogDoublingBound (d : ℕ) (t : ℝ) : Prop :=
  ∃ (I : ℕ → ℝ),
    (∀ j, 0 ≤ I j)
    ∧ Summable (fun j => I j / bxt_E d (2 ^ (j + 1)))
    ∧ (∀ j, bxt_u d t (2 ^ (j + 1))
        ≤ (2 : ℝ) ^ d * bxt_u d t (2 ^ j) + I j * (- Real.log (1 - fsc_logistic t)))
    ∧ (∀ j, |(2 : ℝ) ^ d * bxt_E d (2 ^ j) - bxt_E d (2 ^ (j + 1))| ≤ I j)





















theorem bxt_perVolumeData_of_doubling (t : ℝ)
    (hbox : ∀ j, 0 < (boxGraph d (2 ^ j)).edgeFinset.card)
    (hdoubling : bxt_NegLogDoublingBound d t)
    (hbdd : ∃ M : ℝ, ∀ j, |bxt_u d t (2 ^ j) / bxt_E d (2 ^ j)| ≤ M)
    (osc : ℕ → ℝ) (hosc : Tendsto osc atTop (𝓝 0))
    (hsand : ∀ n, 1 ≤ n → |ivp2_tiltFreeEnergy (boxGraph d n) 2 t
        - ivp2_tiltFreeEnergy (boxGraph d (2 ^ (Nat.log 2 n))) 2 t| ≤ osc (Nat.log 2 n)) :
    bpv_PerVolumeFreeEnergyData d t := by
  classical
  obtain ⟨I, hInn, hIsum, hudbl, hEdge⟩ := hdoubling
  obtain ⟨M, hM⟩ := hbdd
  set c : ℝ := - Real.log (1 - fsc_logistic t) with hc
  
  have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
  have hp0 : (0:ℝ) < fsc_logistic t := fsc_logistic_pos t
  have hc0 : 0 ≤ c := by
    rw [hc, neg_nonneg]
    apply Real.log_nonpos (by linarith) (by linarith)
  
  have hEpos : ∀ j, 0 < bxt_E d (2 ^ j) := fun j => by
    unfold bxt_E; exact_mod_cast hbox j
  
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hMc0 : 0 ≤ M + c := by linarith
  
  have hIE0 : ∀ j, 0 ≤ I j / bxt_E d (2 ^ (j + 1)) := fun j =>
    div_nonneg (hInn j) (hEpos (j + 1)).le
  
  set δ : ℕ → ℝ := fun j => (M + c) * (I j / bxt_E d (2 ^ (j + 1))) with hδ
  refine ⟨δ, osc, ?_, ?_, ?_, ?_, hosc, hsand⟩
  · 
    intro j; exact mul_nonneg hMc0 (hIE0 j)
  · 
    exact hIsum.mul_left (M + c)
  · 
    intro j
    rw [bxt_g_eq d t (2 ^ j), bxt_g_eq d t (2 ^ (j + 1))]
    
    have hstep := bxt_perVolume_doubling_step (a := bxt_u d t (2 ^ j))
      (A := bxt_u d t (2 ^ (j + 1))) (e := bxt_E d (2 ^ j)) (E := bxt_E d (2 ^ (j + 1)))
      (K := (2 : ℝ) ^ d) (c := c) (i := I j)
      (hEpos j) (hEpos (j + 1)) hc0 (hInn j) (hudbl j) (hEdge j)
    
    have hdefle : (|bxt_u d t (2 ^ j)| / bxt_E d (2 ^ j) + c) * (I j / bxt_E d (2 ^ (j + 1)))
        ≤ δ j := by
      show _ ≤ (M + c) * (I j / bxt_E d (2 ^ (j + 1)))
      apply mul_le_mul_of_nonneg_right _ (hIE0 j)
      have habs : |bxt_u d t (2 ^ j)| / bxt_E d (2 ^ j) = |bxt_u d t (2 ^ j) / bxt_E d (2 ^ j)| := by
        rw [abs_div, abs_of_pos (hEpos j)]
      rw [habs]; have := hM j; linarith
    have hgoal : - (bxt_u d t (2 ^ j) / bxt_E d (2 ^ j)) - δ j
        ≤ - (bxt_u d t (2 ^ (j + 1)) / bxt_E d (2 ^ (j + 1))) := by
      have := hstep; linarith
    linarith
  · 
    refine ⟨M + Real.log (1 + Real.exp t), ?_⟩
    rintro x ⟨j, rfl⟩
    simp only
    rw [bxt_g_eq d t (2 ^ j)]
    have hlb : - M ≤ bxt_u d t (2 ^ j) / bxt_E d (2 ^ j) := (abs_le.mp (hM j)).1
    linarith

























theorem bxt_doublingBound_of_crossSplit (t : ℝ) (j : ℕ)
    {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (K : SimpleGraph (boxVerts d (2 ^ j) ⊕ W)) [DecidableRel K.Adj]
    (hci : fis_CrossInterface (boxGraph d (2 ^ j)) H K)
    (φ : boxGraph d (2 ^ (j + 1)) ≃g K)
    (hH : (fkZ (boxGraph d (2 ^ j)) (fsc_logistic t) 2) ^ (2 ^ d - 1)
        ≤ fkZ H (fsc_logistic t) 2) :
    bxt_u d t (2 ^ (j + 1))
      ≤ (2 : ℝ) ^ d * bxt_u d t (2 ^ j)
        + (fis_interface (boxGraph d (2 ^ j)) H K).card * (- Real.log (1 - fsc_logistic t)) := by
  set p := fsc_logistic t with hp
  have hp0 : (0:ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  
  have hiso : fkZ (boxGraph d (2 ^ (j + 1))) p 2 = fkZ K p 2 := fsm_fkZ_iso _ K φ p 2
  have hint := fis_neglog_interface_le hci hp0 hp1 (by norm_num : (0:ℝ) < 2)
  
  have hZG : 0 < fkZ (boxGraph d (2 ^ j)) p 2 := fkZ_pos _ hp0 hp1 (by norm_num)
  have hZH : 0 < fkZ H p 2 := fkZ_pos _ hp0 hp1 (by norm_num)
  
  have hlogH : - Real.log (fkZ H p 2) ≤ ((2 ^ d - 1 : ℕ) : ℝ) * (- Real.log (fkZ (boxGraph d (2 ^ j)) p 2)) := by
    have hle : Real.log ((fkZ (boxGraph d (2 ^ j)) p 2) ^ (2 ^ d - 1)) ≤ Real.log (fkZ H p 2) :=
      Real.log_le_log (pow_pos hZG _) hH
    rw [Real.log_pow] at hle
    
    nlinarith [hle]
  
  rw [bxt_u, hiso, bxt_u]
  
  
  have hcount : ((2 ^ d - 1 : ℕ) : ℝ) = (2:ℝ) ^ d - 1 := by
    have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    push_cast [Nat.cast_sub this]
    ring
  rw [hcount] at hlogH
  have hrw : (fis_interface (boxGraph d (2 ^ j)) H K).card * (- Real.log (1 - p))
      = - ((fis_interface (boxGraph d (2 ^ j)) H K).card * Real.log (1 - p)) := by ring
  rw [hrw]
  push_cast at hint ⊢
  nlinarith [hint, hlogH]









theorem bxt_negLogDoublingBound_satisfiable (d : ℕ) :
    ∃ (u E : ℕ → ℝ) (c : ℝ),
      (∃ (I : ℕ → ℝ),
        (∀ j, 0 ≤ I j)
        ∧ Summable (fun j => I j / E (2 ^ (j + 1)))
        ∧ (∀ j, u (2 ^ (j + 1)) ≤ (2 : ℝ) ^ d * u (2 ^ j) + I j * c)
        ∧ (∀ j, |(2 : ℝ) ^ d * E (2 ^ j) - E (2 ^ (j + 1))| ≤ I j)) := by
  
  refine ⟨fun _ => 0, fun n => (n : ℝ) ^ d, 0, fun _ => 0, fun _ => le_refl 0, ?_, ?_, ?_⟩
  · simp
  · intro j; simp
  · intro j
    simp only [abs_nonpos_iff]
    rw [sub_eq_zero]
    show (2 : ℝ) ^ d * ((2 ^ j : ℕ) : ℝ) ^ d = ((2 ^ (j + 1) : ℕ) : ℝ) ^ d
    push_cast
    rw [← mul_pow, pow_succ]
    ring
























theorem bxt_fk_uniqueness_of_doubling (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hdoubling : ∀ t, bxt_NegLogDoublingBound d t)
    (hbdd : ∀ t, ∃ M : ℝ, ∀ j, |bxt_u d t (2 ^ j) / bxt_E d (2 ^ j)| ≤ M)
    (osc : ℝ → ℕ → ℝ) (hosc : ∀ t, Tendsto (osc t) atTop (𝓝 0))
    (hsand : ∀ t, ∀ n, 1 ≤ n → |ivp2_tiltFreeEnergy (boxGraph d n) 2 t
        - ivp2_tiltFreeEnergy (boxGraph d (2 ^ (Nat.log 2 n))) 2 t| ≤ osc t (Nat.log 2 n))
    (hfreeRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t)
    (hwiredRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  have hdata : ∀ t, bpv_PerVolumeFreeEnergyData d t := fun t =>
    bxt_perVolumeData_of_doubling t (fun j => hEbox (2 ^ j)) (hdoubling t) (hbdd t)
      (osc t) (hosc t) (hsand t)
  exact bpv_fk_uniqueness_of_perVolume_rotation hd N eb hEbox hdata hfreeRot hwiredRot








































theorem bxt_residue_remark : True := trivial

end FK

end StatMech
