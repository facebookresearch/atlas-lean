/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.EventJumpHold

namespace MathlibExtTest.Probability.Process.EventJumpHold

open MathlibExt.Probability.Process.EventJumpHold

/-! Stage A: finite-event JumpHold adapter algebraic checks (cases 1-5). -/

/-- Empty event fixture: no events. -/
private def emptyRate : Fin 0 → Nat → ℝ := fun _ _ => 0
private def emptySucc : Fin 0 → Nat → Nat := fun _ x => x
private theorem emptyNN : ∀ e x, 0 ≤ emptyRate e x := fun _ _ => le_rfl

private theorem emptyEvents_holdRate : holdRate emptyRate (0 : Nat) = 1 := by
  apply holdRate_eq_one_of_totalRate_eq_zero
  unfold totalRate
  simp [emptyRate]

private theorem emptyEvents_jumpPMF :
    jumpPMF emptyRate emptySucc emptyNN (0 : Nat) = PMF.pure 0 := by
  apply jumpPMF_eq_pure_of_totalRate_eq_zero
  unfold totalRate
  simp [emptyRate]

/-- All-zero rates on a nonempty event type. -/
private def zeroRate : Fin 2 → Nat → ℝ := fun _ _ => 0
private def zeroSucc : Fin 2 → Nat → Nat := fun _ x => x
private theorem zeroNN : ∀ e x, 0 ≤ zeroRate e x := fun _ _ => le_rfl

private theorem zeroRates_holdRate : holdRate zeroRate (0 : Nat) = 1 := by
  apply holdRate_eq_one_of_totalRate_eq_zero
  unfold totalRate
  simp [zeroRate]

private theorem zeroRates_jumpPMF :
    jumpPMF zeroRate zeroSucc zeroNN (0 : Nat) = PMF.pure 0 := by
  apply jumpPMF_eq_pure_of_totalRate_eq_zero
  unfold totalRate
  simp [zeroRate]

/-- Duplicate successor: rates 1,2 to state 1 and rate 3 to state 2. -/
private def dupRate : Fin 3 → Nat → ℝ := fun e _ => ((e.val : ℝ) + 1)
private def dupSucc : Fin 3 → Nat → Nat := fun e _ => if e.val < 2 then 1 else 2
private theorem dupNN : ∀ e x, 0 ≤ dupRate e x :=
  fun _e _ => add_nonneg (Nat.cast_nonneg _) zero_le_one

private theorem duplicateSucc_mass :
    jumpPMF dupRate dupSucc dupNN (0 : Nat) (1 : Nat) =
      ENNReal.ofReal (1 / 2) := by
  have h0 : (0 : Fin 3).val = 0 := by decide
  have h1 : (1 : Fin 3).val = 1 := by decide
  have h2 : (2 : Fin 3).val = 2 := by decide
  have h_total : totalRate dupRate (0 : Nat) = 6 := by
    unfold totalRate
    norm_num [dupRate, Fin.sum_univ_three, h0, h1, h2]
  have h_ne : totalRate dupRate (0 : Nat) ≠ 0 := by
    rw [h_total]
    norm_num
  have h_filter :
      Finset.univ.filter (fun e : Fin 3 => dupSucc e (0 : Nat) = 1) = {0, 1} := by
    decide
  have h_group :
      (∑ e ∈ Finset.univ.filter (fun e : Fin 3 => dupSucc e (0 : Nat) = 1),
        dupRate e (0 : Nat)) = 3 := by
    rw [h_filter, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [dupRate, h0, h1]
  rw [jumpPMF_apply_of_totalRate_ne_zero _ _ _ _ h_ne _]
  rw [h_group, h_total]
  congr 1
  norm_num

/-- Holding rate times the duplicate-successor mass recovers the grouped rate `1 + 2`. -/
private theorem duplicateSucc_rate :
    holdRate dupRate (0 : Nat) *
        (jumpPMF dupRate dupSucc dupNN (0 : Nat) (1 : Nat)).toReal = 3 := by
  have h0 : (0 : Fin 3).val = 0 := by decide
  have h1 : (1 : Fin 3).val = 1 := by decide
  have h2 : (2 : Fin 3).val = 2 := by decide
  have h_ne : totalRate dupRate (0 : Nat) ≠ 0 := by
    unfold totalRate
    norm_num [dupRate, Fin.sum_univ_three, h0, h1, h2]
  have h_filter :
      Finset.univ.filter (fun e : Fin 3 => dupSucc e (0 : Nat) = 1) = {0, 1} := by
    decide
  rw [holdRate_mul_jumpPMF_toReal_of_totalRate_ne_zero _ _ _ _ h_ne, h_filter,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [dupRate, h0, h1]

/-- Self event of rate 5 plus an exit of rate 2: events occur at rate 7, departures at rate 2. -/
private def selfRate : Fin 2 → Nat → ℝ := fun e _ => if e.val = 0 then 5 else 2
private def selfSucc : Fin 2 → Nat → Nat := fun e _ => if e.val = 0 then 0 else 1
private theorem selfNN : ∀ e x, 0 ≤ selfRate e x := by
  intro e x
  unfold selfRate
  split
  · norm_num
  · norm_num

private theorem selfEvent_mass :
    holdRate selfRate (0 : Nat) = 7 ∧
    jumpPMF selfRate selfSucc selfNN (0 : Nat) (0 : Nat) =
      ENNReal.ofReal (5 / 7) := by
  have h0 : (0 : Fin 2).val = 0 := by decide
  have h1 : (1 : Fin 2).val = 1 := by decide
  have h10 : (1 : ℕ) ≠ 0 := by decide
  have h_total : totalRate selfRate (0 : Nat) = 7 := by
    unfold totalRate
    norm_num [selfRate, Fin.sum_univ_two, h0, h1, h10]
  have h_ne : totalRate selfRate (0 : Nat) ≠ 0 := by
    rw [h_total]
    norm_num
  have h_hold : holdRate selfRate (0 : Nat) = 7 := by
    rw [holdRate_eq_totalRate_of_totalRate_ne_zero _ _ h_ne, h_total]
  have h_filter :
      Finset.univ.filter (fun e : Fin 2 => selfSucc e (0 : Nat) = 0) = {0} := by
    decide
  have h_group :
      (∑ e ∈ Finset.univ.filter (fun e : Fin 2 => selfSucc e (0 : Nat) = 0),
        selfRate e (0 : Nat)) = 5 := by
    rw [h_filter, Finset.sum_singleton]
    norm_num [selfRate, h0]
  have h_mass :
      jumpPMF selfRate selfSucc selfNN (0 : Nat) (0 : Nat) =
        ENNReal.ofReal (5 / 7) := by
    rw [jumpPMF_apply_of_totalRate_ne_zero _ _ _ _ h_ne _, h_group, h_total]
  exact ⟨h_hold, h_mass⟩

/-- Only self events: identity successors with constant rate 5. -/
private def onlyRate : Fin 1 → Nat → ℝ := fun _ _ => 5
private def onlySucc : Fin 1 → Nat → Nat := fun _ x => x
private theorem onlyNN : ∀ e x, 0 ≤ onlyRate e x := by
  intro e x
  unfold onlyRate
  norm_num

private theorem onlySelf_holdRate : holdRate onlyRate (0 : Nat) = 5 := by
  have h_total : totalRate onlyRate (0 : Nat) = 5 := by
    unfold totalRate
    simp [onlyRate]
  have h_ne : totalRate onlyRate (0 : Nat) ≠ 0 := by
    rw [h_total]
    norm_num
  rw [holdRate_eq_totalRate_of_totalRate_ne_zero _ _ h_ne, h_total]

private theorem onlySelf_jumpPMF_pure :
    jumpPMF onlyRate onlySucc onlyNN (0 : Nat) = PMF.pure 0 := by
  have h_total : totalRate onlyRate (0 : Nat) = 5 := by
    unfold totalRate
    simp [onlyRate]
  have h_ne : totalRate onlyRate (0 : Nat) ≠ 0 := by
    rw [h_total]
    norm_num
  ext y
  by_cases hy : y = 0
  · subst hy
    have h_filter :
        Finset.univ.filter (fun e : Fin 1 => onlySucc e (0 : Nat) = 0) =
          Finset.univ := by
      decide
    have h_group :
        (∑ e ∈ Finset.univ.filter (fun e : Fin 1 => onlySucc e (0 : Nat) = 0),
          onlyRate e (0 : Nat)) = 5 := by
      rw [h_filter]
      simp [onlyRate]
    rw [jumpPMF_apply_of_totalRate_ne_zero _ _ _ _ h_ne _]
    rw [h_group, h_total]
    have h55 : (5 : ℝ) / 5 = 1 := by norm_num
    rw [h55, ENNReal.ofReal_one]
    simp [PMF.pure_apply]
  · have h0y : (0 : Nat) ≠ y := Ne.symm hy
    have h_filter :
        Finset.univ.filter (fun e : Fin 1 => onlySucc e (0 : Nat) = y) = ∅ := by
      simp [onlySucc, h0y]
    have h_group :
        (∑ e ∈ Finset.univ.filter (fun e : Fin 1 => onlySucc e (0 : Nat) = y),
          onlyRate e (0 : Nat)) = 0 := by
      rw [h_filter, Finset.sum_empty]
    rw [jumpPMF_apply_of_totalRate_ne_zero _ _ _ _ h_ne _]
    rw [h_group, h_total]
    have h05 : (0 : ℝ) / 5 = 0 := by norm_num
    rw [h05, ENNReal.ofReal_zero]
    simp [PMF.pure_apply, hy]

/-! Stage B: countable birth/death, deterministic observation, raw-total checks (cases 6-8). -/

/-- Countable birth/death on `Nat` with event type `Fin 2`. -/
private def bdRate : Fin 2 → Nat → ℝ :=
  fun e n => if e.val = 0 then 3 else if 0 < n then 2 else 0
private def bdSucc : Fin 2 → Nat → Nat :=
  fun e n => if e.val = 0 then n + 1 else n - 1
private theorem bdNN : ∀ e x, 0 ≤ bdRate e x := by
  intro e x
  unfold bdRate
  split_ifs <;> norm_num

private theorem birthDeath_zero_holdRate : holdRate bdRate (0 : Nat) = 3 := by
  have h0 : (0 : Fin 2).val = 0 := by decide
  have h1 : (1 : Fin 2).val = 1 := by decide
  have h10 : (1 : ℕ) ≠ 0 := by decide
  have h_total : totalRate bdRate (0 : Nat) = 3 := by
    unfold totalRate
    norm_num [bdRate, Fin.sum_univ_two, h0, h1, h10]
  have h_ne : totalRate bdRate (0 : Nat) ≠ 0 := by
    rw [h_total]
    norm_num
  rw [holdRate_eq_totalRate_of_totalRate_ne_zero _ _ h_ne, h_total]

private theorem birthDeath_zero_mass_one :
    jumpPMF bdRate bdSucc bdNN (0 : Nat) (1 : Nat) = 1 := by
  have h0 : (0 : Fin 2).val = 0 := by decide
  have h1 : (1 : Fin 2).val = 1 := by decide
  have h10 : (1 : ℕ) ≠ 0 := by decide
  have h_total : totalRate bdRate (0 : Nat) = 3 := by
    unfold totalRate
    norm_num [bdRate, Fin.sum_univ_two, h0, h1, h10]
  have h_ne : totalRate bdRate (0 : Nat) ≠ 0 := by
    rw [h_total]
    norm_num
  have h_filter :
      Finset.univ.filter (fun e : Fin 2 => bdSucc e (0 : Nat) = 1) = {0} := by
    decide
  have h_group :
      (∑ e ∈ Finset.univ.filter (fun e : Fin 2 => bdSucc e (0 : Nat) = 1),
        bdRate e (0 : Nat)) = 3 := by
    rw [h_filter, Finset.sum_singleton]
    norm_num [bdRate, h0]
  rw [jumpPMF_apply_of_totalRate_ne_zero _ _ _ _ h_ne _]
  rw [h_group, h_total]
  have h33 : (3 : ℝ) / 3 = 1 := by norm_num
  rw [h33, ENNReal.ofReal_one]

/-- Clamped death variant: death always rate 2, self at zero. -/
private def cdRate : Fin 2 → Nat → ℝ := fun e _ => if e.val = 0 then 3 else 2
private def cdSucc : Fin 2 → Nat → Nat :=
  fun e n => if e.val = 0 then n + 1 else n - 1
private theorem cdNN : ∀ e x, 0 ≤ cdRate e x := by
  intro e x
  unfold cdRate
  split
  · norm_num
  · norm_num

private theorem clampedDeath_zero_holdRate : holdRate cdRate (0 : Nat) = 5 := by
  have h0 : (0 : Fin 2).val = 0 := by decide
  have h1 : (1 : Fin 2).val = 1 := by decide
  have h10 : (1 : ℕ) ≠ 0 := by decide
  have h_total : totalRate cdRate (0 : Nat) = 5 := by
    unfold totalRate
    norm_num [cdRate, Fin.sum_univ_two, h0, h1, h10]
  have h_ne : totalRate cdRate (0 : Nat) ≠ 0 := by
    rw [h_total]
    norm_num
  rw [holdRate_eq_totalRate_of_totalRate_ne_zero _ _ h_ne, h_total]

private theorem clampedDeath_zero_self_mass :
    jumpPMF cdRate cdSucc cdNN (0 : Nat) (0 : Nat) =
      ENNReal.ofReal (2 / 5) := by
  have h0 : (0 : Fin 2).val = 0 := by decide
  have h1 : (1 : Fin 2).val = 1 := by decide
  have h10 : (1 : ℕ) ≠ 0 := by decide
  have h_total : totalRate cdRate (0 : Nat) = 5 := by
    unfold totalRate
    norm_num [cdRate, Fin.sum_univ_two, h0, h1, h10]
  have h_ne : totalRate cdRate (0 : Nat) ≠ 0 := by
    rw [h_total]
    norm_num
  have h_filter :
      Finset.univ.filter (fun e : Fin 2 => cdSucc e (0 : Nat) = 0) = {1} := by
    decide
  have h_group :
      (∑ e ∈ Finset.univ.filter (fun e : Fin 2 => cdSucc e (0 : Nat) = 0),
        cdRate e (0 : Nat)) = 2 := by
    rw [h_filter, Finset.sum_singleton]
    norm_num [cdRate, h1, h10]
  rw [jumpPMF_apply_of_totalRate_ne_zero _ _ _ _ h_ne _, h_group, h_total]

/-- Deterministic step sequence: successor with clock 5. -/
private def detΩ : Nat → (Nat → Nat) × ℝ := fun _ => (Nat.succ, 5)

private theorem obs_concrete_interval :
    (fun n : Nat => n + 10)
      (MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion.JumpHold.path
        (holdRate onlyRate) 0 detΩ 1) = 11 := by
  have h_clock : ∀ j, 0 ≤ (detΩ j).2 := by
    intro j
    simp only [detΩ]
    norm_num
  have h_hold5 : ∀ n : Nat, holdRate onlyRate n = 5 := by
    intro n
    have h_total : totalRate onlyRate n = 5 := by
      unfold totalRate
      simp [onlyRate]
    have h_ne : totalRate onlyRate n ≠ 0 := by
      rw [h_total]
      norm_num
    rw [holdRate_eq_totalRate_of_totalRate_ne_zero _ _ h_ne, h_total]
  have h_ht0 :
      MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion.JumpHold.holdingTime
        (holdRate onlyRate) 0 detΩ 0 = 1 := by
    unfold MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion.JumpHold.holdingTime
    simp only [detΩ]
    rw [h_hold5]
    norm_num
  have h_ht1 :
      MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion.JumpHold.holdingTime
        (holdRate onlyRate) 0 detΩ 1 = 1 := by
    unfold MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion.JumpHold.holdingTime
    simp only [detΩ]
    rw [h_hold5]
    norm_num
  have h_jt1 :
      MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion.JumpHold.jumpTime
        (holdRate onlyRate) 0 detΩ 1 = 1 := by
    unfold MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion.JumpHold.jumpTime
    rw [Finset.sum_range_one, h_ht0]
  have h_jt2 :
      MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion.JumpHold.jumpTime
        (holdRate onlyRate) 0 detΩ 2 = 2 := by
    unfold MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion.JumpHold.jumpTime
    have h2 : (2 : Nat) = 1 + 1 := by norm_num
    rw [h2, Finset.sum_range_succ, Finset.sum_range_one, h_ht0, h_ht1]
    norm_num
  have h_chain1 :
      ProbabilityTheory.ctmcJumpChain
        0 detΩ 1 = 1 :=
    rfl
  have h_lo :
      MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion.JumpHold.jumpTime
        (holdRate onlyRate) 0 detΩ 1 ≤ 1 := by
    rw [h_jt1]
  have h_hi :
      (1 : ℝ) <
        MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion.JumpHold.jumpTime
          (holdRate onlyRate) 0 detΩ (1 + 1) := by
    have h2 : (1 + 1 : Nat) = 2 := by norm_num
    rw [h2, h_jt2]
    norm_num
  have h_obs :=
    obs_path_eq_obs_chain_of_le_of_lt onlyRate onlyNN (fun n : Nat => n + 10) 0 detΩ
      h_clock 1 1 h_lo h_hi
  rw [h_chain1] at h_obs
  exact h_obs

private theorem rawTotalRate_zero_not_pos :
    ¬ (0 : ℝ) < totalRate zeroRate (0 : Nat) := by
  have h_total : totalRate zeroRate (0 : Nat) = 0 := by
    unfold totalRate
    simp [zeroRate]
  rw [h_total]
  norm_num

end MathlibExtTest.Probability.Process.EventJumpHold
