/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Probability.DTMCReachability

namespace Cslib.Probability.Tests

open Cslib.Probability

variable {S : Type*} [Fintype S] [DecidableEq S] (D : DTMC S) (A B : Finset S)

/-- The closed one-state chain: every transition loops. -/
def loopDTMC : DTMC (Fin 1) where
  val := fun _ _ => 1
  property := Matrix.mem_rowStochastic_iff_sum.mpr
    ⟨fun _ _ => zero_le_one, fun _ => by simp⟩

/-- A closed nontarget self-loop has reach probability `0`. -/
theorem reachProb_loop :
    loopDTMC.reachProb {0} ∅ 0 = 0 := by
  have hall : ∀ n (s : Fin 1), loopDTMC.hitProb {0} ∅ n s = 0 := by
    intro n
    induction n with
    | zero =>
      intro s
      have hz := hitProb_zero (S := Fin 1) loopDTMC {0} ∅ s
      rw [hz]
      simp
    | succ n IH =>
      intro s
      have hs := hitProb_succ (S := Fin 1) loopDTMC {0} ∅ n s
      have hsB : s ∉ (∅ : Finset (Fin 1)) := by simp
      have hsA : s ∈ ({0} : Finset (Fin 1)) := by fin_cases s; simp
      have hsA' : ¬ s ∉ ({0} : Finset (Fin 1)) := by simpa using hsA
      rw [hs, ite_eq_right hsB, ite_eq_right hsA']
      have hzero : ∀ t : Fin 1, loopDTMC.P s t * loopDTMC.hitProb {0} ∅ n t = 0 := by
        intro t
        rw [IH t, mul_zero]
      simp [hzero]
  have hconst : (fun n => ((loopDTMC.hitProb {0} ∅ n 0 : ℚ) : ℝ)) = fun _ => (0 : ℝ) := by
    funext n
    have h := hall n 0
    exact_mod_cast h
  unfold DTMC.reachProb
  rw [hconst]
  exact ciSup_const

/-- Yet the constant `1` function is a Bellman fixed point there, so the
fixed-point equation alone does not determine reachability. -/
theorem bellman_loop_one :
    loopDTMC.bellman {0} ∅ (fun _ => 1) = fun _ => 1 := by
  funext s
  fin_cases s
  unfold DTMC.bellman loopDTMC DTMC.P
  simp

/-- The constant `-1` function is also a Bellman fixed point there,
which is why leastness is stated among nonnegative functions. -/
theorem bellman_loop_neg_one :
    loopDTMC.bellman {0} ∅ (fun _ => -1) = fun _ => -1 := by
  funext s
  fin_cases s
  unfold DTMC.bellman loopDTMC DTMC.P
  simp

/-- The half/half branch: from `0`, move to the target `1` or the sink
`2` with probability `1/2` each; both are absorbing. -/
def branchDTMC : DTMC (Fin 3) where
  val := fun s t =>
    if s = 0 then (if t = 0 then 0 else 1 / 2)
    else if t = s then 1 else 0
  property := by
    refine Matrix.mem_rowStochastic_iff_sum.mpr ⟨?_, ?_⟩
    · intro s t
      fin_cases s <;> fin_cases t <;> norm_num
    · intro s
      fin_cases s <;> simp [Fin.sum_univ_three] <;> norm_num

/-- The deterministic two-step chain `0 → 1 → 2`, with `2` absorbing. -/
def chainDTMC : DTMC (Fin 3) where
  val := fun s t =>
    if s = 0 then (if t = 1 then 1 else 0)
    else if s = 1 then (if t = 2 then 1 else 0)
    else if t = 2 then 1 else 0
  property := by
    refine Matrix.mem_rowStochastic_iff_sum.mpr ⟨?_, ?_⟩
    · intro s t
      fin_cases s <;> fin_cases t <;> norm_num
    · intro s
      fin_cases s <;> simp [Fin.sum_univ_three]

/-- The half/half branch reaches the target with probability `1/2`. -/
theorem reachProb_branch :
    branchDTMC.reachProb {0, 2} {1} 0 = 1 / 2 := by
  have h0B : (0 : Fin 3) ∉ ({1} : Finset (Fin 3)) := by simp
  have h0A : (0 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)) := by simp
  have h0A' : ¬ (0 : Fin 3) ∉ ({0, 2} : Finset (Fin 3)) := by simp
  have h1B : (1 : Fin 3) ∈ ({1} : Finset (Fin 3)) := by simp
  have h2B : (2 : Fin 3) ∉ ({1} : Finset (Fin 3)) := by simp
  have h2A : (2 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)) := by simp
  have h2A' : ¬ (2 : Fin 3) ∉ ({0, 2} : Finset (Fin 3)) := by simp
  have h1 : ∀ n, branchDTMC.hitProb {0, 2} {1} n 1 = 1 := by
    intro n
    cases n with
    | zero =>
      have hz := hitProb_zero (S := Fin 3) branchDTMC {0, 2} {1} 1
      rw [ite_eq_left h1B] at hz
      exact hz
    | succ n =>
      have hs := hitProb_succ (S := Fin 3) branchDTMC {0, 2} {1} n 1
      rw [ite_eq_left h1B] at hs
      exact hs
  have h2 : ∀ n, branchDTMC.hitProb {0, 2} {1} n 2 = 0 := by
    intro n
    induction n with
    | zero =>
      have hz := hitProb_zero (S := Fin 3) branchDTMC {0, 2} {1} 2
      rw [ite_eq_right h2B] at hz
      exact hz
    | succ n IH =>
      have hs := hitProb_succ (S := Fin 3) branchDTMC {0, 2} {1} n 2
      rw [ite_eq_right h2B, ite_eq_right h2A'] at hs
      have hsum : (∑ t, branchDTMC.P 2 t * branchDTMC.hitProb {0, 2} {1} n t)
          = branchDTMC.hitProb {0, 2} {1} n 2 := by
        simp [branchDTMC, DTMC.P]
      rw [hsum, IH] at hs
      exact hs
  have hz0 : branchDTMC.hitProb {0, 2} {1} 0 0 = 0 := by
    have hz := hitProb_zero (S := Fin 3) branchDTMC {0, 2} {1} 0
    rw [ite_eq_right h0B] at hz
    exact hz
  have h0succ : ∀ n, branchDTMC.hitProb {0, 2} {1} (n + 1) 0 = 1 / 2 := by
    intro n
    have hs := hitProb_succ (S := Fin 3) branchDTMC {0, 2} {1} n 0
    rw [ite_eq_right h0B, ite_eq_right h0A'] at hs
    have hsum : (∑ t, branchDTMC.P 0 t * branchDTMC.hitProb {0, 2} {1} n t)
        = 1 / 2 * branchDTMC.hitProb {0, 2} {1} n 1
          + 1 / 2 * branchDTMC.hitProb {0, 2} {1} n 2 := by
      simp [branchDTMC, DTMC.P, Fin.sum_univ_three]
    rw [hsum, h1 n, h2 n] at hs
    simp at hs
    linarith
  apply le_antisymm
  · unfold DTMC.reachProb
    apply ciSup_le
    intro n
    cases n with
    | zero =>
      have hc : ((branchDTMC.hitProb {0, 2} {1} 0 0 : ℚ) : ℝ) = 0 := by
        exact_mod_cast hz0
      rw [hc]
      norm_num
    | succ n =>
      have hc : ((branchDTMC.hitProb {0, 2} {1} (n + 1) 0 : ℚ) : ℝ) = 1 / 2 := by
        have h := h0succ n
        rw [h]
        norm_num
      rw [hc]
  · unfold DTMC.reachProb
    have hb := DTMC.hitProb_cast_bdd (S := Fin 3) branchDTMC {0, 2} {1} 0
    have hle : ((branchDTMC.hitProb {0, 2} {1} 1 0 : ℚ) : ℝ)
        ≤ ⨆ n, ((branchDTMC.hitProb {0, 2} {1} n 0 : ℚ) : ℝ) :=
      le_ciSup hb 1
    have hcast : ((branchDTMC.hitProb {0, 2} {1} 1 0 : ℚ) : ℝ) = 1 / 2 := by
      have h : branchDTMC.hitProb {0, 2} {1} 1 0 = 1 / 2 := h0succ 0
      rw [h]
      norm_num
    rw [hcast] at hle
    exact hle

/-- On the two-step chain, horizon `1` is too short, horizon `2`
suffices, and the unbounded probability is `1`. -/
theorem chain_horizons :
    chainDTMC.hitProb {0, 1} {2} 1 0 = 0 ∧
    chainDTMC.hitProb {0, 1} {2} 2 0 = 1 ∧
    chainDTMC.reachProb {0, 1} {2} 0 = 1 := by
  have h0B : (0 : Fin 3) ∉ ({2} : Finset (Fin 3)) := by simp
  have h0A : (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := by simp
  have h0A' : ¬ (0 : Fin 3) ∉ ({0, 1} : Finset (Fin 3)) := by simp
  have h1B : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)) := by simp
  have h1A : (1 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := by simp
  have h1A' : ¬ (1 : Fin 3) ∉ ({0, 1} : Finset (Fin 3)) := by simp
  have h2B : (2 : Fin 3) ∈ ({2} : Finset (Fin 3)) := by simp
  have hz0 := hitProb_zero (S := Fin 3) chainDTMC {0, 1} {2} 0
  have hz1 := hitProb_zero (S := Fin 3) chainDTMC {0, 1} {2} 1
  have hz2 := hitProb_zero (S := Fin 3) chainDTMC {0, 1} {2} 2
  rw [ite_eq_right h0B] at hz0
  rw [ite_eq_right h1B] at hz1
  rw [ite_eq_left h2B] at hz2
  have hs0 := hitProb_succ (S := Fin 3) chainDTMC {0, 1} {2} 0 0
  have hs1 := hitProb_succ (S := Fin 3) chainDTMC {0, 1} {2} 0 1
  rw [ite_eq_right h0B, ite_eq_right h0A'] at hs0
  rw [ite_eq_right h1B, ite_eq_right h1A'] at hs1
  have hsum0 : (∑ t, chainDTMC.P 0 t * chainDTMC.hitProb {0, 1} {2} 0 t)
      = chainDTMC.hitProb {0, 1} {2} 0 1 := by
    simp [chainDTMC, DTMC.P]
  have hsum1 : (∑ t, chainDTMC.P 1 t * chainDTMC.hitProb {0, 1} {2} 0 t)
      = chainDTMC.hitProb {0, 1} {2} 0 2 := by
    simp [chainDTMC, DTMC.P]
  rw [hsum0, hz1] at hs0
  rw [hsum1, hz2] at hs1
  have h1 : chainDTMC.hitProb {0, 1} {2} 1 0 = 0 := hs0
  have hs0b := hitProb_succ (S := Fin 3) chainDTMC {0, 1} {2} 1 0
  rw [ite_eq_right h0B, ite_eq_right h0A'] at hs0b
  have hsum0b : (∑ t, chainDTMC.P 0 t * chainDTMC.hitProb {0, 1} {2} 1 t)
      = chainDTMC.hitProb {0, 1} {2} 1 1 := by
    simp [chainDTMC, DTMC.P]
  rw [hsum0b, hs1] at hs0b
  have h2 : chainDTMC.hitProb {0, 1} {2} 2 0 = 1 := hs0b
  have hreach : chainDTMC.reachProb {0, 1} {2} 0 = 1 := by
    apply le_antisymm
    · exact reachProb_le_one (S := Fin 3) chainDTMC {0, 1} {2} 0
    · unfold DTMC.reachProb
      have hb := DTMC.hitProb_cast_bdd (S := Fin 3) chainDTMC {0, 1} {2} 0
      have hle : ((chainDTMC.hitProb {0, 1} {2} 2 0 : ℚ) : ℝ)
          ≤ ⨆ n, ((chainDTMC.hitProb {0, 1} {2} n 0 : ℚ) : ℝ) :=
        le_ciSup hb 2
      have hcast : ((chainDTMC.hitProb {0, 1} {2} 2 0 : ℚ) : ℝ) = 1 := by
        exact_mod_cast h2
      rw [hcast] at hle
      exact hle
  exact ⟨h1, h2, hreach⟩

/-- Horizon zero at a target state of the chain is `1`. -/
example : chainDTMC.hitProb {0, 1} {2} 0 2 = 1 := by
  rw [hitProb_zero]
  simp

/-- Horizon zero away from the target is `0`. -/
example : chainDTMC.hitProb {0, 1} {2} 0 0 = 0 := by
  rw [hitProb_zero]
  simp

/-- Leastness applied concretely: on the loop, every nonnegative
pre-fixed point is above the reachability value `0` (here the constant
`2` function). -/
example : loopDTMC.reachProb {0} ∅ 0 ≤ 2 :=
  reachProb_least loopDTMC {0} ∅ (fun _ => 2) (fun _ => by norm_num)
    (fun s => by
      fin_cases s
      simp [DTMC.bellman, DTMC.P, loopDTMC]) 0

end Cslib.Probability.Tests
