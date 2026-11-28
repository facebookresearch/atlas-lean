/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.RelativePositionFrequency
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Sqrt

/-! # Tests for relative positions and letter frequencies -/

namespace MetaMathlibExt.tendsto_relativePosition_div_of_frequency

open Filter Topology

-- In abbabb…, two letters out of every three are b, so the signed limit is negative.
private def abb (i : ℕ) : Bool := decide (i % 3 = 0)

example : Tendsto (fun n : ℕ => (relativePosition abb n : ℝ) / n) atTop (𝓝 (-3 / 2)) := by
  have count (m : ℕ) : letterCount abb false m = 2 * m / 3 := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [letterCount_succ, ih]
      simp only [abb, decide_eq_false_iff_not]
      have residues : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases residues with h | h | h <;> simp [h] <;> omega
  have freq : Tendsto (fun m : ℕ => (letterCount abb false m : ℝ) / m) atTop (𝓝 (2 / 3)) := by
    apply ((tendsto_nat_floor_mul_div_atTop (by norm_num : (0 : ℝ) ≤ 2 / 3)).comp
      tendsto_natCast_atTop_atTop).congr
    intro m
    simp only [Function.comp_apply, count, div_mul_eq_mul_div, ← Nat.floor_div_eq_div (K := ℝ)]
    norm_cast
  convert tendsto_relativePosition_div_of_frequency (by norm_num) (by norm_num) freq using 2
  norm_num

end MetaMathlibExt.tendsto_relativePosition_div_of_frequency

namespace MetaMathlibExt.tendsto_letterCount_div_iff_tendsto_letterPosition_div

open Filter Topology

-- Squares and nonsquares both occur infinitely often, but have densities zero and one.
private def squareWord (i : ℕ) : Bool := decide (i.sqrt ^ 2 = i)

private theorem strictMono_sq : StrictMono (fun n : ℕ => n ^ 2) :=
  fun _ _ h => by simpa only [pow_two] using Nat.mul_self_lt_mul_self_iff.mpr h

private theorem squareWord_infinite : BothLettersInfinite squareWord := by
  constructor
  · exact Set.infinite_of_injective_forall_mem strictMono_sq.injective fun n => by
      change squareWord (n ^ 2) = true
      simp [squareWord]
  · have hmono : StrictMono (fun n : ℕ => (n + 1) ^ 2 + 1) :=
      fun _ _ h => Nat.add_lt_add_right (strictMono_sq (Nat.add_lt_add_right h 1)) 1
    refine Set.infinite_of_injective_forall_mem hmono.injective fun n => ?_
    have hlt : (n + 1) ^ 2 + 1 < (n + 1 + 1) ^ 2 := calc
      _ < (n + 1) ^ 2 + (2 * (n + 1) + 1) := Nat.add_lt_add_left (by omega) _
      _ = _ := by ring
    have h := Nat.not_exists_sq' (by omega : (n + 1) ^ 2 < (n + 1) ^ 2 + 1) hlt
    change squareWord ((n + 1) ^ 2 + 1) = false
    simpa only [squareWord, decide_eq_false_iff_not] using fun heq => h ⟨_, heq⟩

private theorem squareWord_position_diverges :
    Tendsto (fun n : ℕ => (letterPosition squareWord true n : ℝ) / n) atTop atTop := by
  have hpos (n : ℕ) : letterPosition squareWord true (n + 1) = n ^ 2 := by
    simp only [letterPosition, Nat.add_sub_cancel]
    symm
    refine Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (fun k : ℕ => k ^ 2) ?_ ?_
      (strictMono_sq.strictMonoOn _) (fun hf => (squareWord_infinite.1 hf).elim)
    · intro k hk
      have heq : k.sqrt ^ 2 = k := by simpa [squareWord] using hk
      exact ⟨k.sqrt, fun hf => (squareWord_infinite.1 hf).elim, heq⟩
    · intro k _
      change squareWord (k ^ 2) = true
      simp [squareWord]
  apply (tendsto_add_atTop_iff_nat 1).mp
  refine tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ) / 2) (fun n => ?_)
    (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num))
  rw [hpos, Nat.cast_pow, Nat.cast_add, Nat.cast_one, le_div_iff₀ (by positivity)]
  rcases n with _ | n
  · norm_num
  · push_cast
    nlinarith

example : Tendsto (fun m : ℕ => (letterCount squareWord true m : ℝ) / m) atTop (𝓝 0) :=
  (tendsto_letterCount_div_iff_tendsto_letterPosition_div squareWord_infinite true).2.mpr
    squareWord_position_diverges

example : Tendsto (fun n : ℕ => (letterPosition squareWord false n : ℝ) / n) atTop (𝓝 1) := by
  have hzero := (tendsto_letterCount_div_iff_tendsto_letterPosition_div
    squareWord_infinite true).2.mpr squareWord_position_diverges
  have hone : Tendsto (fun m : ℕ => (letterCount squareWord false m : ℝ) / m) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with m hm
    have hsum : (letterCount squareWord true m : ℝ) + letterCount squareWord false m = m := by
      exact_mod_cast (show letterCount squareWord true m + letterCount squareWord false m = m by
        simpa [letterCount] using
          (Finset.range m).card_filter_add_card_filter_not (fun i => squareWord i = true))
    rw [eq_sub_of_add_eq' hsum, sub_div, div_self (Nat.cast_ne_zero.mpr hm)]
  simpa only [div_one] using
    ((tendsto_letterCount_div_iff_tendsto_letterPosition_div squareWord_infinite false).1
      1 zero_lt_one le_rfl).mp hone

end MetaMathlibExt.tendsto_letterCount_div_iff_tendsto_letterPosition_div
