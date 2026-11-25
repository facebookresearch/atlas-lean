/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.ListScheduling
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Rounding processing times to ticks

Rounding each processing time up to a whole number of ticks increases it by less than one
tick. On a fixed assignment to machines, the error in the makespan is therefore at most the
tick size times the largest number of jobs on any machine. This does not model setup or
sequence-dependent processing times.
-/

namespace Cslib.Algorithms.Lean.Scheduling

private theorem tick_bounds {p δ : ℝ} (hδ : 0 < δ) (hp : 0 ≤ p) :
    p ≤ δ * (⌈p / δ⌉₊ : ℝ) ∧ δ * (⌈p / δ⌉₊ : ℝ) < p + δ := by
  have hscale : δ * (p / δ) = p := by rw [mul_comm, div_mul_cancel₀ _ hδ.ne']
  constructor
  · calc
      p = δ * (p / δ) := hscale.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) hδ.le
  · calc
      _ < δ * (p / δ + 1) :=
        mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one (div_nonneg hp hδ.le)) hδ
      _ = p + δ := by rw [mul_add, mul_one, hscale]

private theorem sum_ticks_bounds (ps : List ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hps : ∀ p ∈ ps, 0 ≤ p) :
    ps.sum ≤ δ * (((ps.map fun p => ⌈p / δ⌉₊).sum : ℕ) : ℝ) ∧
      δ * (((ps.map fun p => ⌈p / δ⌉₊).sum : ℕ) : ℝ) ≤ ps.sum + δ * (ps.length : ℝ) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp := tick_bounds hδ (hps p List.mem_cons_self)
      have htail := ih fun q hq => hps q (List.mem_cons_of_mem p hq)
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
        mul_add, mul_one]
      refine ⟨add_le_add hp.1 htail.1, ?_⟩
      calc
        _ ≤ (p + δ) + (ps.sum + δ * (ps.length : ℝ)) := add_le_add hp.2.le htail.2
        _ = _ := by ac_rfl

/-- **Rounding processing times to ticks.** Let `σ i` list the nonnegative real processing
 times of the jobs assigned to machine `i`, on `m ≥ 1` machines. For a tick size `δ > 0`, round
 each processing time `p` up to `⌈p / δ⌉₊` ticks, keeping the assignment fixed. If `C` is the
 maximum real load and `T` is the natural-number makespan in ticks, then
 `C ≤ δ * (T : ℝ) ≤ C + δ * (K : ℝ)`, where `K` is the largest job-list length of any machine.
 Empty lists contribute zero load, and repeated times count as separate job occurrences. -/
public theorem makespan_rounding_to_ticks_bounds {m : ℕ} [NeZero m]
    (σ : Fin m → List ℝ) {δ : ℝ} (hδ : 0 < δ) (hσ : ∀ i, ∀ p ∈ σ i, 0 ≤ p) :
    let C := Finset.univ.sup' Finset.univ_nonempty fun i => (σ i).sum
    let T := makespan fun i => (σ i).map fun p => ⌈p / δ⌉₊
    let K := Finset.univ.sup fun i => (σ i).length
    C ≤ δ * (T : ℝ) ∧ δ * (T : ℝ) ≤ C + δ * (K : ℝ) := by
  intro C T K
  let ticks : Fin m → List ℕ := fun i => (σ i).map fun p => ⌈p / δ⌉₊
  constructor
  · refine Finset.sup'_le _ _ fun i _ => ?_
    exact (sum_ticks_bounds (σ i) hδ (hσ i)).1.trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (le_makespan (σ := ticks) i)) hδ.le)
  · obtain ⟨i, hi, hT⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun i => (ticks i).sum)
    change T = _ at hT
    rw [hT]
    refine (sum_ticks_bounds (σ i) hδ (hσ i)).2.trans (add_le_add ?_ ?_)
    · exact Finset.le_sup' (fun i => (σ i).sum) hi
    · exact mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Finset.le_sup (f := fun i => (σ i).length) hi)) hδ.le

end Cslib.Algorithms.Lean.Scheduling
