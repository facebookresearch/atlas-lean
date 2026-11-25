/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

import PhyslibExt.FluidDynamics.Traffic.CumulativeInventory
import PhyslibExt.FluidDynamics.Traffic.ExitTime

/-!
# FIFO exit-time checks

Focused checks for `PhyslibExt.FluidDynamics.Traffic.ExitTime`:
the public shapes, the entry clamp, a flat departure interval,
initial vehicles, no finite exit, the grid sampling bridge to
cumulative inventory, uniqueness for strictly increasing
departures, and controls showing why each stated premise matters.

These are elaboration and non-vacuity checks, not new results.
-/

open scoped NNReal ENNReal

open FluidDynamics.Traffic.CumulativeInventory
open FluidDynamics.Traffic.ExitTime

/-- Test helper: an attained least hitting time is the exit time. -/
private lemma linkExitTime_eq_of_isLeast {N0 : ℝ≥0} {A D : ℝ≥0 → ℝ≥0}
    {t e : ℝ≥0} (hte : t ≤ e) (he : N0 + A t ≤ D e)
    (hmin : ∀ s, t ≤ s → N0 + A t ≤ D s → e ≤ s) :
    linkExitTime N0 A D t = e := by
  have hH : ∃ j, t ≤ j ∧
      (fun s (_ : Unit) => D s) j () ∈ Set.Ici (N0 + A t) :=
    ⟨e, hte, Set.mem_Ici.mpr he⟩
  have hbdd : BddBelow
      {i : ℝ≥0 | t ≤ i ∧
        (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} :=
    ⟨t, fun i hi => hi.1⟩
  have hs : sInf {i : ℝ≥0 | t ≤ i ∧
        (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} = e := by
    refine le_antisymm ?_ ?_
    · exact csInf_le hbdd ⟨hte, Set.mem_Ici.mpr he⟩
    · exact le_csInf ⟨e, hte, Set.mem_Ici.mpr he⟩
        fun i hi => hmin i hi.1 (Set.mem_Ici.mp hi.2)
  unfold linkExitTime MeasureTheory.hittingAfter
  rw [ite_eq_left hH, hs]

/-- Test helper: a hitting-time infimum need not be attained. -/
private lemma linkExitTime_eq_of_isInf {N0 : ℝ≥0} {A D : ℝ≥0 → ℝ≥0}
    {t e : ℝ≥0} (hH : ∃ j, t ≤ j ∧ N0 + A t ≤ D j)
    (hlb : ∀ s, t ≤ s → N0 + A t ≤ D s → e ≤ s)
    (happrox : ∀ ε : ℝ≥0, 0 < ε →
      ∃ s, t ≤ s ∧ N0 + A t ≤ D s ∧ s ≤ e + ε) :
    linkExitTime N0 A D t = e := by
  have hHex : ∃ j, t ≤ j ∧
      (fun s (_ : Unit) => D s) j () ∈ Set.Ici (N0 + A t) := by
    obtain ⟨j, hj, hDj⟩ := hH
    exact ⟨j, hj, Set.mem_Ici.mpr hDj⟩
  have hbdd : BddBelow
      {i : ℝ≥0 | t ≤ i ∧
        (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} :=
    ⟨t, fun i hi => hi.1⟩
  have hs : sInf {i : ℝ≥0 | t ≤ i ∧
        (fun s (_ : Unit) => D s) i () ∈ Set.Ici (N0 + A t)} = e := by
    refine le_antisymm ?_
      (le_csInf hHex fun i hi => hlb i hi.1 (Set.mem_Ici.mp hi.2))
    by_contra hnot
    push Not at hnot
    obtain ⟨r, her, hrs⟩ := exists_between hnot
    obtain ⟨s, hts, hDs, hsle⟩ := happrox (r - e) (tsub_pos_of_lt her)
    have hsum : e + (r - e) = r := add_tsub_cancel_of_le her.le
    rw [hsum] at hsle
    have hle := csInf_le hbdd ⟨hts, Set.mem_Ici.mpr hDs⟩
    exact absurd (le_trans hle hsle) (not_le_of_gt hrs)
  unfold linkExitTime MeasureTheory.hittingAfter
  rw [ite_eq_left hHex, hs]

/-- Test helper: if no later departure count reaches the FIFO
number, the exit time is `⊤`. -/
private lemma linkExitTime_eq_top_of_forall_lt {N0 : ℝ≥0}
    {A D : ℝ≥0 → ℝ≥0} {t : ℝ≥0}
    (h : ∀ j, t ≤ j → D j < N0 + A t) :
    linkExitTime N0 A D t = ⊤ := by
  unfold linkExitTime
  rw [MeasureTheory.hittingAfter_eq_top_iff]
  intro j hj hjmem
  exact not_le_of_gt (h j hj) (Set.mem_Ici.mp hjmem)

/-- Numeric helper for the plateau checks. -/
private lemma nnreal_five_half_eq : (5 / 2 : ℝ≥0) = 2 + 1 / 2 := by
  rw [← NNReal.coe_inj]
  norm_num [NNReal.coe_add, NNReal.coe_div]

/-- Numeric helper for the plateau checks. -/
private lemma nnreal_one_add_half : (1 : ℝ≥0) + 1 / 2 = 3 / 2 := by
  rw [← NNReal.coe_inj]
  norm_num [NNReal.coe_add, NNReal.coe_div]

/-- Public shape: FIFO monotonicity. -/
example {N0 : ℝ≥0} {A D : ℝ≥0 → ℝ≥0} (hA : Monotone A) :
    Monotone (linkExitTime N0 A D) :=
  linkExitTime_mono N0 A D hA

/-- Public shape: finite-exit admission. -/
example {N0 : ℝ≥0} {A D : ℝ≥0 → ℝ≥0} (hD : Monotone D) (t : ℝ≥0) :
    linkExitTime N0 A D t ≠ ⊤ ↔ ∃ s, N0 + A t ≤ D s :=
  linkExitTime_ne_top_iff N0 A D hD t

/-- Public shape: the generalized inverse test. -/
example {N0 : ℝ≥0} {A D : ℝ≥0 → ℝ≥0} (hD : Monotone D)
    (hrc : ∀ s, ContinuousWithinAt D (Set.Ici s) s)
    {t s : ℝ≥0} (hts : t ≤ s) :
    linkExitTime N0 A D t ≤ s ↔ N0 + A t ≤ D s :=
  linkExitTime_le_iff N0 A D hD hrc hts

/-- Public shape: exactness at a finite exit time. -/
example {N0 : ℝ≥0} {A D : ℝ≥0 → ℝ≥0} (hc : Continuous D)
    {t e : ℝ≥0} (hcaus : D t ≤ N0 + A t)
    (he : linkExitTime N0 A D t = e) :
    D e = N0 + A t :=
  apply_eq_label_of_linkExitTime_eq N0 A D hc hcaus he

/-- Public shape: exit time as entry time plus virtual delay. -/
example {N0 : ℝ≥0} {A D : ℝ≥0 → ℝ≥0} (t : ℝ≥0) :
    (linkExitTime N0 A D t : ℝ≥0∞) =
      (t : ℝ≥0∞) +
        Cslib.Algorithms.Networking.NetworkCalculus.delay
          (fun s => N0 + A s) D t :=
  linkExitTime_eq_add_delay N0 A D t

/-- The entry clamp: exit never precedes entry. -/
example {N0 : ℝ≥0} {A D : ℝ≥0 → ℝ≥0} (t : ℝ≥0) :
    (t : WithTop ℝ≥0) ≤ linkExitTime N0 A D t := by
  unfold linkExitTime
  exact MeasureTheory.le_hittingAfter ()

/-- Flat departure interval: FIFO number `1` exits at the left
end `1` of the plateau, not at `2`. -/
example :
    linkExitTime 1 (fun _ => 0) (fun s => min s 1 + (s - 2)) 0 = 1 := by
  refine linkExitTime_eq_of_isLeast (by norm_num) (by norm_num) ?_
  intro s _ hs
  by_contra hlt
  push Not at hlt
  have hs1 : (1 : ℝ≥0) ≤ min s 1 + (s - 2) := by simpa using hs
  have hDs : min s 1 + (s - 2) = s := by
    rw [min_eq_left hlt.le,
      tsub_eq_zero_of_le (le_trans hlt.le (by norm_num)), add_zero]
  rw [hDs] at hs1
  exact absurd hs1 (not_le_of_gt hlt)

/-- Flat departure interval: FIFO number `3 / 2` is reached only
at time `5 / 2`, after the plateau. -/
example :
    linkExitTime (3 / 2) (fun _ => 0)
        (fun s => min s 1 + (s - 2)) 0 = (5 / 2 : ℝ≥0) := by
  refine linkExitTime_eq_of_isLeast (by norm_num) ?_ ?_
  · have hD : min (5 / 2 : ℝ≥0) 1 + ((5 / 2 : ℝ≥0) - 2) = 3 / 2 := by
      rw [min_eq_right
          (by exact_mod_cast (by norm_num : (1 : ℝ) ≤ 5 / 2)),
        tsub_eq_of_eq_add_rev nnreal_five_half_eq]
      exact nnreal_one_add_half
    simpa [hD]
  intro s _ hs
  by_contra hlt
  push Not at hlt
  have hs1 : (3 / 2 : ℝ≥0) ≤ min s 1 + (s - 2) := by simpa using hs
  have hltD : min s 1 + (s - 2) < 3 / 2 := by
    rcases le_or_gt s 2 with hs2 | hs2
    · rw [tsub_eq_zero_of_le hs2, add_zero]
      exact lt_of_le_of_lt (min_le_right s 1)
        (by exact_mod_cast (by norm_num : (1 : ℝ) < 3 / 2))
    · have hsub : s - 2 < 1 / 2 := by
        by_contra hge
        push Not at hge
        have hle : (5 / 2 : ℝ≥0) ≤ s := by
          calc (5 / 2 : ℝ≥0) = 2 + 1 / 2 := nnreal_five_half_eq
            _ ≤ 2 + (s - 2) := add_le_add_right hge 2
            _ = s := add_tsub_cancel_of_le hs2.le
        exact absurd hle (not_le_of_gt hlt)
      have h := add_lt_add_of_le_of_lt (min_le_right s 1) hsub
      rwa [nnreal_one_add_half] at h
  exact absurd hs1 (not_le_of_gt hltD)

/-- Initial vehicles: with `N0 = 3`, the vehicle entering at
time `0` exits at `3 / 2`. -/
example :
    linkExitTime 3 (fun s => s) (fun s => min (2 * s) (3 + s)) 0
      = (3 / 2 : ℝ≥0) := by
  refine linkExitTime_eq_of_isLeast (by norm_num) ?_ ?_
  · have h : (3 : ℝ≥0) ≤ min (2 * (3 / 2)) (3 + 3 / 2) := by
      refine le_min ?_ ?_ <;> rw [← NNReal.coe_le_coe] <;> norm_num
    simpa using h
  intro s _ hs
  by_contra hlt
  push Not at hlt
  have hs1 : (3 : ℝ≥0) ≤ min (2 * s) (3 + s) := by simpa using hs
  have hlt2 : (2 : ℝ≥0) * s < 3 := by
    have h := mul_lt_mul_of_pos_left hlt (by norm_num : (0 : ℝ≥0) < 2)
    norm_num at h
    exact h
  exact absurd (le_trans hs1 (min_le_left _ _)) (not_le_of_gt hlt2)

/-- Initial vehicles: with `N0 = 3`, the vehicle entering at
time `1` exits at `2`. -/
example :
    linkExitTime 3 (fun s => s) (fun s => min (2 * s) (3 + s)) 1
      = 2 := by
  refine linkExitTime_eq_of_isLeast (by norm_num) (by norm_num) ?_
  intro s _ hs
  by_contra hlt
  push Not at hlt
  have hs1 : (4 : ℝ≥0) ≤ min (2 * s) (3 + s) := by
    calc (4 : ℝ≥0) = 3 + 1 := by norm_num
      _ ≤ min (2 * s) (3 + s) := by simpa using hs
  have hlt2 : (2 : ℝ≥0) * s < 4 := by
    have h := mul_lt_mul_of_pos_left hlt (by norm_num : (0 : ℝ≥0) < 2)
    norm_num at h
    exact h
  exact absurd (le_trans hs1 (min_le_left _ _)) (not_le_of_gt hlt2)

/-- No finite exit: a departure count capped at `1` never reaches
FIFO number `2`. -/
example :
    linkExitTime 2 (fun _ => 0) (fun s => min s 1) 1 = ⊤ := by
  refine linkExitTime_eq_top_of_forall_lt ?_
  intro j _
  have h : min j 1 < (2 : ℝ≥0) :=
    lt_of_le_of_lt (min_le_right j 1) (by norm_num)
  simpa using h

/-- Grid bridge: cumulative counts sampled at grid times recover
the discrete inventory identity, and sampling forces `A 0 = 0`. -/
example {N Fin Fout : ℕ → ℝ} {dt : ℝ≥0} {A D : ℝ≥0 → ℝ≥0}
    (hFin : ∀ j, 0 ≤ Fin j) (hFout : ∀ j, 0 ≤ Fout j)
    (hstep : ∀ j, N (j + 1) = N j + (dt : ℝ) * (Fin j - Fout j))
    (hA : ∀ n : ℕ, (A ((n : ℝ≥0) * dt) : ℝ) =
      ∑ j ∈ Finset.range n, (dt : ℝ) * Fin j)
    (hD : ∀ n : ℕ, (D ((n : ℝ≥0) * dt) : ℝ) =
      ∑ j ∈ Finset.range n, (dt : ℝ) * Fout j)
    (n : ℕ) :
    N n = N 0 + (A ((n : ℝ≥0) * dt) : ℝ)
        - (D ((n : ℝ≥0) * dt) : ℝ) ∧ A 0 = 0 := by
  have _ := hFin
  have _ := hFout
  have h := cumulative_link_inventory N Fin Fout (dt : ℝ)
    (NNReal.coe_nonneg dt) hstep n
  constructor
  · simpa [hA n, hD n] using h
  · have h0 := hA 0
    simp at h0
    exact_mod_cast h0

/-- Uniqueness: for strictly increasing continuous departures,
the exit time is the only time with the FIFO count. -/
example {N0 : ℝ≥0} {A D : ℝ≥0 → ℝ≥0} (hD : StrictMono D)
    (hc : Continuous D) {t s e : ℝ≥0} (hcaus : D t ≤ N0 + A t)
    (he : linkExitTime N0 A D t = e) (hs : D s = N0 + A t) :
    s = e := by
  have hDe := apply_eq_label_of_linkExitTime_eq N0 A D hc hcaus he
  exact hD.injective (hs.trans hDe.symm)

/-- Control: without nondecreasing arrivals, a one-time arrival
spike overtakes. The entry at `1` exits at `3`, after the entry
at `2`. -/
example :
    linkExitTime 0 (fun s => if s = 1 then 3 else 0) (fun s => s) 2 <
      linkExitTime 0 (fun s => if s = 1 then 3 else 0)
        (fun s => s) 1 := by
  have h1 : linkExitTime 0 (fun s => if s = 1 then 3 else 0)
        (fun s => s) 1 = 3 := by
    refine linkExitTime_eq_of_isLeast (by norm_num) (by norm_num) ?_
    intro s _ hs
    have hs1 : (3 : ℝ≥0) ≤ s := by simpa using hs
    exact hs1
  have h2 : linkExitTime 0 (fun s => if s = 1 then 3 else 0)
        (fun s => s) 2 = 2 := by
    refine linkExitTime_eq_of_isLeast le_rfl (by norm_num) ?_
    intro s hs _
    exact hs
  rw [h2, h1]
  norm_num

/-- Control: without nondecreasing departures, reaching the FIFO
number before entry does not give a finite exit. -/
example :
    (1 : ℝ≥0) ≤ (fun s => if s ≤ 1 then s else 0) 1 ∧
      linkExitTime 1 (fun _ => 0)
        (fun s => if s ≤ 1 then s else 0) 2 = ⊤ := by
  constructor
  · norm_num
  · refine linkExitTime_eq_top_of_forall_lt ?_
    intro j hj
    have hj1 : ¬ j ≤ 1 :=
      not_le_of_gt (lt_of_lt_of_le (by norm_num) hj)
    simp [hj1]

/-- Control: without right-continuity, the jump time is the
infimum exit time but the departure count there is still `0`. -/
example :
    linkExitTime 1 (fun _ => 0)
        (fun s => if s ≤ 1 then 0 else 1) 0 ≤ 1 ∧
      (fun s => if s ≤ 1 then 0 else 1) 1 = 0 := by
  have hexit : linkExitTime 1 (fun _ => 0)
        (fun s => if s ≤ 1 then 0 else 1) 0 = 1 := by
    refine linkExitTime_eq_of_isInf ?_ ?_ ?_
    · exact ⟨2, by norm_num, by norm_num⟩
    · intro s _ hs
      by_contra hlt
      push Not at hlt
      have hs1 : (1 : ℝ≥0) ≤ (if s ≤ 1 then 0 else 1) := by
        simpa using hs
      rw [ite_eq_left hlt.le] at hs1
      norm_num at hs1
    · intro ε hε
      refine ⟨1 + ε, by norm_num, ?_, le_refl _⟩
      have hnot : ¬ (1 + ε : ℝ≥0) ≤ 1 :=
        not_le_of_gt (lt_add_of_pos_right _ hε)
      simp [hnot]
  exact ⟨hexit.le, by norm_num⟩

/-- Control: the generalized-inverse test needs the comparison
time to be no earlier than entry. -/
example :
    (1 : ℝ≥0) ≤ (fun s => s) 1 ∧
      ¬ linkExitTime 1 (fun _ => 0) (fun s => s) 2 ≤ 1 := by
  have hexit : linkExitTime 1 (fun _ => 0) (fun s => s) 2 = 2 := by
    refine linkExitTime_eq_of_isLeast le_rfl (by norm_num) ?_
    intro s hs _
    exact hs
  constructor
  · norm_num
  · rw [hexit]
    norm_num

/-- Control: without nondecreasing departures, having exited by
a later time does not imply the count is still high then. -/
example :
    linkExitTime (1 / 2) (fun _ => 0)
        (fun s => if s < 1 then s else 0) 0 ≤ 2 ∧
      (fun s => if s < 1 then s else 0) 2 = 0 := by
  have hexit : linkExitTime (1 / 2) (fun _ => 0)
        (fun s => if s < 1 then s else 0) 0 = (1 / 2 : ℝ≥0) := by
    refine linkExitTime_eq_of_isLeast (by norm_num) (by norm_num) ?_
    intro s _ hs
    by_contra hlt
    push Not at hlt
    have hs1 : (1 / 2 : ℝ≥0) ≤ (if s < 1 then s else 0) := by
      simpa using hs
    have hslt : s < 1 := lt_trans hlt (by norm_num)
    rw [ite_eq_left hslt] at hs1
    exact absurd hs1 (not_le_of_gt hlt)
  constructor
  · have hhalf : (1 / 2 : ℝ≥0) ≤ 2 := by
      rw [← NNReal.coe_le_coe]
      norm_num
    rw [hexit]
    exact WithTop.coe_le_coe.mpr hhalf
  · norm_num

/-- Control: exactness needs the causal entry inequality. At
entry `1` with FIFO number `0`, exit is immediate but the
departure count is `1`. -/
example :
    linkExitTime 0 (fun _ => 0) (fun s => s) 1 = 1 ∧
      (fun s => s) 1 ≠ 0 := by
  have hexit : linkExitTime 0 (fun _ => 0) (fun s => s) 1 = 1 := by
    refine linkExitTime_eq_of_isLeast le_rfl (by norm_num) ?_
    intro s hs _
    exact hs
  exact ⟨hexit, by norm_num⟩

/-- Control: exactness needs continuous departures. A jump can
overshoot the FIFO number at the exit time. -/
example :
    linkExitTime 1 (fun s => if s < 1 then 0 else 1)
        (fun s => if s < 1 then 0 else 2) 0 = 1 ∧
      (fun s => if s < 1 then 0 else 2) 1 ≠ 1 := by
  have hexit : linkExitTime 1 (fun s => if s < 1 then 0 else 1)
        (fun s => if s < 1 then 0 else 2) 0 = 1 := by
    refine linkExitTime_eq_of_isLeast (by norm_num) (by norm_num) ?_
    intro s _ hs
    by_contra hlt
    push Not at hlt
    have hs1 : (1 : ℝ≥0) ≤ (if s < 1 then 0 else 2) := by
      simpa using hs
    rw [ite_eq_left hlt] at hs1
    norm_num at hs1
  exact ⟨hexit, by norm_num⟩

#print axioms FluidDynamics.Traffic.ExitTime.linkExitTime_mono
#print axioms FluidDynamics.Traffic.ExitTime.linkExitTime_ne_top_iff
#print axioms FluidDynamics.Traffic.ExitTime.linkExitTime_le_iff
#print axioms
  FluidDynamics.Traffic.ExitTime.apply_eq_label_of_linkExitTime_eq
#print axioms FluidDynamics.Traffic.ExitTime.linkExitTime_eq_add_delay
