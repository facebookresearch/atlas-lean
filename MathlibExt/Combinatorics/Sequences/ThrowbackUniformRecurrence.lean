/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Sequences.ThrowbackSequences
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Fin

/-!
# Uniform recurrence of throwback sequences

Every finite block of leaders of a strictly increasing sequence of positive integers
recurs with bounded gaps. Capping values at a finite threshold gives a reversible
finite system whose orbit records all leaders below the threshold.
-/

namespace MetaMathlibExt
namespace throwbackSequence_uniformly_recurrent

/-- The entry at each position is at least its index, also after a throwback. -/
private theorem index_le_throwback {s : ℕ → ℕ} (hs : ∀ i, i ≤ s i) (i : ℕ) :
    i ≤ throwback id s i := by
  simp only [throwback, id_eq]
  split_ifs with h h
  · exact (Nat.le_succ i).trans (hs _)
  · exact h.le
  · exact hs i

/-- At threshold `b` it suffices to keep positions through `b` and cap their entries at `b`. -/
private abbrev State (b : ℕ) := {s : Fin (b + 1) → Fin (b + 1) // ∀ i, i ≤ s i}

private def cap (b : ℕ) (s : ℕ → ℕ) (hs : ∀ i, i ≤ s i) : State b :=
  ⟨fun i => ⟨min (s i) b, by omega⟩, fun i => le_min (hs i) (Nat.le_of_lt_succ i.isLt)⟩

/-- Each entry shifted left by the rotation becomes strictly greater than its new index. -/
private theorem lt_shifted {b : ℕ} (s : State b) {i : Fin (b + 1)} (hi : i < s.val 0) :
    i < s.val ((s.val 0).cycleRange i) := by
  apply lt_of_lt_of_le _ (s.property _)
  change i.val < ((s.val 0).cycleRange i).val
  rw [Fin.coe_cycleRange_of_lt hi]
  omega

private def step {b : ℕ} (s : State b) : State b :=
  ⟨s.val ∘ (s.val 0).cycleRange, fun i => by
    rcases lt_trichotomy i (s.val 0) with h | rfl | h
    · exact (lt_shifted s h).le
    · simp [Fin.cycleRange_self]
    · simpa [Fin.cycleRange_of_gt h] using s.property i⟩

/-- The previous leader is the first index carrying its own value in the new row. -/
private theorem head_isLeast (b : ℕ) (s : State b) :
    IsLeast {i | (step s).val i = i} (s.val 0) := by
  refine ⟨by simp [step, Fin.cycleRange_self], ?_⟩
  intro i hi
  exact le_of_not_gt fun h => (lt_shifted s h).ne' hi

private theorem step_injective (b : ℕ) : Function.Injective (step (b := b)) := by
  intro s u he
  have hs := head_isLeast b s
  rw [he] at hs
  have hhead := hs.unique (head_isLeast b u)
  have heq := congrArg Subtype.val he
  change s.val ∘ (s.val 0).cycleRange = u.val ∘ (u.val 0).cycleRange at heq
  rw [hhead] at heq
  exact Subtype.ext ((u.val 0).cycleRange.surjective.injective_comp_right heq)

private theorem cap_throwback (b : ℕ) (s : ℕ → ℕ) (hs : ∀ i, i ≤ s i) :
    cap b (throwback id s) (index_le_throwback hs) = step (cap b s hs) := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  let head := (cap b s hs).val 0
  have hh : head.val = min (s 0) b := rfl
  change min (throwback id s i) b = min (s (head.cycleRange i)) b
  rcases lt_trichotomy i head with h | rfl | h
  · rw [Fin.coe_cycleRange_of_lt h]
    have hi : i.val < s 0 := lt_of_lt_of_le h (min_le_left _ _ : head.val ≤ s 0)
    simp [throwback, hi]
  · rw [Fin.cycleRange_self]
    have := hs (head.val + 1)
    simp only [throwback, id_eq, Fin.val_zero]
    split_ifs <;> omega
  · rw [Fin.cycleRange_of_gt h]
    have hi : s 0 < i.val := by
      have : head.val < i.val := h
      omega
    simp [throwback, hi.not_gt, hi.ne']

/-- Every capped sequence of leaders is periodic starting at time zero. -/
private theorem periodic_cap (b : ℕ) (X : ℕ → ℕ) (hX : ∀ i, i ≤ X i) :
    ∃ p > 0, Function.Periodic (fun n => min (throwbackSequence X n) b) p := by
  let row (n : ℕ) := (throwback id)^[n] X
  have valid (n : ℕ) : ∀ i, i ≤ row n i := by
    induction n with
    | zero => exact hX
    | succ n ih =>
      simpa only [row, Function.iterate_succ_apply'] using index_le_throwback ih
  have orbit (n : ℕ) : cap b (row n) (valid n) = step^[n] (cap b X hX) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa only [row, Function.iterate_succ_apply', ← ih] using cap_throwback b (row n) (valid n)
  obtain ⟨p, hp, hper⟩ := Function.mem_periodicPts.mp
    ((step_injective b).mem_periodicPts (cap b X hX))
  refine ⟨p, hp, fun n => ?_⟩
  have same : cap b (row (n + p)) (valid _) = cap b (row n) (valid _) := by
    rw [orbit, orbit, Function.iterate_add_apply, hper.eq]
  exact congrArg (fun s : State b => (s.val 0).val) same

end throwbackSequence_uniformly_recurrent

open throwbackSequence_uniformly_recurrent in
/-- **Throwback sequences of increasing sequences are uniformly recurrent.** Let
$X = (x_0, x_1, \dots)$ be a strictly increasing sequence of positive integers with throwback
sequence $T(X) = (t_0, t_1, \dots)$. Then every block of consecutive terms of $T(X)$ recurs with
bounded gaps: for all natural numbers $i$ and $L$ there is a natural number $G$ such that for
every natural number $m$ there is an index $j$ with $m \le j \le m + G$ and $t_{j+s} = t_{i+s}$
for all $s < L$.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Theorem 7 (`jis-2025-25.5.1-thm-7`). -/
public theorem throwbackSequence_uniformly_recurrent (X : ℕ → ℕ) (hX : StrictMono X)
    (hX0 : 0 < X 0) (i L : ℕ) :
    ∃ G, ∀ m, ∃ j, m ≤ j ∧ j ≤ m + G ∧
      ∀ t < L, throwbackSequence X (j + t) = throwbackSequence X (i + t) := by
  let b := (Finset.range L).sup (fun t => throwbackSequence X (i + t)) + 1
  have below (t : ℕ) (ht : t < L) : throwbackSequence X (i + t) < b :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun t => throwbackSequence X (i + t))
      (Finset.mem_range.mpr ht))
  have hinit (k : ℕ) : k < X k := by
    calc
      k < k + X 0 := Nat.lt_add_of_pos_right hX0
      _ ≤ X k := by simpa using hX.add_le_nat k 0
  obtain ⟨p, hp, hperiod⟩ := periodic_cap b X fun k => (hinit k).le
  refine ⟨i + p, fun m => ?_⟩
  let q := m / p + 1
  have bounds : m ≤ q * p ∧ q * p ≤ m + p := by
    have := Nat.mod_add_div m p
    have := Nat.mod_lt m hp
    dsimp [q]
    rw [Nat.succ_mul, Nat.mul_comm (m / p)]
    omega
  refine ⟨i + q * p, by omega, by omega, fun t ht => ?_⟩
  have he := hperiod.nat_mul q (i + t)
  change min (throwbackSequence X (i + t + q * p)) b = min (throwbackSequence X (i + t)) b at he
  rw [Nat.add_right_comm] at he
  have := below t ht
  omega

end MetaMathlibExt
