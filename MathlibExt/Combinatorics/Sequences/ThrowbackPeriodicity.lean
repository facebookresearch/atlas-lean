/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Sequences.ThrowbackSequences
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Finset.Card

/-!
# Periodicity of partial placement sequences

A shift by one period of a placement changes the signed vacancy count by a constant.
Repeating that shift a suitable number of times preserves the next placement as well.
-/

namespace MetaMathlibExt

namespace partialPlacement_periodic

private def openCount (P : ℤ → Option ℕ) (s z : ℤ) : ℤ :=
  (((Finset.Ico s z).filter fun w => P w = none).card : ℤ) -
    (((Finset.Ico z s).filter fun w => P w = none).card : ℤ)

private theorem openCount_succ (P : ℤ → Option ℕ) (s z : ℤ) :
    openCount P s (z + 1) = openCount P s z + (if P z = none then 1 else 0) := by
  have card_insert (t : Finset ℤ) (hz : z ∉ t) :
      (((insert z t).filter fun w => P w = none).card : ℤ) =
        ((t.filter fun w => P w = none).card : ℤ) + (if P z = none then 1 else 0) := by
    rw [Finset.filter_insert]
    split_ifs
    · rw [Finset.card_insert_of_notMem (fun h => hz (Finset.mem_filter.mp h).1)]
      simp
    · simp
  unfold openCount
  by_cases hs : s ≤ z
  · have hIco : Finset.Ico s (z + 1) = insert z (Finset.Ico s z) := by
      ext w
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hIco, card_insert _ (by simp), Finset.Ico_eq_empty_of_le hs,
      Finset.Ico_eq_empty_of_le (show s ≤ z + 1 by omega)]
    simp
  · -- Below the anchor, the step removes `z` from the interval counted negatively.
    have hIco : Finset.Ico z s = insert z (Finset.Ico (z + 1) s) := by
      ext w
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hz : z ∉ Finset.Ico (z + 1) s := by simp [Finset.mem_Ico]
    rw [hIco, card_insert _ hz, Finset.Ico_eq_empty_of_le (show z ≤ s by omega),
      Finset.Ico_eq_empty_of_le (show z + 1 ≤ s by omega)]
    omega

private theorem openCount_add_mul_period {P : ℤ → Option ℕ} {p : ℤ} (s : ℤ)
    (hp : Function.Periodic P p) :
    ∃ C : ℤ, ∀ (k : ℕ) (z : ℤ), openCount P s (z + k * p) = openCount P s z + k * C := by
  -- The two unit increments cancel, so the difference over one period is constant.
  have hdiff : Function.Periodic (fun z => openCount P s (z + p) - openCount P s z) 1 := by
    intro z
    change openCount P s (z + 1 + p) - openCount P s (z + 1) =
      openCount P s (z + p) - openCount P s z
    rw [add_right_comm z 1 p, openCount_succ P s (z + p), openCount_succ P s z, hp z]
    omega
  let C := openCount P s p - openCount P s 0
  have hshift (z : ℤ) : openCount P s (z + p) = openCount P s z + C := by
    have hz : openCount P s (z + p) - openCount P s z = C := by
      simpa [C] using hdiff.int_mul_eq z
    omega
  refine ⟨C, fun k z => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hshift, ih, add_mul, one_mul, add_assoc]

end partialPlacement_periodic

open partialPlacement_periodic in
/-- **Partial placement sequences are periodic.** Let $X = (x_0, x_1, \dots)$ be a strictly
increasing sequence of positive integers and let $n \ge 0$. Then the partial placement sequence
$P_n(X)$ is periodic: there is an integer $p > 0$ such that for every position
$z \in \mathbb{Z}$, the positions $z + p$ and $z$ of $P_n(X)$ are either both empty or hold the
same term.

Source: Jesiah Darnell and Benjamin F. Dribus, *Throwback Sequences of Positive Integers*,
Journal of Integer Sequences 28 (2025), Article 25.5.1, Lemma 6 (`jis-2025-25.5.1-lem-6`). -/
public theorem partialPlacement_periodic (X : ℕ → ℕ) (hX : StrictMono X)
    (hX0 : 0 < X 0) (n : ℕ) :
    ∃ p : ℤ, 0 < p ∧ ∀ z, partialPlacement X n (z + p) = partialPlacement X n z := by
  have hindex (i : ℕ) : i < X i := by
    induction i with
    | zero => exact hX0
    | succ i ih => exact (Nat.succ_le_of_lt ih).trans_lt (hX (Nat.lt_succ_self i))
  induction n with
  | zero =>
    refine ⟨(X 0 : ℤ) + 1, by omega, fun z => ?_⟩
    simp only [partialPlacement, dvd_add_self_right]
  | succ n ih =>
    obtain ⟨p, hp, hP⟩ := ih
    let P := partialPlacement X n
    let s : ℤ := (sInf {i : ℕ | P i = none} : ℕ)
    let d : ℤ := (X (n + 1) : ℤ) - (n + 1) + 1
    have hd : 0 < d := by dsimp [d]; have := hindex (n + 1); omega
    have hperiod : Function.Periodic P p := hP
    obtain ⟨C, hcount⟩ := openCount_add_mul_period s hperiod
    refine ⟨d * p, mul_pos hd hp, fun z => ?_⟩
    have hcount' : openCount P s (z + d * p) = openCount P s z + d * C := by
      simpa only [Int.toNat_of_nonneg hd.le] using hcount d.toNat z
    have hdvd : d ∣ openCount P s (z + d * p) ↔ d ∣ openCount P s z := by
      rw [hcount']
      exact dvd_add_left (dvd_mul_right d C)
    simp only [partialPlacement]
    change (if P (z + d * p) = none ∧ d ∣ openCount P s (z + d * p) then some (X (n + 1))
      else P (z + d * p)) = (if P z = none ∧ d ∣ openCount P s z then some (X (n + 1)) else P z)
    have hP' : P (z + d * p) = P z := hperiod.int_mul d z
    simp only [hP', hdvd]

end MetaMathlibExt
