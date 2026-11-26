/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.UpperWythoffUnsum
import all MathlibExt.Combinatorics.Enumerative.UpperWythoffUnsum

/-!
# The last unit gap between upper Wythoff unsums

The Fibonacci-block recognizer for unsums also checks whether two consecutive integers
are both unsums. Check each base frame and propagate the check through subdivisions.
The initial frame exempts the integers below 14; the recognizer's offsets start at 2.
-/

namespace MetaMathlibExt

open upperWythoffUnsumPalindrome_head_getLast

private theorem noAdjacent_base :
    ∀ (i : RowIndex) (z : Fin (width 0 (frame i).short)),
      ((frame i).initial = false ∨ 12 ≤ z.val) →
      ¬ (baseMissing (frame i) z.val = true ∧ baseMissing (frame i) (z.val + 1) = true) := by
  decide +kernel

-- Transfer both positions to the same child frame, even when the second position
-- is just beyond the child block: `missing_advance` covers that boundary.
private theorem noAdjacent (n : ℕ) (f : Frame) (hf : Known f) {z : ℕ}
    (hz : z < width n f.short) (hinit : f.initial = false ∨ 12 ≤ z)
    (h₀ : missing n f z) : ¬ missing n f (z + 1) := by
  intro h₁
  induction n generalizing f z with
  | zero =>
    obtain ⟨i, rfl⟩ := hf
    exact noAdjacent_base i ⟨z, hz⟩ hinit ⟨(baseMissing_spec (frame i) z).2 h₀,
      (baseMissing_spec (frame i) (z + 1)).2 h₁⟩
  | succ n ih =>
    obtain ⟨x, hx, i, hi, rfl⟩ := subdivide n f.short hz
    have hi' : i < width n false := by
      have := widthBounds n
      cases x <;> omega
    have hchild : (advance f x).initial = false ∨ 12 ≤ i := by
      cases x
      · simpa [advance, offset] using hinit
      · simp [advance]
    rw [Nat.add_assoc] at h₁
    exact ih (advance f x) (closed f hf x hx) hi hchild
      ((missing_advance n f x (by omega)).1 h₀)
      ((missing_advance n f x (by omega)).1 h₁)

private theorem not_unsum_succ {m : ℕ} (hm : 14 ≤ m) (h : IsUpperWythoffUnsum m) :
    ¬ IsUpperWythoffUnsum (m + 1) := by
  let z := m - 2
  have hwidth : m + 7 < width m false := fibWord_length (m + 7)
  have h₀ : missing m root z := (missing_root m z (by dsimp [z]; omega)).2 <| by
    rwa [show z + 2 = m by dsimp [z]; omega]
  intro h₁
  apply noAdjacent m root root_mem (by change z < width m false; dsimp [z]; omega)
    (Or.inr (by dsimp [z]; omega)) h₀
  apply (missing_root m (z + 1) (by dsimp [z]; omega)).2
  rwa [show z + 1 + 2 = m + 1 by dsimp [z]; omega]

/-- **The last gap of size one between unsums.** Let $a_1 < a_2 < \cdots$ be the unsums
(OEIS A260317), and for $i \ge 0$ let $g_i = a_{i+2} - a_{i+1}$ be the $i$-th gap between
consecutive unsums, counted from zero. Then $g_9 = 1$, and $g_i \ne 1$ for every $i \ge 10$.

Source: Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve
Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8,
Lemma 1 (`jis-2025-25.3.8-lem-1`). -/
public theorem upperWythoffUnsumGap_ne_one :
    upperWythoffUnsumGap 9 = 1 ∧ ∀ i, 10 ≤ i → upperWythoffUnsumGap i ≠ 1 := by
  constructor
  · exact gap_eq 9 (by decide)
  intro i hi hgap
  have h₁₀ : unsum 10 = 14 := nth_unsum (by decide) (by decide +kernel) (by decide +kernel)
  have hm : 14 ≤ unsum i := h₁₀ ▸ (Nat.nth_strictMono infiniteUnsums).monotone hi
  have hnext : unsum (i + 1) = unsum i + 1 := by
    change unsum (i + 1) - unsum i = 1 at hgap
    omega
  exact not_unsum_succ hm (Nat.nth_mem_of_infinite infiniteUnsums i)
    (hnext ▸ Nat.nth_mem_of_infinite infiniteUnsums (i + 1))

end MetaMathlibExt
