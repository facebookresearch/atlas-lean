/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.Algebra.Order.Chebyshev
import Lean.Elab.Tactic.Omega

/-!
# The Plotkin bound

A `q`-ary code of length `n` whose minimum distance `d` exceeds `(1 - 1/q) n` has at most
`q d / (q d - (q - 1) n)` codewords. The proof sums the distances over all ordered pairs of
codewords in two ways: each distinct pair contributes at least `d`, while in each coordinate at
most a `1 - 1/q` fraction of the `|C|²` ordered pairs disagree (Cauchy–Schwarz on the symbol
counts).

## Relation to `MathlibExt.Combinatorics.Coding.Plotkin`

That module proves the binary case by the same double count, as
`MathlibExt.Combinatorics.Coding.Plotkin.plotkin_bound`: `|C| ≤ 2d / (2d - n)` in `ℝ` for codes
`Fin n → Fin 2` with `n < 2d`. `card_mul_le` here covers every finite alphabet and avoids division.

## References

* M. Plotkin, "Binary codes with specified minimum distance", *IRE Transactions on Information
  Theory* 6 (1960), 445–450.
* V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025,
  Theorem 4.4.1 (part 2).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.PlotkinBound

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- **Disagreeing pairs in one coordinate.** For a code `C` over an alphabet with `q` letters and
a coordinate `j`, at most a `1 - 1/q` fraction of the `|C|²` ordered pairs of codewords disagree
at `j`: `q · #{(c, c') ∈ C² : c j ≠ c' j} ≤ (q - 1) |C|²`. -/
theorem card_mul_sum_ne_le (C : Finset (Fin n → α)) (j : Fin n) :
    Fintype.card α * ∑ c ∈ C, ∑ c' ∈ C, (if c j ≠ c' j then (1 : ℕ) else 0) ≤
      (Fintype.card α - 1) * C.card ^ 2 := by
  classical
  set m : α → ℕ := fun a => (C.filter fun c => c j = a).card with hm
  -- Agreeing pairs are the sum of the squared symbol counts.
  have hagree : ∑ c ∈ C, ∑ c' ∈ C, (if c j = c' j then (1 : ℕ) else 0) = ∑ a, m a ^ 2 := by
    have : ∀ a, m a ^ 2 =
        ∑ c ∈ C, ∑ c' ∈ C, (if c j = a then (if c' j = a then (1 : ℕ) else 0) else 0) := by
      intro a
      simp only [hm, card_filter, sq, sum_mul_sum]
      refine sum_congr rfl fun c _ => sum_congr rfl fun c' _ => ?_
      split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_comm (s := univ) (t := C)]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm (s := univ) (t := C)]
    apply Finset.sum_congr rfl
    intro c' _
    rw [sum_ite_eq]
    simp [eq_comm]
  have hsum : ∑ a, m a = C.card :=
    (card_eq_sum_card_fiberwise (s := C) (f := fun c => c j) (t := univ)
      fun _ _ => mem_univ _).symm
  have hCS : (∑ a, m a) ^ 2 ≤ Fintype.card α * ∑ a, m a ^ 2 := by
    simpa [card_univ] using sq_sum_le_card_mul_sum_sq (s := (univ : Finset α)) (f := m)
  have htotal : ∑ c ∈ C, ∑ c' ∈ C, (if c j ≠ c' j then (1 : ℕ) else 0) +
      ∑ c ∈ C, ∑ c' ∈ C, (if c j = c' j then (1 : ℕ) else 0) = C.card ^ 2 := by
    rw [← sum_add_distrib, sq, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun c _ => ?_
    rw [← sum_add_distrib]
    rw [sum_congr rfl (fun c' _ => (by split_ifs <;> simp_all :
      (if c j ≠ c' j then (1 : ℕ) else 0) + (if c j = c' j then 1 else 0) = 1)),
      sum_const, smul_eq_mul, mul_one]
  rw [hsum] at hCS
  rw [hagree] at htotal
  have hq : 1 ≤ Fintype.card α ∨ C.card = 0 := by
    rcases Nat.eq_zero_or_pos C.card with h | h
    · exact Or.inr h
    · left
      obtain ⟨c, hc⟩ := card_pos.mp h
      exact Fintype.card_pos_iff.mpr ⟨c j⟩
  rcases hq with hq | hC0
  · have e : (Fintype.card α - 1) * C.card ^ 2 + C.card ^ 2 = Fintype.card α * C.card ^ 2 := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hq]
    nlinarith
  · rw [card_eq_zero.mp hC0]; simp

/-- **Plotkin bound.** Let `C` be a code of length `n` over an alphabet with `q` letters whose
distinct codewords are at Hamming distance at least `d`, where `q d > (q - 1) n`. Then
`|C| · (q d - (q - 1) n) ≤ q d`, that is `|C| ≤ q d / (q d - (q - 1) n)`.

This is part 2 of Theorem 4.4.1 of Guruswami, Rudra and Sudan, *Essential Coding Theory* (draft
of August 26, 2025), stated there for `d > (1 - 1/q) n`; it is proved here by the classical
averaging argument rather than their geometric lemma. Source: M. Plotkin, "Binary codes with
specified minimum distance", *IRE Transactions on Information Theory* 6 (1960), 445–450. -/
theorem card_mul_le (C : Finset (Fin n → α)) {d : ℕ}
    (hdist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hd : (Fintype.card α - 1) * n < Fintype.card α * d) :
    C.card * (Fintype.card α * d - (Fintype.card α - 1) * n) ≤ Fintype.card α * d := by
  classical
  set q := Fintype.card α with hq
  set M := C.card with hM
  -- Sum of all pairwise distances, computed coordinate by coordinate.
  set S := ∑ c ∈ C, ∑ c' ∈ C, hammingDist c c' with hS
  have hScoord : S = ∑ j, ∑ c ∈ C, ∑ c' ∈ C, (if c j ≠ c' j then (1 : ℕ) else 0) := by
    simp only [hS, hammingDist, card_filter]
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm (s := C) (t := univ))]
    exact Finset.sum_comm
  have hup : q * S ≤ n * ((q - 1) * M ^ 2) := by
    rw [hScoord, mul_sum]
    calc ∑ j, q * ∑ c ∈ C, ∑ c' ∈ C, (if c j ≠ c' j then (1 : ℕ) else 0)
        ≤ ∑ _j : Fin n, (q - 1) * M ^ 2 := sum_le_sum fun j _ => card_mul_sum_ne_le C j
      _ = n * ((q - 1) * M ^ 2) := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  have hlow : M * ((M - 1) * d) ≤ S := by
    rw [hS, hM, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun c hc => ?_
    rw [← add_sum_erase C _ hc, hammingDist_self, zero_add]
    calc (C.card - 1) * d = (C.erase c).card • d := by rw [card_erase_of_mem hc, smul_eq_mul]
      _ ≤ ∑ c' ∈ C.erase c, hammingDist c c' :=
          card_nsmul_le_sum _ _ _ fun c' hc' => hdist c hc c' (mem_of_mem_erase hc')
            (ne_of_mem_erase hc').symm
  -- Combine: `q M (M - 1) d ≤ (q - 1) n M²`, so `q (M - 1) d ≤ (q - 1) n M`.
  rcases Nat.eq_zero_or_pos M with h0 | hMpos
  · rw [h0]; simp
  have hkey : q * ((M - 1) * d) ≤ n * ((q - 1) * M) := by
    have h1 : M * (q * ((M - 1) * d)) ≤ M * (n * ((q - 1) * M)) := by
      calc M * (q * ((M - 1) * d)) = q * (M * ((M - 1) * d)) := by ring
        _ ≤ q * S := Nat.mul_le_mul_left _ hlow
        _ ≤ n * ((q - 1) * M ^ 2) := hup
        _ = M * (n * ((q - 1) * M)) := by ring
    exact Nat.le_of_mul_le_mul_left h1 hMpos
  -- Integer arithmetic.
  have hz : (M : ℤ) * ((q : ℤ) * d - ((q : ℤ) - 1) * n) ≤ (q : ℤ) * d := by
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · rw [h] at hd; simp at hd
      · exact h
    have hk : ((q * ((M - 1) * d) : ℕ) : ℤ) ≤ ((n * ((q - 1) * M) : ℕ) : ℤ) := by
      exact_mod_cast hkey
    push_cast [Nat.cast_sub hq1, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hMpos.ne')] at hk
    nlinarith
  have hsub : ((q * d - (q - 1) * n : ℕ) : ℤ) = (q : ℤ) * d - ((q : ℤ) - 1) * n := by
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · rw [h] at hd; simp at hd
      · exact h
    rw [Nat.cast_sub hd.le]; push_cast [Nat.cast_sub hq1]; ring
  have : ((M * (q * d - (q - 1) * n) : ℕ) : ℤ) ≤ ((q * d : ℕ) : ℤ) := by
    push_cast [hsub]
    exact hz
  exact_mod_cast this

end MathlibExt.Combinatorics.Coding.PlotkinBound
