/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.ListDecoding
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.LinearCombination

/-!
# The q-ary Johnson bound

For a q-ary code of length `n` and minimum distance `d`, every Hamming ball
of radius `e` below the Johnson radius `J_q(d / n)` contains at most
`q * d * n` codewords (Guruswami, Rudra and Sudan, *Essential Coding Theory*,
draft of August 26, 2025, Theorem 7.3.1; the general-alphabet form follows
Guruswami and Sudan, "Extensions to the Johnson bound", 2001, Theorem 1).
The Lean definition is the displayed total formula, which on its classical
domain `2 ≤ q`, `0 ≤ δ`, and `q * δ ≤ q - 1` is the usual Johnson radius.
For `2 ≤ q` and `(q - 1) / q ≤ δ`, the clipped radicand is `0`, so this total
form saturates at `1 - 1 / q`. For every other input, including `q < 2` or
`δ < 0`, the displayed total formula still defines the value, with totalized
division and an unclipped positive radicand when `1 - q * δ / (q - 1)` is
positive, but it carries no Johnson-radius interpretation there. The radius
theorems below are therefore statements about this total function, and on the
classical domain they are the usual Johnson-radius statements.
The integer form `qary_johnson_bound` is the double-counting core; the
remaining declarations turn it into list-decodability statements, the real
Johnson-radius form, and a statement-level nonvacuity family above the radius.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.JohnsonBound

open Finset MathlibExt.Combinatorics.Coding.ListDecoding

/-- This is the total form of the q-ary Johnson radius:
`J_q(δ) = (1 - 1/q)(1 - √(max 0 (1 - qδ/(q - 1))))`.
On the classical domain `2 ≤ q`, `0 ≤ δ`, and `q * δ ≤ q - 1` this is the usual
Johnson radius. For `2 ≤ q` and `(q - 1) / q ≤ δ`, the clipped radicand is `0`,
so this total form saturates at `1 - 1 / q`. For every other input, including
`q < 2` or `δ < 0`, this same total formula still defines the value, with
totalized division and an unclipped positive radicand when `1 - qδ/(q - 1)` is
positive, but it carries no Johnson-radius interpretation there. The radius
theorems below are statements about this total function, and on the classical
domain they are the usual statements. -/
noncomputable def johnsonRadius (q : ℕ) (δ : ℝ) : ℝ :=
  (1 - 1 / (q : ℝ)) * (1 - Real.sqrt (max 0 (1 - q * δ / (q - 1))))

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- **Integer q-ary Johnson bound.** Let `S` be a set of words of length `n` over an
alphabet of size at least `2`, with pairwise Hamming distance at least `d`, all lying in the
radius-`e` Hamming ball around `y`, and satisfying `q * e ≤ (q - 1) * n`. Then the Johnson
gap factor times `S.card` is at most `(q - 1) * n * d`. This is the integer double-counting
core (Guruswami, Rudra and Sudan, *Essential Coding Theory*, draft of August 26, 2025,
Theorem 7.3.1; Guruswami and Sudan, "Extensions to the Johnson bound", 2001, Theorem 1). -/
theorem qary_johnson_bound (S : Finset (Fin n → α)) (y : Fin n → α) {d e : ℕ}
    (hq : 2 ≤ Fintype.card α)
    (hqe : Fintype.card α * e ≤ (Fintype.card α - 1) * n)
    (hdist : ∀ c₁ ∈ S, ∀ c₂ ∈ S, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hball : ∀ c ∈ S, hammingDist y c ≤ e) :
    (S.card : ℤ) * (((Fintype.card α : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2 -
      ((Fintype.card α : ℤ) - 1) * n * ((n : ℤ) - d)) ≤
      ((Fintype.card α : ℤ) - 1) * n * d := by
  -- Agreement count: filter-card equals `n - dist` (mirrors `card_filter_eq`).
  have hce : ∀ c₁ c₂ : Fin n → α,
      ((Finset.univ.filter (fun j => c₁ j = c₂ j)).card : ℤ) =
        (n : ℤ) - (hammingDist c₁ c₂ : ℤ) := by
    intro c₁ c₂
    have hnat : (Finset.univ.filter (fun j => c₁ j = c₂ j)).card =
        n - hammingDist c₁ c₂ := by
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (fun j => c₁ j = c₂ j)
      rw [Finset.card_univ, Fintype.card_fin] at hpart
      have hdist : hammingDist c₁ c₂ =
          (Finset.univ.filter (fun j => c₁ j ≠ c₂ j)).card := rfl
      have hcard : (Finset.univ.filter (fun j => ¬c₁ j = c₂ j)).card =
          (Finset.univ.filter (fun j => c₁ j ≠ c₂ j)).card := rfl
      omega
    have hle : hammingDist c₁ c₂ ≤ n := by
      have h := hammingDist_le_card_fintype (x := c₁) (y := c₂)
      rwa [Fintype.card_fin] at h
    rw [hnat, Nat.cast_sub hle]
  have hq1N : 1 ≤ Fintype.card α := by omega
  have hnn : (0 : ℤ) ≤ (n : ℤ) := Nat.cast_nonneg _
  have hq1nn : (0 : ℤ) ≤ (Fintype.card α : ℤ) - 1 := by
    have h1 : (1 : ℤ) ≤ Fintype.card α := by
      exact_mod_cast (by omega : 1 ≤ Fintype.card α)
    linarith
  have hcast_qm1 : (((Fintype.card α - 1) * n : ℕ) : ℤ) =
      ((Fintype.card α : ℤ) - 1) * n := by
    push_cast
    rw [Nat.cast_sub hq1N, Nat.cast_one]
  have hqeZ : (Fintype.card α : ℤ) * e ≤ ((Fintype.card α : ℤ) - 1) * n := by
    rw [← hcast_qm1]
    exact_mod_cast hqe
  have hqT0 : (n : ℤ) * S.card ≤
      (Fintype.card α : ℤ) * ((S.card : ℤ) * ((n : ℤ) - e)) := by
    have hMnn : (0 : ℤ) ≤ (S.card : ℤ) := Nat.cast_nonneg _
    have hprod : (0 : ℤ) ≤ (S.card : ℤ) *
        ((((Fintype.card α : ℤ) - 1) * n) - (Fintype.card α : ℤ) * e) :=
      mul_nonneg hMnn (by linarith [hqeZ])
    linarith [hprod]
  -- Per-coordinate sum over the alphabet.
  have hsum_alpha : ∀ j : Fin n,
      (∑ a ∈ (Finset.univ : Finset α),
        ((S.filter (fun c => c j = a)).card : ℤ)) = (S.card : ℤ) := by
    intro j
    have h := Finset.card_eq_sum_card_fiberwise (s := S)
      (t := (Finset.univ : Finset α)) (f := fun c => c j)
      (fun x _ => Finset.mem_univ (x j))
    have hnat : (∑ b ∈ (Finset.univ : Finset α),
        (S.filter (fun c => c j = b)).card) = S.card := h.symm
    exact_mod_cast hnat
  -- Agreement sum: per-coordinate agreements add up over codewords.
  have hagree : (∑ j ∈ (Finset.univ : Finset (Fin n)),
        ((S.filter (fun c => c j = y j)).card : ℤ)) =
      ∑ c ∈ S, ((n : ℤ) - (hammingDist y c : ℤ)) := by
    simp_rw [Finset.natCast_card_filter]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))]
    simp_rw [← Finset.natCast_card_filter]
    have hper : ∀ c ∈ S,
        ((Finset.univ.filter (fun j => c j = y j)).card : ℤ) =
          (n : ℤ) - (hammingDist y c : ℤ) := by
      intro c _
      rw [hce c y, hammingDist_comm c y]
    exact Finset.sum_congr rfl hper
  -- Pair-count identity, via per-entry expansion.
  have hstep : ∀ j : Fin n, ∀ a : α,
      (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2 =
        ∑ c₁ ∈ S, ∑ c₂ ∈ S,
          ((if c₁ j = a then (1 : ℤ) else 0) *
            (if c₂ j = a then (1 : ℤ) else 0)) := by
    intro j a
    rw [pow_two, Finset.natCast_card_filter, Finset.sum_mul_sum]
  have heval : ∀ (j : Fin n) (c₁ c₂ : Fin n → α),
      (∑ a ∈ (Finset.univ : Finset α),
        ((if c₁ j = a then (1 : ℤ) else 0) *
          (if c₂ j = a then (1 : ℤ) else 0))) =
        (if c₁ j = c₂ j then (1 : ℤ) else 0) := by
    intro j c₁ c₂
    by_cases h : c₁ j = c₂ j
    · rw [if_pos h, ← h]
      have hterm : ∀ a : α,
          ((if c₁ j = a then (1 : ℤ) else 0) *
            (if c₁ j = a then (1 : ℤ) else 0)) =
            (if c₁ j = a then (1 : ℤ) else 0) := by
        intro a
        by_cases ha : c₁ j = a <;> simp [ha]
      simp_rw [hterm]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ (c₁ j))]
    · rw [if_neg h]
      have h0 : ∀ a ∈ (Finset.univ : Finset α),
          ((if c₁ j = a then (1 : ℤ) else 0) *
            (if c₂ j = a then (1 : ℤ) else 0)) = 0 := by
        intro a _
        by_cases ha : c₁ j = a
        · rw [if_pos ha, if_neg (fun h2 => h (ha.trans h2.symm)), mul_zero]
        · rw [if_neg ha, zero_mul]
      calc (∑ a ∈ (Finset.univ : Finset α),
              ((if c₁ j = a then (1 : ℤ) else 0) *
                (if c₂ j = a then (1 : ℤ) else 0)))
            = ∑ _a ∈ (Finset.univ : Finset α), (0 : ℤ) :=
              Finset.sum_congr rfl h0
        _ = 0 := Finset.sum_const_zero
  have hinner : ∀ c₁ ∈ S,
      (∑ j ∈ (Finset.univ : Finset (Fin n)), ∑ c₂ ∈ S,
        (if c₁ j = c₂ j then (1 : ℤ) else 0)) =
        ∑ c₂ ∈ S, ((n : ℤ) - (hammingDist c₁ c₂ : ℤ)) := by
    intro c₁ _
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))]
    have hper2 : ∀ c₂ ∈ S,
        (∑ j ∈ (Finset.univ : Finset (Fin n)),
          (if c₁ j = c₂ j then (1 : ℤ) else 0)) =
          (n : ℤ) - (hammingDist c₁ c₂ : ℤ) := by
      intro c₂ _
      rw [← Finset.natCast_card_filter]
      exact hce c₁ c₂
    exact Finset.sum_congr rfl hper2
  have hpair : (∑ j ∈ (Finset.univ : Finset (Fin n)),
        ∑ a ∈ (Finset.univ : Finset α),
          (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2) =
      ∑ c₁ ∈ S, ∑ c₂ ∈ S, ((n : ℤ) - (hammingDist c₁ c₂ : ℤ)) := by
    simp_rw [hstep]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset α))]
    simp_rw [heval]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))]
    exact Finset.sum_congr rfl hinner
  -- Total agreements are at least `M * (n - e)`.
  have hTge : (S.card : ℤ) * ((n : ℤ) - e) ≤
      ∑ j ∈ (Finset.univ : Finset (Fin n)),
        ((S.filter (fun c => c j = y j)).card : ℤ) := by
    rw [hagree]
    have h1 : (∑ c ∈ S, ((n : ℤ) - e)) ≤
        ∑ c ∈ S, ((n : ℤ) - (hammingDist y c : ℤ)) := by
      apply Finset.sum_le_sum
      intro c hc
      have hce := hball c hc
      have hle : (hammingDist y c : ℤ) ≤ (e : ℤ) := by exact_mod_cast hce
      linarith
    have h2 : (∑ c ∈ S, ((n : ℤ) - e)) = (S.card : ℤ) * ((n : ℤ) - e) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← h2]
    exact h1
  have hcard_erase : ∀ j : Fin n,
      ((Finset.univ : Finset α).erase (y j)).card = Fintype.card α - 1 := by
    intro j
    rw [Finset.card_erase_of_mem (Finset.mem_univ (y j)), Finset.card_univ]
  -- Per-coordinate Cauchy-Schwarz over the off-center symbols.
  have hCSj : ∀ j : Fin n,
      ((Fintype.card α : ℤ) - 1) *
          (((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2 +
        ((S.card : ℤ) - ((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2 ≤
        ((Fintype.card α : ℤ) - 1) *
          (∑ a ∈ (Finset.univ : Finset α),
            (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2) := by
    intro j
    have hCS := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset α).erase (y j))
      (f := fun a => (((S.filter (fun c => c j = a)).card : ℕ) : ℤ))
    rw [hcard_erase j, Nat.cast_sub hq1N, Nat.cast_one] at hCS
    have hsplit : (((S.filter (fun c => c j = y j)).card : ℤ)) +
          (∑ a ∈ (Finset.univ : Finset α).erase (y j),
            ((S.filter (fun c => c j = a)).card : ℤ)) =
          ∑ a ∈ (Finset.univ : Finset α),
            ((S.filter (fun c => c j = a)).card : ℤ) :=
      Finset.add_sum_erase (Finset.univ : Finset α)
        (fun a => ((S.filter (fun c => c j = a)).card : ℤ))
        (Finset.mem_univ (y j))
    have htot := hsum_alpha j
    have hE : (∑ a ∈ (Finset.univ : Finset α).erase (y j),
          ((S.filter (fun c => c j = a)).card : ℤ)) =
        (S.card : ℤ) - ((S.filter (fun c => c j = y j)).card : ℤ) := by
      linarith [hsplit, htot]
    have hCS' : ((∑ a ∈ (Finset.univ : Finset α).erase (y j),
            ((S.filter (fun c => c j = a)).card : ℤ))) ^ 2 ≤
          ((Fintype.card α : ℤ) - 1) *
            (∑ a ∈ (Finset.univ : Finset α).erase (y j),
              (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2) := hCS
    rw [hE] at hCS'
    have hsplit2 : (∑ a ∈ (Finset.univ : Finset α),
            (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2) =
          ((((S.filter (fun c => c j = y j)).card : ℕ) : ℤ)) ^ 2 +
            (∑ a ∈ (Finset.univ : Finset α).erase (y j),
              (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2) :=
      (Finset.add_sum_erase (Finset.univ : Finset α)
        (fun a => (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2)
        (Finset.mem_univ (y j))).symm
    rw [hsplit2]
    linarith [hCS']
  -- Cauchy-Schwarz over coordinates, twice.
  have hCSn1 : ((∑ j ∈ (Finset.univ : Finset (Fin n)),
          ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2 ≤
        (n : ℤ) * (∑ j ∈ (Finset.univ : Finset (Fin n)),
          (((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => (((S.filter (fun c => c j = y j)).card : ℕ) : ℤ))
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hCSn2 : (((n : ℤ) * S.card -
        (∑ j ∈ (Finset.univ : Finset (Fin n)),
          ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2) ≤
        (n : ℤ) * (∑ j ∈ (Finset.univ : Finset (Fin n)),
          (((S.card : ℤ) - ((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2)) := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j =>
        ((S.card : ℤ) - ((S.filter (fun c => c j = y j)).card : ℤ)))
    rw [Finset.card_univ, Fintype.card_fin] at h
    have hsum : (∑ j ∈ (Finset.univ : Finset (Fin n)),
          ((S.card : ℤ) - ((S.filter (fun c => c j = y j)).card : ℤ))) =
        (n : ℤ) * S.card -
          (∑ j ∈ (Finset.univ : Finset (Fin n)),
            ((S.filter (fun c => c j = y j)).card : ℤ)) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin]
    simp only [hsum] at h
    exact h
  -- Monotonicity of the quadratic in the total agreements.
  have hmono : (S.card : ℤ) ^ 2 *
        (((Fintype.card α : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2) ≤
        ((Fintype.card α : ℤ) - 1) *
            (∑ j ∈ (Finset.univ : Finset (Fin n)),
              ((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2 +
          (((n : ℤ) * S.card -
            (∑ j ∈ (Finset.univ : Finset (Fin n)),
              ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2) := by
    have hTT0 : (S.card : ℤ) * ((n : ℤ) - e) ≤
        ∑ j ∈ (Finset.univ : Finset (Fin n)),
          ((S.filter (fun c => c j = y j)).card : ℤ) := hTge
    have hqnn : (0 : ℤ) ≤ (Fintype.card α : ℤ) := Nat.cast_nonneg _
    have ht1 : (0 : ℤ) ≤ (Fintype.card α : ℤ) *
        ((∑ j ∈ (Finset.univ : Finset (Fin n)),
            ((S.filter (fun c => c j = y j)).card : ℤ)) -
          (S.card : ℤ) * ((n : ℤ) - e)) :=
      mul_nonneg hqnn (by linarith [hTT0])
    have ht2 : (0 : ℤ) ≤ 2 *
        (((Fintype.card α : ℤ) * ((S.card : ℤ) * ((n : ℤ) - e))) -
          (n : ℤ) * (S.card : ℤ)) := by
      linarith [hqT0]
    have hdiff : (0 : ℤ) ≤
        (((∑ j ∈ (Finset.univ : Finset (Fin n)),
              ((S.filter (fun c => c j = y j)).card : ℤ)) -
            (S.card : ℤ) * ((n : ℤ) - e))) *
          ((Fintype.card α : ℤ) *
              ((∑ j ∈ (Finset.univ : Finset (Fin n)),
                  ((S.filter (fun c => c j = y j)).card : ℤ)) +
                (S.card : ℤ) * ((n : ℤ) - e)) -
            2 * (n : ℤ) * (S.card : ℤ)) := by
      have hA : (0 : ℤ) ≤
          (∑ j ∈ (Finset.univ : Finset (Fin n)),
            ((S.filter (fun c => c j = y j)).card : ℤ)) -
            (S.card : ℤ) * ((n : ℤ) - e) := by
        linarith [hTT0]
      have hB : (0 : ℤ) ≤ (Fintype.card α : ℤ) *
            ((∑ j ∈ (Finset.univ : Finset (Fin n)),
                ((S.filter (fun c => c j = y j)).card : ℤ)) +
              (S.card : ℤ) * ((n : ℤ) - e)) -
            2 * (n : ℤ) * (S.card : ℤ) := by
        linarith [ht1, ht2]
      exact mul_nonneg hA hB
    have hexpand :
        (((Fintype.card α : ℤ) - 1) *
              (∑ j ∈ (Finset.univ : Finset (Fin n)),
                ((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2 +
            (((n : ℤ) * S.card -
              (∑ j ∈ (Finset.univ : Finset (Fin n)),
                ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2)) -
          (((Fintype.card α : ℤ) - 1) * ((S.card : ℤ) * ((n : ℤ) - e)) ^ 2 +
            (((n : ℤ) * S.card - (S.card : ℤ) * ((n : ℤ) - e)) ^ 2)) =
          (((∑ j ∈ (Finset.univ : Finset (Fin n)),
                ((S.filter (fun c => c j = y j)).card : ℤ)) -
              (S.card : ℤ) * ((n : ℤ) - e))) *
            ((Fintype.card α : ℤ) *
                ((∑ j ∈ (Finset.univ : Finset (Fin n)),
                    ((S.filter (fun c => c j = y j)).card : ℤ)) +
                  (S.card : ℤ) * ((n : ℤ) - e)) -
              2 * (n : ℤ) * (S.card : ℤ)) := by
      ring
    have hT0val :
        (((Fintype.card α : ℤ) - 1) * ((S.card : ℤ) * ((n : ℤ) - e)) ^ 2 +
          (((n : ℤ) * S.card - (S.card : ℤ) * ((n : ℤ) - e)) ^ 2)) =
          (S.card : ℤ) ^ 2 *
            (((Fintype.card α : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2) := by
      ring
    linarith [hdiff, hexpand, hT0val]
  -- Summing the per-coordinate bound.
  have hsumF : (∑ j ∈ (Finset.univ : Finset (Fin n)),
          (((Fintype.card α : ℤ) - 1) *
              (((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2 +
            ((((S.card : ℤ) - ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2))) ≤
        ((Fintype.card α : ℤ) - 1) *
          (∑ j ∈ (Finset.univ : Finset (Fin n)),
            ∑ a ∈ (Finset.univ : Finset α),
              (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2) := by
    have hle : (∑ j ∈ (Finset.univ : Finset (Fin n)),
            (((Fintype.card α : ℤ) - 1) *
                (((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2 +
              ((((S.card : ℤ) - ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2))) ≤
          (∑ j ∈ (Finset.univ : Finset (Fin n)),
            (((Fintype.card α : ℤ) - 1) *
              (∑ a ∈ (Finset.univ : Finset α),
                (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2))) := by
      apply Finset.sum_le_sum
      intro j _
      exact hCSj j
    have hfactor : (∑ j ∈ (Finset.univ : Finset (Fin n)),
            (((Fintype.card α : ℤ) - 1) *
              (∑ a ∈ (Finset.univ : Finset α),
                (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2))) =
          ((Fintype.card α : ℤ) - 1) *
            (∑ j ∈ (Finset.univ : Finset (Fin n)),
              ∑ a ∈ (Finset.univ : Finset α),
                (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2) := by
      rw [Finset.mul_sum]
    rw [← hfactor]
    exact hle
  have hCSn : ((Fintype.card α : ℤ) - 1) *
          (∑ j ∈ (Finset.univ : Finset (Fin n)),
            ((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2 +
        (((n : ℤ) * S.card -
          (∑ j ∈ (Finset.univ : Finset (Fin n)),
            ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2) ≤
        (n : ℤ) * (∑ j ∈ (Finset.univ : Finset (Fin n)),
          (((Fintype.card α : ℤ) - 1) *
              (((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2 +
            ((((S.card : ℤ) - ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2))) := by
    have hmul1 : ((Fintype.card α : ℤ) - 1) *
            (∑ j ∈ (Finset.univ : Finset (Fin n)),
              ((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2 ≤
          ((Fintype.card α : ℤ) - 1) *
            ((n : ℤ) * (∑ j ∈ (Finset.univ : Finset (Fin n)),
              (((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hCSn1 hq1nn
    have hexp : (n : ℤ) * (∑ j ∈ (Finset.univ : Finset (Fin n)),
            (((Fintype.card α : ℤ) - 1) *
                (((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2 +
              ((((S.card : ℤ) - ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2))) =
          ((Fintype.card α : ℤ) - 1) *
              ((n : ℤ) * (∑ j ∈ (Finset.univ : Finset (Fin n)),
                (((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2)) +
            (n : ℤ) * (∑ j ∈ (Finset.univ : Finset (Fin n)),
              ((((S.card : ℤ) - ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    have h1 : ((Fintype.card α : ℤ) - 1) *
            (∑ j ∈ (Finset.univ : Finset (Fin n)),
              ((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2 +
          (((n : ℤ) * S.card -
            (∑ j ∈ (Finset.univ : Finset (Fin n)),
              ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2) ≤
          ((Fintype.card α : ℤ) - 1) *
              ((n : ℤ) * (∑ j ∈ (Finset.univ : Finset (Fin n)),
                (((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2)) +
            (n : ℤ) * (∑ j ∈ (Finset.univ : Finset (Fin n)),
              ((((S.card : ℤ) - ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2)) := by
      linarith [hmul1, hCSn2]
    linarith [h1, hexp]
  -- Per-pair estimate from the distance hypothesis.
  have hterm : ∀ c₁ ∈ S, ∀ c₂ ∈ S,
      ((n : ℤ) - (hammingDist c₁ c₂ : ℤ)) ≤
        ((n : ℤ) - d) + (if c₁ = c₂ then (d : ℤ) else 0) := by
    intro c₁ hc₁ c₂ hc₂
    by_cases h : c₁ = c₂
    · subst h
      rw [if_pos rfl, hammingDist_self, Nat.cast_zero]
      linarith
    · rw [if_neg h]
      have hle : (d : ℤ) ≤ (hammingDist c₁ c₂ : ℤ) := by
        exact_mod_cast hdist c₁ hc₁ c₂ hc₂ h
      linarith
  have hle2 : (∑ c₁ ∈ S, ∑ c₂ ∈ S, ((n : ℤ) - (hammingDist c₁ c₂ : ℤ))) ≤
      (∑ c₁ ∈ S, ∑ c₂ ∈ S,
        (((n : ℤ) - d) + (if c₁ = c₂ then (d : ℤ) else 0))) := by
    apply Finset.sum_le_sum
    intro c₁ hc₁
    apply Finset.sum_le_sum
    intro c₂ hc₂
    exact hterm c₁ hc₁ c₂ hc₂
  have heq2 : (∑ c₁ ∈ S, ∑ c₂ ∈ S,
        (((n : ℤ) - d) + (if c₁ = c₂ then (d : ℤ) else 0))) =
      (S.card : ℤ) ^ 2 * ((n : ℤ) - d) + (S.card : ℤ) * d := by
    have hinner : ∀ c₁ ∈ S,
        (∑ c₂ ∈ S, (((n : ℤ) - d) + (if c₁ = c₂ then (d : ℤ) else 0))) =
          ((S.card : ℤ) * ((n : ℤ) - d) + d) := by
      intro c₁ hc₁
      have hs1 : (∑ c₂ ∈ S, ((n : ℤ) - d)) = (S.card : ℤ) * ((n : ℤ) - d) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hs2 : (∑ c₂ ∈ S, (if c₁ = c₂ then (d : ℤ) else 0)) = (d : ℤ) := by
        rw [Finset.sum_ite_eq, if_pos hc₁]
      rw [Finset.sum_add_distrib]
      simp only [hs1, hs2]
    have houter : (∑ c₁ ∈ S, ∑ c₂ ∈ S,
          (((n : ℤ) - d) + (if c₁ = c₂ then (d : ℤ) else 0))) =
        (∑ c₁ ∈ S, ((S.card : ℤ) * ((n : ℤ) - d) + d)) := by
      apply Finset.sum_congr rfl
      intro c₁ hc₁
      exact hinner c₁ hc₁
    rw [houter, Finset.sum_const, nsmul_eq_mul]
    ring
  have hPbound : (∑ j ∈ (Finset.univ : Finset (Fin n)),
        ∑ a ∈ (Finset.univ : Finset α),
          (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2) ≤
      (S.card : ℤ) ^ 2 * ((n : ℤ) - d) + (S.card : ℤ) * d := by
    linarith [hpair, hle2, heq2]
  have hstep1 : (S.card : ℤ) ^ 2 *
        (((Fintype.card α : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2) ≤
        (n : ℤ) * ((Fintype.card α : ℤ) - 1) *
          (∑ j ∈ (Finset.univ : Finset (Fin n)),
            ∑ a ∈ (Finset.univ : Finset α),
              (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2) := by
    have hmul : (n : ℤ) *
          (∑ j ∈ (Finset.univ : Finset (Fin n)),
            (((Fintype.card α : ℤ) - 1) *
                (((S.filter (fun c => c j = y j)).card : ℤ)) ^ 2 +
              ((((S.card : ℤ) - ((S.filter (fun c => c j = y j)).card : ℤ))) ^ 2))) ≤
          (n : ℤ) * (((Fintype.card α : ℤ) - 1) *
            (∑ j ∈ (Finset.univ : Finset (Fin n)),
              ∑ a ∈ (Finset.univ : Finset α),
                (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsumF hnn
    linarith [hmono, hCSn, hmul]
  have hstep2 : (n : ℤ) * ((Fintype.card α : ℤ) - 1) *
        (∑ j ∈ (Finset.univ : Finset (Fin n)),
          ∑ a ∈ (Finset.univ : Finset α),
            (((S.filter (fun c => c j = a)).card : ℤ)) ^ 2) ≤
        (n : ℤ) * ((Fintype.card α : ℤ) - 1) *
          ((S.card : ℤ) ^ 2 * ((n : ℤ) - d) + (S.card : ℤ) * d) := by
    apply mul_le_mul_of_nonneg_left hPbound
    exact mul_nonneg hnn hq1nn
  by_cases hM : S.card = 0
  · rw [hM, Nat.cast_zero, zero_mul]
    apply mul_nonneg
    · apply mul_nonneg
      · have h1 : (1 : ℤ) ≤ Fintype.card α := by
          exact_mod_cast (by omega : 1 ≤ Fintype.card α)
        linarith
      · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  · have hMposN : 0 < S.card := Nat.pos_of_ne_zero hM
    have hMpos : (0 : ℤ) < (S.card : ℤ) := by exact_mod_cast hMposN
    have hcancel : (S.card : ℤ) *
          ((S.card : ℤ) *
            (((Fintype.card α : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2)) ≤
          (S.card : ℤ) *
            (((n : ℤ) * ((Fintype.card α : ℤ) - 1)) *
              ((S.card : ℤ) * ((n : ℤ) - d) + d)) := by
      linarith [hstep1, hstep2]
    have hdiv : (S.card : ℤ) *
          (((Fintype.card α : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2) ≤
          ((n : ℤ) * ((Fintype.card α : ℤ) - 1)) *
            ((S.card : ℤ) * ((n : ℤ) - d) + d) :=
      le_of_mul_le_mul_left hcancel hMpos
    linarith [hdiv]
/-- **Cardinality form of the q-ary Johnson bound.** Under the hypotheses of
`qary_johnson_bound`, together with the strict integer Johnson inequality `hJ`, conclude
`S.card ≤ (q - 1) * n * d`, where `q` is the alphabet size. -/
theorem card_le_of_qary_johnson (S : Finset (Fin n → α)) (y : Fin n → α) {d e : ℕ}
    (hq : 2 ≤ Fintype.card α)
    (hqe : Fintype.card α * e ≤ (Fintype.card α - 1) * n)
    (hdist : ∀ c₁ ∈ S, ∀ c₂ ∈ S, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hball : ∀ c ∈ S, hammingDist y c ≤ e)
    (hJ : ((Fintype.card α : ℤ) - 1) * n * ((n : ℤ) - d) <
      ((Fintype.card α : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2) :
    S.card ≤ (Fintype.card α - 1) * n * d := by
  by_contra hcon
  push Not at hcon
  have hcore := qary_johnson_bound S y hq hqe hdist hball
  have hq1 : (1 : ℤ) ≤ (Fintype.card α : ℤ) := by
    have h1 : 1 ≤ Fintype.card α := by omega
    exact_mod_cast h1
  have hCnonneg : (0 : ℤ) ≤ ((Fintype.card α : ℤ) - 1) * n * d := by
    apply mul_nonneg
    · apply mul_nonneg
      · linarith
      · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  have hcast : ((((Fintype.card α - 1) * n * d : ℕ)) : ℤ) =
      ((Fintype.card α : ℤ) - 1) * n * d := by
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card α), Nat.cast_one]
  have hlt : ((Fintype.card α : ℤ) - 1) * n * d < (S.card : ℤ) := by
    rw [← hcast]
    exact Nat.cast_lt.mpr hcon
  have hMpos : (0 : ℤ) < (S.card : ℤ) := lt_of_le_of_lt hCnonneg hlt
  have hstep : (S.card : ℤ) * (((Fintype.card α : ℤ) - 1) * ((n : ℤ) - e) ^ 2 +
      (e : ℤ) ^ 2 - ((Fintype.card α : ℤ) - 1) * n * ((n : ℤ) - d)) <
      (S.card : ℤ) * 1 := by
    calc (S.card : ℤ) * (((Fintype.card α : ℤ) - 1) * ((n : ℤ) - e) ^ 2 +
          (e : ℤ) ^ 2 - ((Fintype.card α : ℤ) - 1) * n * ((n : ℤ) - d))
        ≤ ((Fintype.card α : ℤ) - 1) * n * d := hcore
      _ < (S.card : ℤ) := hlt
      _ = (S.card : ℤ) * 1 := by ring
  have hK : ((Fintype.card α : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2 -
      ((Fintype.card α : ℤ) - 1) * n * ((n : ℤ) - d) < 1 :=
    (mul_lt_mul_iff_of_pos_left hMpos).mp hstep
  have hKpos : (0 : ℤ) < ((Fintype.card α : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2 -
      ((Fintype.card α : ℤ) - 1) * n * ((n : ℤ) - d) := by omega
  omega

/-- **List decodability from the integer Johnson conditions.** A code of length `n` and
minimum distance at least `d` over an alphabet of size `q ≥ 2` is list decodable at radius
`e` with list bound `q * d * n`, provided `q * e ≤ (q - 1) * n` and the strict integer
Johnson inequality `hJ` holds. -/
theorem isListDecodable_of_qary_johnson (C : Finset (Fin n → α)) {d e : ℕ}
    (hq : 2 ≤ Fintype.card α)
    (hqe : Fintype.card α * e ≤ (Fintype.card α - 1) * n)
    (hdist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hJ : ((Fintype.card α : ℤ) - 1) * n * ((n : ℤ) - d) <
      ((Fintype.card α : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2) :
    IsListDecodable C e (Fintype.card α * d * n) := by
  intro y
  have hle := card_le_of_qary_johnson (C ∩ Hamming.ball y e) y hq hqe
    (fun c₁ hc₁ c₂ hc₂ hne =>
      hdist c₁ (Finset.mem_inter.mp hc₁).1 c₂ (Finset.mem_inter.mp hc₂).1 hne)
    (fun c hc => Hamming.mem_ball.mp (Finset.mem_inter.mp hc).2)
    hJ
  have h1 : Fintype.card α - 1 ≤ Fintype.card α := Nat.sub_le _ _
  have h2 : (Fintype.card α - 1) * (n * d) ≤ Fintype.card α * (n * d) :=
    mul_le_mul_left h1 (n * d)
  have hcap : (C ∩ Hamming.ball y e).card ≤ Fintype.card α * d * n :=
    calc (C ∩ Hamming.ball y e).card ≤ (Fintype.card α - 1) * n * d := hle
      _ ≤ Fintype.card α * d * n := by linear_combination h2
  convert hcap using 2
  ext c
  simp [Finset.mem_inter, Finset.mem_filter, Hamming.mem_ball, hammingDist_comm, and_comm]

/-- **Real-radius to integer-conditions bridge.** If `e` is strictly below the unnormalized
Johnson radius `J_q(d / n) * n`, then both `q * e < (q - 1) * n` and the strict integer
Johnson inequality used by the q-ary bound hold. -/
theorem qary_johnson_conditions_of_lt_johnsonRadius {q n d e : ℕ} (hq : 2 ≤ q)
    (he : (e : ℝ) < johnsonRadius q ((d : ℝ) / n) * n) :
    q * e < (q - 1) * n ∧
      ((q : ℤ) - 1) * n * ((n : ℤ) - d) < ((q : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2 := by
  by_cases hn : n = 0
  · subst hn
    rw [Nat.cast_zero, mul_zero] at he
    have hnn : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg _
    exfalso
    linarith [he, hnn]
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (by omega : 0 < q)
    have hqn0 : (q : ℝ) ≠ 0 := ne_of_gt hq0
    have h2q : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hJ : johnsonRadius q ((d : ℝ) / (n : ℝ)) =
        (1 - 1 / (q : ℝ)) *
          (1 - Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1)))) := rfl
    have hsqrt_nn : (0 : ℝ) ≤
        Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1))) :=
      Real.sqrt_nonneg _
    have hpart1 : q * e < (q - 1) * n := by
      have h1q : (1 : ℝ) / (q : ℝ) ≤ 1 := by
        rw [div_le_one hq0]
        linarith [h2q]
      have hA : (0 : ℝ) ≤ 1 - 1 / (q : ℝ) := by linarith [h1q]
      have hB : 1 - Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1))) ≤ 1 := by
        linarith [hsqrt_nn]
      have hN : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn0
      have hAN : (0 : ℝ) ≤ (1 - 1 / (q : ℝ)) * (n : ℝ) := mul_nonneg hA hN
      have hB1 : (1 - Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1)))) - 1 ≤ 0 := by
        linarith [hB]
      have hle : johnsonRadius q ((d : ℝ) / (n : ℝ)) * (n : ℝ) ≤
          (1 - 1 / (q : ℝ)) * (n : ℝ) := by
        rw [hJ]
        have h := mul_nonpos_of_nonneg_of_nonpos hAN hB1
        linarith [h]
      have he2 : (e : ℝ) < (1 - 1 / (q : ℝ)) * (n : ℝ) :=
        lt_of_lt_of_le he hle
      have hmul := mul_lt_mul_of_pos_left he2 hq0
      have hfield : (q : ℝ) * ((1 - 1 / (q : ℝ)) * (n : ℝ)) =
          ((q : ℝ) - 1) * (n : ℝ) := by
        field_simp
      have hpart1R : (q : ℝ) * (e : ℝ) < ((q : ℝ) - 1) * (n : ℝ) := by
        linarith [hmul, hfield]
      have hcast : ((((q - 1) * n : ℕ)) : ℝ) = ((q : ℝ) - 1) * (n : ℝ) := by
        push_cast
        rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
      rw [← hcast] at hpart1R
      exact_mod_cast hpart1R
    have hq1_ne : (q : ℝ) - 1 ≠ 0 := by
      have hpos : (0 : ℝ) < (q : ℝ) - 1 := by linarith [h2q]
      exact ne_of_gt hpos
    have hWpos : (0 : ℝ) < ((q : ℝ) - 1) * (n : ℝ) := by
      have h1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith [h2q]
      exact mul_pos h1 hn0
    have hq1 : (q : ℝ) * (1 - 1 / (q : ℝ)) = (q : ℝ) - 1 := by
      field_simp
    have hfield2 : (q : ℝ) * (johnsonRadius q ((d : ℝ) / (n : ℝ)) * (n : ℝ)) =
        ((q : ℝ) - 1) * (n : ℝ) -
          ((q : ℝ) - 1) * (n : ℝ) *
            Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1))) := by
      rw [hJ]
      calc (q : ℝ) * (((1 - 1 / (q : ℝ)) *
              (1 - Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1))))) *
            (n : ℝ))
            = ((q : ℝ) * (1 - 1 / (q : ℝ))) *
              ((1 - Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1)))) *
                (n : ℝ)) := by ring
        _ = ((q : ℝ) - 1) *
              ((1 - Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1)))) *
                (n : ℝ)) := by rw [hq1]
        _ = ((q : ℝ) - 1) * (n : ℝ) -
              ((q : ℝ) - 1) * (n : ℝ) *
                Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1))) := by ring
    have hWsV : ((q : ℝ) - 1) * (n : ℝ) *
          Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1))) <
        ((q : ℝ) - 1) * (n : ℝ) - (q : ℝ) * (e : ℝ) := by
      have hmul := mul_lt_mul_of_pos_left he hq0
      linarith [hmul, hfield2]
    have hWsnn : (0 : ℝ) ≤ ((q : ℝ) - 1) * (n : ℝ) *
        Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1))) :=
      mul_nonneg (le_of_lt hWpos) hsqrt_nn
    have hsqW : ((((q : ℝ) - 1) * (n : ℝ) *
          Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1)))) ^ 2) <
        ((((q : ℝ) - 1) * (n : ℝ) - (q : ℝ) * (e : ℝ))) ^ 2 := by
      have hd1 : (0 : ℝ) <
          (((q : ℝ) - 1) * (n : ℝ) - (q : ℝ) * (e : ℝ)) -
            ((q : ℝ) - 1) * (n : ℝ) *
              Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1))) := by
        linarith [hWsV]
      have hd2 : (0 : ℝ) <
          (((q : ℝ) - 1) * (n : ℝ) - (q : ℝ) * (e : ℝ)) +
            ((q : ℝ) - 1) * (n : ℝ) *
              Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1))) := by
        linarith [hWsV, hWsnn]
      have hprod := mul_pos hd1 hd2
      linarith [hprod]
    have hsqW' : (((q : ℝ) - 1) * (n : ℝ)) ^ 2 *
          (Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1)))) ^ 2 <
        ((((q : ℝ) - 1) * (n : ℝ) - (q : ℝ) * (e : ℝ))) ^ 2 := by
      linarith [hsqW]
    have hXle : (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1)) ≤
        (Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1)))) ^ 2 := by
      rw [Real.sq_sqrt (le_max_left (0 : ℝ) _)]
      exact le_max_right _ _
    have hmulX : (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1)) *
          (((q : ℝ) - 1) * (n : ℝ)) ^ 2 ≤
        (Real.sqrt (max 0 (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1)))) ^ 2 *
          (((q : ℝ) - 1) * (n : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hXle (sq_nonneg _)
    have hXW2V : (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1)) *
          (((q : ℝ) - 1) * (n : ℝ)) ^ 2 <
        ((((q : ℝ) - 1) * (n : ℝ) - (q : ℝ) * (e : ℝ))) ^ 2 := by
      linarith [hmulX, hsqW']
    have hXW2 : (1 - (q : ℝ) * ((d : ℝ) / (n : ℝ)) / ((q : ℝ) - 1)) *
          (((q : ℝ) - 1) * (n : ℝ)) ^ 2 =
          ((((q : ℝ) - 1) * (n : ℝ)) ^ 2) -
            (q : ℝ) * (d : ℝ) * ((q : ℝ) - 1) * (n : ℝ) := by
      field_simp
    have hAqB : (q : ℝ) * (((q : ℝ) - 1) * (n : ℝ) * ((n : ℝ) - (d : ℝ))) <
        (q : ℝ) * (((q : ℝ) - 1) * ((n : ℝ) - (e : ℝ)) ^ 2 + (e : ℝ) ^ 2) := by
      linarith [hXW2V, hXW2]
    have h2R : ((q : ℝ) - 1) * (n : ℝ) * ((n : ℝ) - (d : ℝ)) <
        ((q : ℝ) - 1) * ((n : ℝ) - (e : ℝ)) ^ 2 + (e : ℝ) ^ 2 :=
      (mul_lt_mul_iff_of_pos_left hq0).mp hAqB
    have hpart2 : ((q : ℤ) - 1) * n * ((n : ℤ) - d) <
        ((q : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2 := by
      exact_mod_cast h2R
    exact ⟨hpart1, hpart2⟩

/-- **List decodability below the Johnson radius.** If `e` is strictly below
`J_q(d / n) * n`, the code is list decodable at radius `e` with list bound `q * d * n`. -/
theorem isListDecodable_of_lt_johnsonRadius (C : Finset (Fin n → α)) {d e : ℕ}
    (hq : 2 ≤ Fintype.card α)
    (hdist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (he : (e : ℝ) < johnsonRadius (Fintype.card α) ((d : ℝ) / n) * n) :
    IsListDecodable C e (Fintype.card α * d * n) := by
  obtain ⟨hlt, hJ⟩ := qary_johnson_conditions_of_lt_johnsonRadius hq he
  exact isListDecodable_of_qary_johnson C hq (le_of_lt hlt) hdist hJ

/-- **Floored real-radius form.** For every nonnegative relative radius `ρ` strictly below
`J_q(d / n)`, the code is list decodable at the integer radius `⌊ρ * n⌋₊` with list bound
`q * d * n`. -/
theorem isListDecodable_floor_of_lt_johnsonRadius (C : Finset (Fin n → α)) {d : ℕ} {ρ : ℝ}
    (hq : 2 ≤ Fintype.card α)
    (hdist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < johnsonRadius (Fintype.card α) ((d : ℝ) / n)) :
    IsListDecodable C ⌊ρ * n⌋₊ (Fintype.card α * d * n) := by
  by_cases hn : n = 0
  · have hJ0 : johnsonRadius (Fintype.card α) ((d : ℝ) / (n : ℝ)) = 0 := by
      rw [hn]
      unfold johnsonRadius
      norm_num [Real.sqrt_one]
    rw [hJ0] at hρ
    exact absurd hρ (not_lt_of_ge hρ0)
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hfle : ((⌊ρ * n⌋₊ : ℕ) : ℝ) ≤ ρ * n :=
      Nat.floor_le (mul_nonneg hρ0 (Nat.cast_nonneg _))
    have hlt : ρ * (n : ℝ) < johnsonRadius (Fintype.card α) ((d : ℝ) / n) * n :=
      mul_lt_mul_of_pos_right hρ hn0
    have he : ((⌊ρ * n⌋₊ : ℕ) : ℝ) <
        johnsonRadius (Fintype.card α) ((d : ℝ) / n) * n :=
      lt_of_le_of_lt hfle hlt
    exact isListDecodable_of_lt_johnsonRadius C hq hdist he

/-- **Ball-intersection cardinality below the Johnson radius.** If `e` is strictly below
`J_q(d / n) * n`, every radius-`e` Hamming ball contains at most `q * d * n` codewords. -/
theorem card_inter_ball_le_of_lt_johnsonRadius (C : Finset (Fin n → α)) (y : Fin n → α)
    {d e : ℕ} (hq : 2 ≤ Fintype.card α)
    (hdist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (he : (e : ℝ) < johnsonRadius (Fintype.card α) ((d : ℝ) / n) * n) :
    (C ∩ Hamming.ball y e).card ≤ Fintype.card α * d * n := by
  have h := isListDecodable_of_lt_johnsonRadius C hq hdist he y
  convert h using 2
  ext c
  simp [Finset.mem_inter, Finset.mem_filter, Hamming.mem_ball, hammingDist_comm, and_comm]

/-- All binary words of length `n` and Hamming weight `w`. -/
def weightCode (n w : ℕ) : Finset (Fin n → ZMod 2) :=
  univ.filter fun c => hammingNorm c = w

private theorem zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

private theorem zmod2_ind_eq : ∀ x : ZMod 2, (if x ≠ 0 then (1 : ZMod 2) else 0) = x := by
  decide

private theorem support_indicator (s : Finset (Fin n)) :
    Finset.univ.filter (fun j => (if j ∈ s then (1 : ZMod 2) else 0) ≠ 0) = s := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hj : j ∈ s <;> simp [hj, zmod2_one_ne_zero]

private def weightSuppEquiv (n : ℕ) :
    { c : Fin n → ZMod 2 // hammingNorm c = 3 } ≃ { s : Finset (Fin n) // s.card = 3 } where
  toFun c := ⟨Finset.univ.filter (fun j => c.val j ≠ 0), c.property⟩
  invFun s :=
    ⟨fun j => if j ∈ s.val then 1 else 0, by
      have h1 : hammingNorm (fun j => if j ∈ s.val then (1 : ZMod 2) else 0) = s.val.card := by
        have hrfl : hammingNorm (fun j => if j ∈ s.val then (1 : ZMod 2) else 0) =
            (Finset.univ.filter (fun j => (if j ∈ s.val then (1 : ZMod 2) else 0) ≠ 0)).card :=
          rfl
        rw [hrfl, support_indicator]
      exact h1.trans s.property⟩
  left_inv c := by
    refine Subtype.ext ?_
    show (fun j => if j ∈ Finset.univ.filter (fun j => c.val j ≠ 0) then (1 : ZMod 2) else 0) =
      c.val
    funext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact zmod2_ind_eq (c.val j)
  right_inv s := by
    refine Subtype.ext ?_
    show Finset.univ.filter (fun j => (if j ∈ s.val then (1 : ZMod 2) else 0) ≠ 0) = s.val
    exact support_indicator s.val

private theorem card_weightCode (n : ℕ) : (weightCode n 3).card = n.choose 3 := by
  have e1 : { c : Fin n → ZMod 2 // hammingNorm c = 3 } ≃ ↥(weightCode n 3) :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun c => by simp [weightCode])
  have e2 : { s : Finset (Fin n) // s.card = 3 } ≃ ↥(Finset.powersetCard 3 Finset.univ) :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun s => by simp [Finset.mem_powersetCard])
  have hcard := Fintype.card_congr (e1.symm.trans ((weightSuppEquiv n).trans e2))
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  rw [hcard, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private theorem choose_three_gt (n : ℕ) (hn : 7 ≤ n) : 4 * n < n.choose 3 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h2 : 4 ≤ n.choose 2 := by
      calc 4 ≤ (7).choose 2 := by decide
        _ ≤ n.choose 2 := Nat.choose_le_choose 2 hn
    have hcc : (n + 1).choose 3 = n.choose 2 + n.choose 3 := Nat.choose_succ_succ n 2
    omega

/-- **Minimum distance of a constant-weight binary code.** Any two distinct binary words of
the same Hamming weight have even, positive Hamming distance, hence distance at least `2`. -/
theorem two_le_hammingDist_weightCode {n w : ℕ} :
    ∀ c₁ ∈ weightCode n w, ∀ c₂ ∈ weightCode n w, c₁ ≠ c₂ → 2 ≤ hammingDist c₁ c₂ := by
  intro c₁ hc₁ c₂ hc₂ hne
  simp only [weightCode, Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
  have hpos : 0 < hammingDist c₁ c₂ := hammingDist_pos.mpr hne
  have hcoord : ∀ a b : ZMod 2,
      ((if a ≠ b then (1 : ℕ) else 0) + (if a ≠ 0 then (1 : ℕ) else 0) +
        (if b ≠ 0 then (1 : ℕ) else 0)) % 2 = 0 := by
    decide
  have hA : (∑ j ∈ (Finset.univ : Finset (Fin n)), (if c₁ j ≠ c₂ j then (1 : ℕ) else 0)) =
      hammingDist c₁ c₂ := by
    have hrfl : hammingDist c₁ c₂ = (Finset.univ.filter (fun j => c₁ j ≠ c₂ j)).card := rfl
    rw [hrfl]
    exact (Finset.card_filter _ _).symm
  have hB : (∑ j ∈ (Finset.univ : Finset (Fin n)), (if c₁ j ≠ 0 then (1 : ℕ) else 0)) =
      hammingNorm c₁ := by
    have hrfl : hammingNorm c₁ = (Finset.univ.filter (fun j => c₁ j ≠ 0)).card := rfl
    rw [hrfl]
    exact (Finset.card_filter _ _).symm
  have hC : (∑ j ∈ (Finset.univ : Finset (Fin n)), (if c₂ j ≠ 0 then (1 : ℕ) else 0)) =
      hammingNorm c₂ := by
    have hrfl : hammingNorm c₂ = (Finset.univ.filter (fun j => c₂ j ≠ 0)).card := rfl
    rw [hrfl]
    exact (Finset.card_filter _ _).symm
  have hdecomp : (∑ j ∈ (Finset.univ : Finset (Fin n)),
        ((if c₁ j ≠ c₂ j then (1 : ℕ) else 0) + (if c₁ j ≠ 0 then (1 : ℕ) else 0) +
          (if c₂ j ≠ 0 then (1 : ℕ) else 0))) =
      hammingDist c₁ c₂ + (hammingNorm c₁ + hammingNorm c₂) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC, add_assoc]
  have hmod : (hammingDist c₁ c₂) % 2 = 0 := by
    have hsum : ((∑ j ∈ (Finset.univ : Finset (Fin n)),
        ((if c₁ j ≠ c₂ j then (1 : ℕ) else 0) + (if c₁ j ≠ 0 then (1 : ℕ) else 0) +
          (if c₂ j ≠ 0 then (1 : ℕ) else 0)))) % 2 = 0 := by
      rw [Finset.sum_nat_mod]
      simp only [hcoord, Finset.sum_const_zero, Nat.zero_mod]
    rw [hdecomp, hc₁, hc₂] at hsum
    omega
  have heven : Even (hammingDist c₁ c₂) := Nat.even_iff.mpr hmod
  obtain ⟨r, hr⟩ := heven
  omega

/-- **Binary radius bound at relative distance `2 / n`.** The unnormalized Johnson radius
`J_2(2 / n) * n`, the unnormalized clipped Johnson radius, is strictly less than `3`
for every length `n`; this is the nonvacuity input for the weight-three example. -/
theorem johnsonRadius_two_lt_three (n : ℕ) :
    johnsonRadius 2 ((2 : ℝ) / n) * n < 3 := by
  by_cases hn5 : n ≤ 5
  · have hs : (0 : ℝ) ≤
        Real.sqrt (max 0 (1 - ((2 : ℕ) : ℝ) * ((2 : ℝ) / (n : ℝ)) / (((2 : ℕ) : ℝ) - 1))) :=
      Real.sqrt_nonneg _
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hn5' : (n : ℝ) ≤ 5 := by exact_mod_cast hn5
    have hJ : johnsonRadius 2 ((2 : ℝ) / n) * n ≤ (n : ℝ) / 2 := by
      have h2 : (1 : ℝ) - 1 / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
      unfold johnsonRadius
      rw [h2]
      have hprod := mul_nonneg hs hnn
      linarith
    linarith [hJ, hn5']
  · push Not at hn5
    have hn6 : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 6 ≤ n)
    have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    simp only [johnsonRadius, Nat.cast_ofNat]
    have heq : 2 * (2 / (n : ℝ)) / (2 - 1) = 4 / n := by
      field_simp
      ring
    have hr : (0 : ℝ) ≤ 1 - 2 * (2 / (n : ℝ)) / (2 - 1) := by
      have h4 : (4 : ℝ) / n ≤ 1 := by
        rw [div_le_one hn_pos]
        linarith [hn6]
      rw [heq]
      linarith [h4]
    have heq2 : (1 : ℝ) - 2 * (2 / (n : ℝ)) / (2 - 1) = 1 - 4 / n := by rw [heq]
    have hsq : 1 - 6 / (n : ℝ) < Real.sqrt (max 0 (1 - 2 * (2 / (n : ℝ)) / (2 - 1))) := by
      have hnn : (0 : ℝ) ≤ 1 - 6 / n := by
        have h6 : (6 : ℝ) / n ≤ 1 := by
          rw [div_le_one hn_pos]
          linarith [hn6]
        linarith [h6]
      rw [max_eq_right hr, Real.lt_sqrt hnn, heq2]
      field_simp
      linarith [hn6]
    have h2 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h2]
    have h1s : 1 - Real.sqrt (max 0 (1 - 2 * (2 / (n : ℝ)) / (2 - 1))) < 6 / (n : ℝ) := by
      linarith [hsq]
    calc (1 / 2 : ℝ) * (1 - Real.sqrt (max 0 (1 - 2 * (2 / (n : ℝ)) / (2 - 1)))) * n
        < (1 / 2) * (6 / (n : ℝ)) * n := by
          apply mul_lt_mul_of_pos_right
          · linarith [h1s]
          · linarith [hn6]
      _ = 3 := by field_simp; ring

/-- **Nonvacuity beyond the binary Johnson radius.** For `7 ≤ n`, all `n.choose 3`
weight-three binary words lie in the radius-`3` ball around zero, and their number exceeds
`2 * 2 * n`; hence this constant-weight code is not list decodable at radius `3` with that
list bound. -/
theorem not_isListDecodable_weightCode_three {n : ℕ} (hn : 7 ≤ n) :
    ¬ IsListDecodable (weightCode n 3) 3 (2 * 2 * n) := by
  intro hcon
  have h0 := hcon 0
  have h0cap : (weightCode n 3 ∩ Hamming.ball 0 3).card ≤ 2 * 2 * n := by
    convert h0 using 2
    ext c
    simp [Finset.mem_inter, Finset.mem_filter, Hamming.mem_ball, hammingDist_comm, and_comm]
  have hsub : weightCode n 3 ⊆ Hamming.ball 0 3 := by
    intro c hc
    simp only [weightCode, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Hamming.mem_ball]
    have hdc : hammingDist (0 : Fin n → ZMod 2) c = hammingNorm c := by
      rw [hammingDist_comm]
      exact hammingDist_zero_right c
    omega
  have hinter : weightCode n 3 ∩ Hamming.ball 0 3 = weightCode n 3 :=
    Finset.inter_eq_left.mpr hsub
  rw [hinter, card_weightCode] at h0cap
  have hgt := choose_three_gt n hn
  omega

end MathlibExt.Combinatorics.Coding.JohnsonBound
