/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.Recurrences.DegenerateSecondOrder
public import MathlibExt.NumberTheory.Recurrences.LucasPeriodAverage
public import MathlibExt.NumberTheory.Recurrences.NondegenerateLucasPair
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Sums of eight degenerate second-order recurrences

This module proves `degenerate_secondOrder_sums`: the sums of the Lucas sequences
`U(0, -1)` and `U(-2, 1)`, the moduli with integral averages for three recurrences, and
the block-sum and affine-sum formulas for the eight degenerate second-order recurrences.
It defines `lucasAllAveragesIntegral`, the property that `n` divides every `n`-term sum
of a recurrence.

Statements from Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of
Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36.

The paper writes the recurrence as `W (n + 2) = a * W (n + 1) + b * W n` with discriminant
`D = a ^ 2 + 4 * b`. This module uses the repository convention of `lucasU`: parameters
`P = a` and `Q = -b`, so `b = -params.q`, `D = params.p ^ 2 - 4 * params.q`,
`a + b - 1 = params.p - params.q - 1` and `-b - 1 = params.q - 1`. The paper's `B_W(n)` is
`∑ i ∈ Finset.Icc 1 n, w i`, and "`A_W(n) = B_W(n) / n` is an integer" is
`(n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, w i`. Nondegeneracy (`ab ≠ 0` and `α / β` not a root of
unity) is `IsNondegenerateLucasPair params.p params.q`; `Q ≠ 0` is built into
`LucasSequenceParams`, and `a = 0` is excluded because then `α / β = -1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Integral averages of all recurrences.** For integers $P$ and $Q \ne 0$ and a natural number
$n$, the property that $n$ has integral averages means that every integer sequence
$(w_k)_{k \ge 0}$ with $w_{k+2} = P w_{k+1} - Q w_k$ for all $k$ satisfies
$n \mid w_1 + \dots + w_n$; for $n > 0$ this says that the average
$A_W(n) = (w_1 + \dots + w_n)/n$ is an integer.

In the paper's notation $a = P$ and $b = -Q$, so the recurrence reads
$w_{k+2} = a w_{k+1} + b w_k$.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Section 2 (definition of
`B_W(n)` and `A_W(n)`). -/
def lucasAllAveragesIntegral (params : LucasSequenceParams) (n : ℕ) : Prop :=
  ∀ w : ℕ → ℤ, (∀ k, w (k + 2) = params.p * w (k + 1) - params.q * w k) →
    (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, w i

open degenerate_secondOrder_closedForms in
private theorem sum_u_aux (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, lucasU ⟨0, -1, by decide⟩ i = (((n + 1) / 2 : ℕ) : ℤ) := by
  have hw : ∀ k, lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams) (k + 2) =
      lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams) k := by
    intro k
    have h := lucasU_add_two (⟨0, -1, by decide⟩ : LucasSequenceParams) k
    simpa using h
  have hu0 : lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams) 0 = 0 := rfl
  have hu1 : lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams) 1 = 1 := rfl
  have hpair : ∀ m, lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams) m +
      lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams) (m + 1) = 1 := by
    intro m
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
    · have e1 : r + r = 2 * r := by omega
      rw [hr, e1, (period_two _ hw r).1, (period_two _ hw r).2, hu0, hu1, zero_add]
    · have e : 2 * r + 1 + 1 = 2 * (r + 1) := by omega
      rw [hr, e, (period_two _ hw r).2, (period_two _ hw (r + 1)).1, hu0, hu1, add_zero]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [lucasU]
  | more n ih1 ih2 =>
    have h1 : ∑ i ∈ Finset.Icc 1 (n + 1),
        lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams) i =
        ∑ i ∈ Finset.Icc 1 n, lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams) i +
        lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams) (n + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have h2 : ∑ i ∈ Finset.Icc 1 (n + 2),
        lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams) i =
        ∑ i ∈ Finset.Icc 1 (n + 1), lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams) i +
        lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams) (n + 2) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (n + 1) + 1 from by omega)
        (lucasU (⟨0, -1, by decide⟩ : LucasSequenceParams))
      simpa [show (n + 1) + 1 = n + 2 from by omega] using h
    have hdiv : (n + 2 + 1) / 2 = (n + 1) / 2 + 1 := by omega
    have hpr := hpair (n + 1)
    rw [show (n + 1) + 1 = n + 2 from by omega] at hpr
    rw [h2, h1, ih1, hdiv, Nat.cast_add, Nat.cast_one, add_assoc, hpr]

private theorem allAvg_01 (n : ℕ) (hn : 1 ≤ n) :
    lucasAllAveragesIntegral ⟨0, -1, by decide⟩ n ↔ n = 1 := by
  constructor
  · intro havg
    have hdvd := havg _ (fun k => lucasU_add_two _ k)
    rw [sum_u_aux n] at hdvd
    have hnat : n ∣ (n + 1) / 2 := Int.natCast_dvd_natCast.mp hdvd
    have hpos : 0 < (n + 1) / 2 := by omega
    have hle := Nat.le_of_dvd hpos hnat
    omega
  · intro hn1
    subst hn1
    intro w hw
    simp

private theorem sum_neg_four (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = -w k) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 (4 * n), w i = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 4 * (n + 1) = 4 * n + 4 := by omega
    have h4 : ∑ i ∈ Finset.Icc 1 (4 * n + 4), w i =
        ∑ i ∈ Finset.Icc 1 (4 * n + 3), w i + w (4 * n + 4) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (4 * n + 3) + 1 from by omega) w
      simpa [show (4 * n + 3) + 1 = 4 * n + 4 from by omega] using h
    have h3 : ∑ i ∈ Finset.Icc 1 (4 * n + 3), w i =
        ∑ i ∈ Finset.Icc 1 (4 * n + 2), w i + w (4 * n + 3) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (4 * n + 2) + 1 from by omega) w
      simpa [show (4 * n + 2) + 1 = 4 * n + 3 from by omega] using h
    have h2 : ∑ i ∈ Finset.Icc 1 (4 * n + 2), w i =
        ∑ i ∈ Finset.Icc 1 (4 * n + 1), w i + w (4 * n + 2) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (4 * n + 1) + 1 from by omega) w
      simpa [show (4 * n + 1) + 1 = 4 * n + 2 from by omega] using h
    have h1 : ∑ i ∈ Finset.Icc 1 (4 * n + 1), w i =
        ∑ i ∈ Finset.Icc 1 (4 * n), w i + w (4 * n + 1) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (4 * n) + 1 from by omega) w
      simpa [show (4 * n) + 1 = 4 * n + 1 from by omega] using h
    have a : w (4 * n + 3) = -w (4 * n + 1) := by
      have h := hw (4 * n + 1)
      simpa [show (4 * n + 1) + 2 = 4 * n + 3 from by omega] using h
    have b : w (4 * n + 4) = -w (4 * n + 2) := by
      have h := hw (4 * n + 2)
      simpa [show (4 * n + 2) + 2 = 4 * n + 4 from by omega] using h
    rw [e, h4, h3, h2, h1, ih, a, b]
    ring

private theorem sum_diff_six (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = w (k + 1) - w k)
    (n : ℕ) : ∑ i ∈ Finset.Icc 1 (6 * n), w i = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 6 * (n + 1) = 6 * n + 6 := by omega
    have h6 : ∑ i ∈ Finset.Icc 1 (6 * n + 6), w i =
        ∑ i ∈ Finset.Icc 1 (6 * n + 5), w i + w (6 * n + 6) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (6 * n + 5) + 1 from by omega) w
      simpa [show (6 * n + 5) + 1 = 6 * n + 6 from by omega] using h
    have h5 : ∑ i ∈ Finset.Icc 1 (6 * n + 5), w i =
        ∑ i ∈ Finset.Icc 1 (6 * n + 4), w i + w (6 * n + 5) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (6 * n + 4) + 1 from by omega) w
      simpa [show (6 * n + 4) + 1 = 6 * n + 5 from by omega] using h
    have h4 : ∑ i ∈ Finset.Icc 1 (6 * n + 4), w i =
        ∑ i ∈ Finset.Icc 1 (6 * n + 3), w i + w (6 * n + 4) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (6 * n + 3) + 1 from by omega) w
      simpa [show (6 * n + 3) + 1 = 6 * n + 4 from by omega] using h
    have h3 : ∑ i ∈ Finset.Icc 1 (6 * n + 3), w i =
        ∑ i ∈ Finset.Icc 1 (6 * n + 2), w i + w (6 * n + 3) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (6 * n + 2) + 1 from by omega) w
      simpa [show (6 * n + 2) + 1 = 6 * n + 3 from by omega] using h
    have h2 : ∑ i ∈ Finset.Icc 1 (6 * n + 2), w i =
        ∑ i ∈ Finset.Icc 1 (6 * n + 1), w i + w (6 * n + 2) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (6 * n + 1) + 1 from by omega) w
      simpa [show (6 * n + 1) + 1 = 6 * n + 2 from by omega] using h
    have h1 : ∑ i ∈ Finset.Icc 1 (6 * n + 1), w i =
        ∑ i ∈ Finset.Icc 1 (6 * n), w i + w (6 * n + 1) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (6 * n) + 1 from by omega) w
      simpa [show (6 * n) + 1 = 6 * n + 1 from by omega] using h
    have c3 : w (6 * n + 3) = w (6 * n + 2) - w (6 * n + 1) := by
      have h := hw (6 * n + 1)
      simpa [show (6 * n + 1) + 2 = 6 * n + 3 from by omega,
        show (6 * n + 1) + 1 = 6 * n + 2 from by omega] using h
    have c4 : w (6 * n + 4) = w (6 * n + 3) - w (6 * n + 2) := by
      have h := hw (6 * n + 2)
      simpa [show (6 * n + 2) + 2 = 6 * n + 4 from by omega,
        show (6 * n + 2) + 1 = 6 * n + 3 from by omega] using h
    have c5 : w (6 * n + 5) = w (6 * n + 4) - w (6 * n + 3) := by
      have h := hw (6 * n + 3)
      simpa [show (6 * n + 3) + 2 = 6 * n + 5 from by omega,
        show (6 * n + 3) + 1 = 6 * n + 4 from by omega] using h
    have c6 : w (6 * n + 6) = w (6 * n + 5) - w (6 * n + 4) := by
      have h := hw (6 * n + 4)
      simpa [show (6 * n + 4) + 2 = 6 * n + 6 from by omega,
        show (6 * n + 4) + 1 = 6 * n + 5 from by omega] using h
    rw [e, h6, h5, h4, h3, h2, h1, ih]
    linear_combination c3 + 2 * c4 + 2 * c5 + c6

private theorem sum_neg_add_three (w : ℕ → ℤ)
    (hw : ∀ k, w (k + 2) = -w (k + 1) - w k) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 (3 * n), w i = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 3 * (n + 1) = 3 * n + 3 := by omega
    have h3 : ∑ i ∈ Finset.Icc 1 (3 * n + 3), w i =
        ∑ i ∈ Finset.Icc 1 (3 * n + 2), w i + w (3 * n + 3) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (3 * n + 2) + 1 from by omega) w
      simpa [show (3 * n + 2) + 1 = 3 * n + 3 from by omega] using h
    have h2 : ∑ i ∈ Finset.Icc 1 (3 * n + 2), w i =
        ∑ i ∈ Finset.Icc 1 (3 * n + 1), w i + w (3 * n + 2) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (3 * n + 1) + 1 from by omega) w
      simpa [show (3 * n + 1) + 1 = 3 * n + 2 from by omega] using h
    have h1 : ∑ i ∈ Finset.Icc 1 (3 * n + 1), w i =
        ∑ i ∈ Finset.Icc 1 (3 * n), w i + w (3 * n + 1) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (3 * n) + 1 from by omega) w
      simpa [show (3 * n) + 1 = 3 * n + 1 from by omega] using h
    have c : w (3 * n + 3) = -w (3 * n + 2) - w (3 * n + 1) := by
      have h := hw (3 * n + 1)
      simpa [show (3 * n + 1) + 2 = 3 * n + 3 from by omega,
        show (3 * n + 1) + 1 = 3 * n + 2 from by omega] using h
    rw [e, h3, h2, h1, ih, c]
    ring

private theorem sum_alt_tail_two (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = -w (k + 1))
    (n : ℕ) : ∑ i ∈ Finset.Icc 1 (2 * n), w i = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 2 := by omega
    have h2 : ∑ i ∈ Finset.Icc 1 (2 * n + 2), w i =
        ∑ i ∈ Finset.Icc 1 (2 * n + 1), w i + w (2 * n + 2) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (2 * n + 1) + 1 from by omega) w
      simpa [show (2 * n + 1) + 1 = 2 * n + 2 from by omega] using h
    have h1 : ∑ i ∈ Finset.Icc 1 (2 * n + 1), w i =
        ∑ i ∈ Finset.Icc 1 (2 * n), w i + w (2 * n + 1) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (2 * n) + 1 from by omega) w
      simpa [show (2 * n) + 1 = 2 * n + 1 from by omega] using h
    have c : w (2 * n + 2) = -w (2 * n + 1) := by
      have h := hw (2 * n)
      simpa [show 2 * n + 2 = (2 * n) + 2 from by omega,
        show 2 * n + 1 = (2 * n) + 1 from by omega] using h
    rw [e, h2, h1, ih, c]
    ring

open degenerate_secondOrder_closedForms in
private theorem sum_affine (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = 2 * w (k + 1) - w k)
    (n : ℕ) : 2 * ∑ i ∈ Finset.Icc 1 n, w i =
      (w 1 - w 0) * n * (n + 1) + 2 * w 0 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : ∑ i ∈ Finset.Icc 1 (n + 1), w i =
        ∑ i ∈ Finset.Icc 1 n, w i + w (n + 1) :=
      Finset.sum_Icc_succ_top (by omega) w
    have hL : 2 * ∑ i ∈ Finset.Icc 1 (n + 1), w i =
        2 * ∑ i ∈ Finset.Icc 1 n, w i + 2 * w (n + 1) := by
      rw [hsplit, mul_add]
    have haff := affine w hw (n + 1)
    rw [hL, ih, haff, Nat.cast_add, Nat.cast_one]
    ring

open degenerate_secondOrder_closedForms in
private theorem sum_const_tail (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = w (k + 1))
    (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, w i = n * w 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : ∑ i ∈ Finset.Icc 1 (n + 1), w i =
        ∑ i ∈ Finset.Icc 1 n, w i + w (n + 1) :=
      Finset.sum_Icc_succ_top (by omega) w
    have hw1 : w (n + 1) = w 1 := constant_tail w hw (n + 1) (by omega)
    rw [hsplit, ih, hw1, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

private theorem sum_affine_odd (w : ℕ → ℤ)
    (hw : ∀ k, w (k + 2) = 2 * w (k + 1) - w k) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 (2 * n - 1), w i =
      ((2 * n - 1 : ℕ) : ℤ) * (n * (w 1 - w 0) + w 0) := by
  have hN1 : ((2 * n - 1 : ℕ) : ℤ) + 1 = 2 * (n : ℤ) := by omega
  have h6 := sum_affine w hw (2 * n - 1)
  have h2 : (2 : ℤ) * ∑ i ∈ Finset.Icc 1 (2 * n - 1), w i =
      2 * (((2 * n - 1 : ℕ) : ℤ) * (n * (w 1 - w 0) + w 0)) := by
    rw [h6, hN1]
    ring
  exact mul_left_cancel₀ (by decide) h2

private theorem allAvg_21 (n : ℕ) (hn : 1 ≤ n) :
    lucasAllAveragesIntegral ⟨2, 1, by decide⟩ n ↔ Odd n := by
  constructor
  · intro havg
    have hwLit : ∀ k, ((k + 2 : ℕ) : ℤ) = 2 * ((k + 1 : ℕ) : ℤ) - 1 * ((k : ℕ) : ℤ) :=
      fun k => by omega
    have hwB : ∀ k, ((k + 2 : ℕ) : ℤ) = 2 * ((k + 1 : ℕ) : ℤ) - ((k : ℕ) : ℤ) :=
      fun k => by omega
    have hdvd := havg (fun k : ℕ => ((k : ℕ) : ℤ)) hwLit
    have h6 := sum_affine (fun k : ℕ => ((k : ℕ) : ℤ)) hwB n
    simp only [Nat.cast_one, Nat.cast_zero, sub_zero, one_mul, mul_zero, zero_mul,
      add_zero] at h6
    obtain ⟨t, ht⟩ := hdvd
    rw [ht] at h6
    have hN : (n : ℤ) ≠ 0 := by omega
    have h2 : (2 : ℤ) * ((n : ℤ) * t) = (n : ℤ) * (2 * t) := by ring
    rw [h2] at h6
    have hcancel : (2 : ℤ) * t = (n : ℤ) + 1 := mul_left_cancel₀ hN h6
    have hOddInt : Odd ((n : ℤ)) := ⟨t - 1, by omega⟩
    exact (Int.odd_natCast n).mp hOddInt
  · intro hodd w hwA
    have hwB : ∀ k, w (k + 2) = 2 * w (k + 1) - w k := fun k => by
      have h : w (k + 2) = 2 * w (k + 1) - 1 * w k := hwA k
      simpa using h
    have h6 := sum_affine w hwB n
    rcases hodd with ⟨m, hm⟩
    have hN : (n : ℤ) = 2 * (m : ℤ) + 1 := by rw [hm]; simp
    have hS : ∑ i ∈ Finset.Icc 1 n, w i =
        (n : ℤ) * ((w 1 - w 0) * ((m : ℤ) + 1) + w 0) := by
      have h2 : (2 : ℤ) * ∑ i ∈ Finset.Icc 1 n, w i =
          2 * ((n : ℤ) * ((w 1 - w 0) * ((m : ℤ) + 1) + w 0)) := by
        rw [h6, hN]
        ring
      exact mul_left_cancel₀ (by decide) h2
    exact ⟨_, hS⟩

open degenerate_secondOrder_closedForms in
private theorem sum_v_aux (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, lucasU ⟨-2, 1, by decide⟩ i =
      (-1) ^ (n + 1) * (((n + 1) / 2 : ℕ) : ℤ) := by
  have hwv : ∀ k, lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) (k + 2) =
      -2 * lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) (k + 1) -
        lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) k := by
    intro k
    have h : lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) (k + 2) =
        -2 * lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) (k + 1) -
          1 * lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) k :=
      lucasU_add_two _ k
    simpa using h
  have hv0 : lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) 0 = 0 := rfl
  have hv1 : lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) 1 = 1 := rfl
  have hv : ∀ m, lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) m =
      (-1) ^ (m + 1) * ((m : ℕ) : ℤ) := by
    intro m
    rw [alternating_affine _ hwv m, hv0, hv1]
    ring
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [lucasU]
  | more n ih1 ih2 =>
    have h1 : ∑ i ∈ Finset.Icc 1 (n + 1),
        lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) i =
        ∑ i ∈ Finset.Icc 1 n, lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) i +
        lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) (n + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have h2 : ∑ i ∈ Finset.Icc 1 (n + 2),
        lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) i =
        ∑ i ∈ Finset.Icc 1 (n + 1), lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) i +
        lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) (n + 2) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ (n + 1) + 1 from by omega)
        (lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams))
      simpa [show (n + 1) + 1 = n + 2 from by omega] using h
    have q2 : (-1 : ℤ) ^ (n + 2) = -(-1 : ℤ) ^ (n + 1) := by
      rw [show n + 2 = (n + 1) + 1 from by omega, pow_add, pow_one]
      ring
    have q3 : (-1 : ℤ) ^ (n + 3) = (-1 : ℤ) ^ (n + 1) := by
      rw [show n + 3 = (n + 1) + 2 from by omega, pow_add]
      have h2neg : (-1 : ℤ) ^ 2 = 1 := by decide
      rw [h2neg, mul_one]
    have hpair : lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) (n + 1) +
        lucasU (⟨-2, 1, by decide⟩ : LucasSequenceParams) (n + 2) =
        (-1 : ℤ) ^ (n + 1) := by
      have e1 : (n + 1) + 1 = n + 2 := by omega
      have e2 : (n + 2) + 1 = n + 3 := by omega
      have c : ((n + 2 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by omega
      rw [hv (n + 1), hv (n + 2), e1, e2, q2, q3, c]
      ring
    have hdiv : ((n + 2) + 1) / 2 = (n + 1) / 2 + 1 := by omega
    have q3' : (-1 : ℤ) ^ ((n + 2) + 1) = (-1 : ℤ) ^ (n + 1) := by
      rw [show (n + 2) + 1 = n + 3 from by omega]
      exact q3
    rw [h2, h1, ih1, q3', hdiv, Nat.cast_add, Nat.cast_one, add_assoc, hpair]
    ring

private theorem allAvg_neg21 (n : ℕ) (hn : 1 ≤ n) :
    lucasAllAveragesIntegral ⟨-2, 1, by decide⟩ n ↔ n = 1 := by
  constructor
  · intro havg
    have hdvd := havg _ (fun k => lucasU_add_two _ k)
    rw [sum_v_aux n] at hdvd
    have hu2 : ∀ m, ((-1 : ℤ) ^ m) ^ 2 = 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have e : (-1 : ℤ) ^ (m + 1) = (-1 : ℤ) ^ m * (-1) := by
          rw [pow_add, pow_one]
        have h : (((-1 : ℤ) ^ m) * (-1)) ^ 2 =
            (((-1 : ℤ) ^ m) ^ 2) * ((-1 : ℤ) ^ 2) := by ring
        rw [e, h, ih]
        decide
    have heq : (-1 : ℤ) ^ (n + 1) * ((-1 : ℤ) ^ (n + 1) * (((n + 1) / 2 : ℕ) : ℤ)) =
        (((n + 1) / 2 : ℕ) : ℤ) := by
      have h : (-1 : ℤ) ^ (n + 1) * ((-1 : ℤ) ^ (n + 1) * (((n + 1) / 2 : ℕ) : ℤ)) =
          (((-1 : ℤ) ^ (n + 1)) ^ 2) * (((n + 1) / 2 : ℕ) : ℤ) := by ring
      rw [h, hu2 (n + 1), one_mul]
    obtain ⟨t, ht⟩ := hdvd
    have hNatDvd : (n : ℤ) ∣ (((n + 1) / 2 : ℕ) : ℤ) :=
      ⟨(-1 : ℤ) ^ (n + 1) * t, by rw [← heq, ht]; ring⟩
    have hnat : n ∣ (n + 1) / 2 := Int.natCast_dvd_natCast.mp hNatDvd
    have hpos : 0 < (n + 1) / 2 := by omega
    have hle := Nat.le_of_dvd hpos hnat
    omega
  · intro hn1
    subst hn1
    intro w hw
    simp

/-- **Sums of eight degenerate second-order recurrences.** For an integer sequence
$(w_j)_{j \ge 0}$ write $B_w(n) = w_1 + \dots + w_n$. Let $u$ be the sequence with $u_0 = 0$,
$u_1 = 1$ and $u_{j+2} = u_j$, and $v$ the sequence with $v_0 = 0$, $v_1 = 1$ and
$v_{j+2} = -2 v_{j+1} - v_j$. For every $n \ge 1$: $B_u(n) = \lfloor (n + 1) / 2 \rfloor$ and
$B_v(n) = (-1)^{n+1} \lfloor (n + 1) / 2 \rfloor$; $n$ divides $B_w(n)$ for every integer
sequence $w$ with $w_{j+2} = w_j$ if and only if $n = 1$; $n$ divides $B_w(n)$ for every integer
sequence $w$ with $w_{j+2} = 2 w_{j+1} - w_j$ if and only if $n$ is odd; and $n$ divides
$B_w(n)$ for every integer sequence $w$ with $w_{j+2} = -2 w_{j+1} - w_j$ if and only if
$n = 1$. For every integer sequence $w$ and every $n \in \mathbb{N}$: if $w_{j+2} = -w_j$ for all
$j$, then $B_w(4n) = 0$; if $w_{j+2} = w_{j+1} - w_j$ for all $j$, then $B_w(6n) = 0$; if
$w_{j+2} = -w_{j+1} - w_j$ for all $j$, then $B_w(3n) = 0$; if $w_{j+2} = w_{j+1}$ for all $j$,
then $B_w(n) = n w_1$; if $w_{j+2} = -w_{j+1}$ for all $j$, then $B_w(2n) = 0$; and if
$w_{j+2} = 2 w_{j+1} - w_j$ for all $j$, then $2 B_w(n) = (w_1 - w_0) n (n + 1) + 2 w_0 n$ and,
when $n \ge 1$, $B_w(2n - 1) = (2n - 1)(n (w_1 - w_0) + w_0)$.

In the paper's notation $W_{j+2} = a W_{j+1} + b W_j$ these are the pairs $(a, b) = (0, 1)$,
$(0, -1)$, $(1, -1)$, $(-1, -1)$, $(2, -1)$, $(-2, -1)$, $(1, 0)$ and $(-1, 0)$.

Source: Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of
Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.1
(`integers-2024-A36-thm-2-1`). -/
public theorem degenerate_secondOrder_sums :
    (∀ n, 1 ≤ n → ∑ i ∈ Finset.Icc 1 n, lucasU ⟨0, -1, by decide⟩ i = ((n + 1) / 2 : ℕ)) ∧
    (∀ n, 1 ≤ n → (lucasAllAveragesIntegral ⟨0, -1, by decide⟩ n ↔ n = 1)) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -w k) → ∀ n, ∑ i ∈ Finset.Icc 1 (4 * n), w i = 0) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = w (k + 1) - w k) →
      ∀ n, ∑ i ∈ Finset.Icc 1 (6 * n), w i = 0) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -w (k + 1) - w k) →
      ∀ n, ∑ i ∈ Finset.Icc 1 (3 * n), w i = 0) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = 2 * w (k + 1) - w k) →
      ∀ n : ℕ, 2 * ∑ i ∈ Finset.Icc 1 n, w i = (w 1 - w 0) * n * (n + 1) + 2 * w 0 * n) ∧
    (∀ n, 1 ≤ n → (lucasAllAveragesIntegral ⟨2, 1, by decide⟩ n ↔ Odd n)) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = 2 * w (k + 1) - w k) →
      ∀ n : ℕ, 1 ≤ n → ∑ i ∈ Finset.Icc 1 (2 * n - 1), w i =
        ((2 * n - 1 : ℕ) : ℤ) * (n * (w 1 - w 0) + w 0)) ∧
    (∀ n, 1 ≤ n → ∑ i ∈ Finset.Icc 1 n, lucasU ⟨-2, 1, by decide⟩ i =
      (-1) ^ (n + 1) * ((n + 1) / 2 : ℕ)) ∧
    (∀ n, 1 ≤ n → (lucasAllAveragesIntegral ⟨-2, 1, by decide⟩ n ↔ n = 1)) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = w (k + 1)) → ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, w i = n * w 1) ∧
    (∀ w : ℕ → ℤ, (∀ k, w (k + 2) = -w (k + 1)) → ∀ n, ∑ i ∈ Finset.Icc 1 (2 * n), w i = 0) :=
  ⟨fun n _ => sum_u_aux n, allAvg_01, sum_neg_four, sum_diff_six, sum_neg_add_three,
    sum_affine, allAvg_21, sum_affine_odd, fun n _ => sum_v_aux n, allAvg_neg21,
    sum_const_tail, sum_alt_tail_two⟩

end

end MetaMathlibExt
