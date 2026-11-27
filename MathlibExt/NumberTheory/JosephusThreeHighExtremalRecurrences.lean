/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Nth
public import MathlibExt.Combinatorics.Enumerative.JosephusFunction
import MathlibExt.NumberTheory.JosephusHighExtremal

/-!
# Consecutive high extremal points of the Josephus function with step three

`josephusThree_highExtremal_recurrences` gives the next high extremal point, its survivor,
their difference, and the parity of the point.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **High extremal points of the Josephus function $J_3$.** A natural number $n$ is a high
extremal point of the Josephus function $J_3$ (elimination step $3$) when $n \ge 1$ and either
$J_3(n) = n$ or $J_3(n) = n - 1$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 1, Definition
(Extremal and Fixed points). -/
public def IsJosephusThreeHighExtremal (n : ℕ) : Prop :=
  1 ≤ n ∧ (josephus 3 n = n ∨ josephus 3 n + 1 = n)

/-- **Fixed points of the Josephus function $J_3$.** A natural number $n$ is a fixed point of the
Josephus function $J_3$ (elimination step $3$) when $n \ge 1$ and $J_3(n) = n$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 1, Definition
(Extremal and Fixed points). -/
public def IsJosephusThreeFixedPoint (n : ℕ) : Prop :=
  1 ≤ n ∧ josephus 3 n = n

/-- **$3$ is a high extremal point but not a fixed point of $J_3$.** The number $3$ is a high
extremal point of the Josephus function $J_3$ (elimination step $3$) and is not a fixed point of
$J_3$; indeed $J_3(3) = 2$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 1, Definition
(Extremal and Fixed points). -/
public theorem isJosephusThreeHighExtremal_three :
    IsJosephusThreeHighExtremal 3 ∧ ¬ IsJosephusThreeFixedPoint 3 := by
  unfold IsJosephusThreeHighExtremal IsJosephusThreeFixedPoint
  decide

/-- **$4$ is not a high extremal point of $J_3$.** The number $4$ is not a high extremal point of
the Josephus function $J_3$ (elimination step $3$).

Indeed $J_3(4) = 1$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 1, Definition
(Extremal and Fixed points). -/
public theorem not_isJosephusThreeHighExtremal_four : ¬ IsJosephusThreeHighExtremal 4 := by
  unfold IsJosephusThreeHighExtremal
  decide

/-- **$13$ is a fixed point of $J_3$.** The number $13$ is a fixed point of the Josephus function
$J_3$ (elimination step $3$), that is, $J_3(13) = 13$.

It is the third fixed point of $J_3$, after $1$ and $2$; the statement records only that $13$ is
a fixed point.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Section 2, Table 1. -/
public theorem isJosephusThreeFixedPoint_thirteen : IsJosephusThreeFixedPoint 13 := by
  unfold IsJosephusThreeFixedPoint
  decide

namespace JosephusThree

private theorem exists_next_highExtremal {a : ℕ} (ha : IsJosephusThreeHighExtremal a) :
    ∃ b, IsLeast {n | a < n ∧ IsJosephusThreeHighExtremal n} b ∧
      josephus 3 b + 3 * a + 1 + (a - josephus 3 a) = 3 * b := by
  obtain ⟨ha₁, haJ⟩ := ha
  let j := josephus 3 (a + 1)
  -- The first step wraps to 2 after a fixed point and to 1 after a pure extremal point.
  have hj : j + (a - josephus 3 a) = 2 := by
    dsimp [j]
    rw [josephus_succ 3 a (by decide) ha₁]
    have h : josephus 3 a + 3 - 1 = a + 1 + (josephus 3 a + 1 - a) := by omega
    rw [h, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega
  have hj₁ : 1 ≤ j := by omega
  have hj₂ : j ≤ 2 := by omega
  let d := (a - (j - 1)) / 2
  -- Until the gap has fallen to 0 or 1, the survivor advances three places per step.
  have linear (m : ℕ) (hm : m ≤ d) : josephus 3 (a + 1 + m) = j + 3 * m := by
    by_cases h : 3 ≤ a
    · exact MathlibExt.NumberTheory.JosephusWanted.josephus_add_eq_of_high 3 a m
        (by decide) h ⟨hj₁, hj₂⟩ hm
    · have hm₀ : m = 0 := by
        rcases (show a = 1 ∨ a = 2 by omega) with rfl | rfl <;>
          simpa [d, j, josephus] using hm
      simp [hm₀, j]
  let b := a + 1 + d
  have hbJ : josephus 3 b = j + 3 * d := linear d le_rfl
  have hb : IsJosephusThreeHighExtremal b := by
    rw [IsJosephusThreeHighExtremal, hbJ]
    dsimp [b, d]
    omega
  refine ⟨b, ⟨⟨by dsimp [b]; omega, hb⟩, ?_⟩, ?_⟩
  · rintro n ⟨han, _, hnJ⟩
    by_contra! hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show a + 1 ≤ n by omega)
    have hm : m < d := by dsimp [b] at hn; omega
    have hJ := linear m hm.le
    dsimp [d] at hm
    omega
  · rw [hbJ]
    dsimp [b]
    omega

private theorem infinite_highExtremal : (Set.ofPred IsJosephusThreeHighExtremal).Infinite := by
  intro h
  obtain ⟨a, ha, hmax⟩ := h.exists_maximal ⟨3, isJosephusThreeHighExtremal_three.1⟩
  obtain ⟨b, hb, _⟩ := exists_next_highExtremal ha
  exact hb.1.1.not_ge (hmax hb.1.2 hb.1.1.le)

end JosephusThree

open JosephusThree in
/-- **Unified recurrences for consecutive high extremal points of $J_3$.** For every natural
number $i$, let $a$ and $b$ be the $(i+1)$-th and $(i+2)$-th smallest high extremal points of the
Josephus function $J_3$. In the integers, put $r = a \bmod 2$, $f = a - J_3(a)$ and
$s = \lfloor (3a + 2 - r)/2 \rfloor \bmod 2$. Then
$$2b = 3a + 1 + (1 - r)(2f - 1), \qquad 2J_3(b) = 3a + (2 - 3r)(2f - 1),$$
$$b - J_3(b) = f - (1 - r)(2f - 1), \qquad b \bmod 2 = s - (1 - r)(1 - f)(2s - 1).$$

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Lemma 1
(`integers-2024-A115-lem-1`). -/
public theorem josephusThree_highExtremal_recurrences (i : ℕ) :
    let a := Nat.nth IsJosephusThreeHighExtremal i
    let b := Nat.nth IsJosephusThreeHighExtremal (i + 1)
    let r : ℤ := (a : ℤ) % 2
    let f : ℤ := (a : ℤ) - josephus 3 a
    let s : ℤ := ((3 * (a : ℤ) + 2 - r) / 2) % 2
    2 * (b : ℤ) = 3 * a + 1 + (1 - r) * (2 * f - 1) ∧
      2 * (josephus 3 b : ℤ) = 3 * a + (2 - 3 * r) * (2 * f - 1) ∧
      (b : ℤ) - josephus 3 b = f - (1 - r) * (2 * f - 1) ∧
      (b : ℤ) % 2 = s - (1 - r) * (1 - f) * (2 * s - 1) := by
  intro a b r f s
  have ha : IsJosephusThreeHighExtremal a := Nat.nth_mem_of_infinite infinite_highExtremal i
  have hb : IsJosephusThreeHighExtremal b := Nat.nth_mem_of_infinite infinite_highExtremal (i + 1)
  obtain ⟨c, hc, hline⟩ := exists_next_highExtremal ha
  have hbc : b = c := le_antisymm
    ((Nat.nth_add_one_le_iff infinite_highExtremal hc.1.2).2 hc.1.1)
    (hc.2 ⟨Nat.nth_strictMono infinite_highExtremal (Nat.lt_succ_self i), hb⟩)
  subst c
  obtain ⟨_, haJ⟩ := ha
  obtain ⟨_, hbJ⟩ := hb
  have hf : f = 0 ∨ f = 1 := by dsimp [f]; omega
  have hr : r = 0 ∨ r = 1 := by dsimp [r]; omega
  rcases hf with hf | hf <;> rcases hr with hr | hr <;>
    simp only [s, hf, hr, Int.reduceSub, Int.reduceMul, one_mul, mul_one, sub_zero, add_zero] <;>
    dsimp [f] at hf <;> dsimp [r] at hr <;> omega

end

end MetaMathlibExt
