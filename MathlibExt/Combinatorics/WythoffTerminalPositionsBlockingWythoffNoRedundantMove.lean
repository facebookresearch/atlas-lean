/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.BlockingWythoff
public import MathlibExt.Combinatorics.WythoffMexGoldenRatio
public import MathlibExt.Combinatorics.WythoffTerminalPositions
import Mathlib.Tactic.Linarith

/-!
# No redundant move in blocking Wythoff Nim

Removing any positive horizontal, vertical or diagonal move leaves a position outside each
of Larsson's sets with fewer than the required number of options into that set.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Theorem 31.
-/

namespace MetaMathlibExt

@[expose] public section

namespace blockingWythoff_no_redundant_move

open scoped goldenRatio

private noncomputable def a (n : ℕ) : ℕ := 2 * ⌊(n : ℝ) * φ⌋₊ + 2

private noncomputable def b (n : ℕ) : ℕ := 2 * ⌊(n : ℝ) * φ ^ 2⌋₊ + 2

private theorem b_eq (n : ℕ) : b n = a n + 2 * n := by
  have hf : ⌊(n : ℝ) * φ ^ 2⌋₊ = ⌊(n : ℝ) * φ⌋₊ + n := by
    rw [Real.goldenRatio_sq, mul_add, mul_one, Nat.floor_add_natCast]
    exact mul_nonneg n.cast_nonneg Real.goldenRatio_pos.le
  simp only [a, b, hf, Nat.mul_add]
  omega

private theorem mem_two (u w : ℕ) : (u, w) ∈ larssonSetTwo ↔
    (u = 0 ∧ w = 0) ∨ w = 2 * u + 1 ∨ u = 2 * w + 1 ∨
      ∃ n, (u = a n ∧ w = b n) ∨ (u = b n ∧ w = a n) := by
  simp only [larssonSetTwo, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    Prod.mk.injEq, a, b]
  grind

private theorem mem_three (u w : ℕ) : (u, w) ∈ larssonSetThree ↔
    (u = 0 ∧ w = 0) ∨ w = 2 * u + 1 ∨ u = 2 * w + 1 ∨
      w = 2 * u + 2 ∨ u = 2 * w + 2 := by
  simp only [larssonSetThree, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    Prod.mk.injEq]
  grind

private theorem move (x z u w : ℕ) : wythoffTerminalMove 0 (x, z) (u, w) ↔
    (w = z ∧ u < x) ∨ (u = x ∧ w < z) ∨ (u < x ∧ x + w = u + z) := by
  constructor
  · rintro ⟨_, h | h | ⟨k, hk, hu, hw⟩⟩ <;> omega
  · intro h
    refine ⟨by omega, ?_⟩
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨x - u, by omega, by omega, by omega⟩)

private theorem b_spacing (m n : ℕ) (h : m + 2 ≤ n) : b m + 10 ≤ b n := by
  have hφ : (5 : ℝ) ≤ 2 * φ ^ 2 := by
    have hs : (2 : ℝ) < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    rw [Real.goldenRatio_sq]
    dsimp [Real.goldenRatio]
    linarith
  have hr : (m : ℝ) * φ ^ 2 + 5 ≤ (n : ℝ) * φ ^ 2 := by
    have hc : (m : ℝ) + 2 ≤ n := by exact_mod_cast h
    nlinarith [sq_nonneg φ]
  have hf := Nat.floor_le_floor hr
  have he : ⌊(m : ℝ) * φ ^ 2 + 5⌋₊ = ⌊(m : ℝ) * φ ^ 2⌋₊ + 5 := by
    simpa only [Nat.cast_ofNat] using
      Nat.floor_add_natCast (mul_nonneg m.cast_nonneg (sq_nonneg φ)) 5
  rw [he] at hf
  unfold b
  omega

private theorem b_gap (m n : ℕ) (h : m < n) : b m + 4 ≤ b n := by
  have hφ : (2 : ℝ) ≤ φ ^ 2 := by
    rw [Real.goldenRatio_sq]
    linarith [Real.one_lt_goldenRatio]
  have hr : (m : ℝ) * φ ^ 2 + 2 ≤ (n : ℝ) * φ ^ 2 := by
    have hc : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    nlinarith [sq_nonneg φ]
  have hf := Nat.floor_le_floor hr
  have he : ⌊(m : ℝ) * φ ^ 2 + 2⌋₊ = ⌊(m : ℝ) * φ ^ 2⌋₊ + 2 := by
    simpa only [Nat.cast_ofNat] using
      Nat.floor_add_natCast (mul_nonneg m.cast_nonneg (sq_nonneg φ)) 2
  rw [he] at hf
  unfold b
  omega

private theorem b_strictMono : StrictMono b := by
  intro m n h
  have := b_gap m n h
  omega

private theorem missing_upper (m : ℕ) :
    (∀ n, b n ≠ m) ∨ (∀ n, b n ≠ m + 4) ∨ (∀ n, b n ≠ m + 8) := by
  by_contra h
  push Not at h
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, r, hr⟩ := h
  have hpq : p < q := b_strictMono.lt_iff_lt.mp (by omega)
  have hqr : q < r := b_strictMono.lt_iff_lt.mp (by omega)
  have := b_spacing p r (by omega)
  omega

private theorem axis_two (i : ℕ) (hi : 0 < i) :
    ∃ x ∉ larssonSetTwo, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo ∧
      ¬(y.1 + i = x.1 ∧ y.2 + 0 = x.2)}.ncard < 2 := by
  refine ⟨(i + 1, 0), ?_, ?_⟩
  · rw [mem_two]
    rintro (h | h | h | ⟨n, h | h⟩)
    all_goals first | omega | (have := b_eq n; unfold a at *; omega)
  · have hs : {y | wythoffTerminalMove 0 (i + 1, 0) y ∧ y ∈ larssonSetTwo ∧
        ¬(y.1 + i = i + 1 ∧ y.2 + 0 = 0)} ⊆ {(0, 0)} := by
      rintro ⟨u, w⟩ ⟨hm, hs, hv⟩
      have hm' := (move _ _ _ _).mp hm
      have hs' := (mem_two _ _).mp hs
      change (u, w) = (0, 0)
      apply Prod.ext <;> dsimp
      all_goals rcases hs' with h | h | h | ⟨n, h | h⟩
      all_goals first | omega | (have := b_eq n; unfold a at *; omega)
    have hc := Set.ncard_le_ncard hs (Set.finite_singleton _)
    rw [Set.ncard_singleton] at hc
    exact lt_of_le_of_lt hc (by decide)

private theorem axis_three (i : ℕ) (hi : 0 < i) :
    ∃ x ∉ larssonSetThree, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetThree ∧
      ¬(y.1 + i = x.1 ∧ y.2 + 0 = x.2)}.ncard < 3 := by
  refine ⟨(i + 2, 0), ?_, ?_⟩
  · rw [mem_three]
    omega
  · have hs : {y | wythoffTerminalMove 0 (i + 2, 0) y ∧ y ∈ larssonSetThree ∧
        ¬(y.1 + i = i + 2 ∧ y.2 + 0 = 0)} ⊆ {(0, 0), (1, 0)} := by
      rintro ⟨u, w⟩ ⟨hm, hs, hv⟩
      have hm' := (move _ _ _ _).mp hm
      have hs' := (mem_three _ _).mp hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    have hc := Set.ncard_le_ncard hs (Set.toFinite _)
    rw [Set.ncard_pair (by decide : (0, 0) ≠ (1, 0))] at hc
    exact lt_of_le_of_lt hc (by decide)

private theorem diagonal_three (i : ℕ) (hi : 0 < i) :
    ∃ x ∉ larssonSetThree, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetThree ∧
      ¬(y.1 + i = x.1 ∧ y.2 + i = x.2)}.ncard < 3 := by
  refine ⟨(i, i), ?_, ?_⟩
  · rw [mem_three]
    omega
  · have hs : {y | wythoffTerminalMove 0 (i, i) y ∧ y ∈ larssonSetThree ∧
        ¬(y.1 + i = i ∧ y.2 + i = i)} ⊆ {((i - 1) / 2, i), (i, (i - 1) / 2)} := by
      rintro ⟨u, w⟩ ⟨hm, hs, hv⟩
      have hm' := (move _ _ _ _).mp hm
      have hs' := (mem_three _ _).mp hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    have hc := Set.ncard_le_ncard hs (Set.toFinite _)
    have hn : ((i - 1) / 2, i) ≠ (i, (i - 1) / 2) := by
      simp only [ne_eq, Prod.mk.injEq]
      omega
    rw [Set.ncard_pair hn] at hc
    exact lt_of_le_of_lt hc (by decide)

private theorem diagonal_two_position (i m : ℕ) (hm : m = i ∨ m = i + 2)
    (hlarge : 4 ≤ m) (heven : m % 2 = 0) (hmissing : ∀ n, b n ≠ m) :
    ∃ x ∉ larssonSetTwo, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo ∧
      ¬(y.1 + i = x.1 ∧ y.2 + i = x.2)}.ncard < 2 := by
  refine ⟨(m, m), ?_, ?_⟩
  · rw [mem_two]
    rintro (h | h | h | ⟨n, h | h⟩)
    all_goals first | omega | (have := b_eq n; have := hmissing n; omega)
  · have htargets (u w : ℕ) (hmove : wythoffTerminalMove 0 (m, m) (u, w))
        (hset : (u, w) ∈ larssonSetTwo) : u = w ∧ (u = 0 ∨ u = 2) := by
      have hm' := (move _ _ _ _).mp hmove
      rcases (mem_two _ _).mp hset with h | h | h | ⟨n, h | h⟩
      all_goals try omega
      all_goals
        have hb := b_eq n
        have hn : n = 0 := by
          have := hmissing n
          omega
        subst n
        simp only [a, b, Nat.cast_zero, zero_mul, Nat.floor_zero, mul_zero, zero_add] at h
        omega
    let t := if m = i then 2 else 0
    have hs : {y | wythoffTerminalMove 0 (m, m) y ∧ y ∈ larssonSetTwo ∧
        ¬(y.1 + i = m ∧ y.2 + i = m)} ⊆ {(t, t)} := by
      rintro ⟨u, w⟩ ⟨hmove, hset, hv⟩
      have := htargets u w hmove hset
      simp only [Set.mem_singleton_iff, Prod.mk.injEq]
      dsimp [t]
      split_ifs <;> omega
    have hc := Set.ncard_le_ncard hs (Set.finite_singleton _)
    rw [Set.ncard_singleton] at hc
    exact lt_of_le_of_lt hc (by decide)

private theorem diagonal_even_two (i : ℕ) (hi : 0 < i) (heven : i % 2 = 0) :
    ∃ x ∉ larssonSetTwo, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo ∧
      ¬(y.1 + i = x.1 ∧ y.2 + i = x.2)}.ncard < 2 := by
  by_cases hm : ∀ n, b n ≠ i + 2
  · exact diagonal_two_position i (i + 2) (Or.inr rfl) (by omega) (by omega) hm
  · push Not at hm
    obtain ⟨q, hq⟩ := hm
    have hn : ∀ p, b p ≠ i := by
      intro p hp
      have hpq : p < q := b_strictMono.lt_iff_lt.mp (by omega)
      have := b_gap p q hpq
      omega
    have hlarge : 4 ≤ i := by
      by_contra h
      have hi2 : i = 2 := by omega
      subst i
      have hq0 : 0 < q := by
        by_contra h
        have : q = 0 := by omega
        subst q
        simp [b] at hq
      have := b_gap 0 q hq0
      have hb0 : b 0 = 2 := by simp [b]
      rw [hb0, hq] at this
      omega
    exact diagonal_two_position i i (Or.inl rfl) hlarge heven hn

private theorem ray_diagonal_two (i n : ℕ) (hi : 0 < i) (hodd : i % 2 = 1)
    (heven : n % 2 = 0) (hmissing : ∀ k, b k ≠ i + 2 * n + 1) :
    ∃ x ∉ larssonSetTwo, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo ∧
      ¬(y.1 + i = x.1 ∧ y.2 + i = x.2)}.ncard < 2 := by
  refine ⟨(i + n, i + 2 * n + 1), ?_, ?_⟩
  · rw [mem_two]
    rintro (h | h | h | ⟨k, h | h⟩)
    all_goals first | omega | (unfold a b at h; omega)
  · have hs : {y | wythoffTerminalMove 0 (i + n, i + 2 * n + 1) y ∧
        y ∈ larssonSetTwo ∧ ¬(y.1 + i = i + n ∧ y.2 + i = i + 2 * n + 1)} ⊆
        {(i + n, (i + n - 1) / 2)} := by
      rintro ⟨u, w⟩ ⟨hmove, hset, hv⟩
      have hm' := (move _ _ _ _).mp hmove
      simp only [Set.mem_singleton_iff, Prod.mk.injEq]
      rcases (mem_two _ _).mp hset with h | h | h | ⟨k, h | h⟩
      all_goals try omega
      all_goals
        have hb := b_eq k
        have ha : a k % 2 = 0 := by unfold a; omega
        have hmiss := hmissing k
        omega
    have hc := Set.ncard_le_ncard hs (Set.finite_singleton _)
    rw [Set.ncard_singleton] at hc
    exact lt_of_le_of_lt hc (by decide)

private theorem diagonal_two (i : ℕ) (hi : 0 < i) :
    ∃ x ∉ larssonSetTwo, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo ∧
      ¬(y.1 + i = x.1 ∧ y.2 + i = x.2)}.ncard < 2 := by
  by_cases heven : i % 2 = 0
  · exact diagonal_even_two i hi heven
  · have hodd : i % 2 = 1 := by omega
    rcases missing_upper (i + 1) with h | h | h
    · exact ray_diagonal_two i 0 hi hodd (by decide) (by simpa using h)
    · exact ray_diagonal_two i 2 hi hodd (by decide) (by simpa [Nat.add_assoc] using h)
    · exact ray_diagonal_two i 4 hi hodd (by decide) (by simpa [Nat.add_assoc] using h)

private theorem swap_result (S : Set (ℕ × ℕ)) (k : ℕ) (v : ℕ × ℕ)
    (hsym : ∀ u w, (u, w) ∈ S → (w, u) ∈ S)
    (h : ∃ x ∉ S, {y | wythoffTerminalMove 0 x y ∧ y ∈ S ∧
      ¬(y.1 + v.1 = x.1 ∧ y.2 + v.2 = x.2)}.ncard < k) :
    ∃ x ∉ S, {y | wythoffTerminalMove 0 x y ∧ y ∈ S ∧
      ¬(y.1 + v.swap.1 = x.1 ∧ y.2 + v.swap.2 = x.2)}.ncard < k := by
  obtain ⟨⟨x, z⟩, hx, hc⟩ := h
  refine ⟨(z, x), fun h => hx (hsym z x h), ?_⟩
  have he : {y | wythoffTerminalMove 0 (x, z) y ∧ y ∈ S ∧
      ¬(y.1 + v.1 = x ∧ y.2 + v.2 = z)}.ncard =
      {y | wythoffTerminalMove 0 (z, x) y ∧ y ∈ S ∧
      ¬(y.1 + v.2 = z ∧ y.2 + v.1 = x)}.ncard := by
    apply Set.BijOn.ncard_eq (f := Prod.swap)
    refine ⟨?_, Prod.swap_injective.injOn, ?_⟩
    · rintro ⟨u, w⟩ ⟨hm, hs, hv⟩
      refine ⟨?_, hsym u w hs, ?_⟩
      · have := (move _ _ _ _).mp hm
        exact (move _ _ _ _).mpr (by omega)
      · dsimp at hv ⊢
        omega
    · rintro ⟨u, w⟩ ⟨hm, hs, hv⟩
      refine ⟨(w, u), ⟨?_, hsym u w hs, ?_⟩, rfl⟩
      · have := (move _ _ _ _).mp hm
        exact (move _ _ _ _).mpr (by omega)
      · dsimp at hv ⊢
        omega
  exact he ▸ hc

private theorem swap_two (u w : ℕ) (h : (u, w) ∈ larssonSetTwo) :
    (w, u) ∈ larssonSetTwo := by
  rw [mem_two] at h ⊢
  grind

private theorem swap_three (u w : ℕ) (h : (u, w) ∈ larssonSetThree) :
    (w, u) ∈ larssonSetThree := by
  rw [mem_three] at h ⊢
  omega

end blockingWythoff_no_redundant_move

/-- **Blocking Wythoff Nim with one or two blocked options has no redundant move.** Let
$\varphi$ be the golden ratio. Let $R_2$ consist of $(0, 0)$ and, for every $n \ge 0$, the
positions $(n, 2n + 1)$, $(2n + 1, n)$,
$(2\lfloor n\varphi \rfloor + 2, 2\lfloor n\varphi^2 \rfloor + 2)$ and
$(2\lfloor n\varphi^2 \rfloor + 2, 2\lfloor n\varphi \rfloor + 2)$, and let $R_3$ consist of
$(0, 0)$ and, for every $n \ge 0$, the positions $(n, 2n + 1)$, $(2n + 1, n)$, $(n, 2n + 2)$ and
$(2n + 2, n)$. A Wythoff move from a position $x$ of two piles to a position $y$ removes a
positive number of tokens from one pile, or the same positive number from both. Let $v$ be
$(i, 0)$, $(0, i)$ or $(i, i)$ for an integer $i > 0$. Then some position $x \notin R_2$ has
fewer than two Wythoff moves to positions $y \in R_2$ with $y + v \ne x$, and some position
$x \notin R_3$ has fewer than three Wythoff moves to positions $y \in R_3$ with $y + v \ne x$.

So once the moves by $v$ are removed, $R_2$ and $R_3$ are no longer the sets of P-positions of
$W^2$ and $W^3$, Wythoff's game in which the previous player may forbid one, respectively two,
options.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 31 (`jis-2026-26.1.6-thm-31`). -/
public theorem blockingWythoff_no_redundant_move (v : ℕ × ℕ)
    (hv : ∃ i, 0 < i ∧ (v = (i, 0) ∨ v = (0, i) ∨ v = (i, i))) :
    (∃ x ∉ larssonSetTwo, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo ∧
        ¬(y.1 + v.1 = x.1 ∧ y.2 + v.2 = x.2)}.ncard < 2) ∧
      ∃ x ∉ larssonSetThree, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetThree ∧
        ¬(y.1 + v.1 = x.1 ∧ y.2 + v.2 = x.2)}.ncard < 3
    := by
  obtain ⟨i, hi, rfl | rfl | rfl⟩ := hv
  · exact ⟨blockingWythoff_no_redundant_move.axis_two i hi,
      blockingWythoff_no_redundant_move.axis_three i hi⟩
  · exact ⟨blockingWythoff_no_redundant_move.swap_result _ _ (i, 0)
        blockingWythoff_no_redundant_move.swap_two
        (blockingWythoff_no_redundant_move.axis_two i hi),
      blockingWythoff_no_redundant_move.swap_result _ _ (i, 0)
        blockingWythoff_no_redundant_move.swap_three
        (blockingWythoff_no_redundant_move.axis_three i hi)⟩
  · exact ⟨blockingWythoff_no_redundant_move.diagonal_two i hi,
      blockingWythoff_no_redundant_move.diagonal_three i hi⟩

end

end MetaMathlibExt
