/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/845.lean` (Formal Conjectures), for the conjecture statement.
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import MathlibExt.Data.Set.Density
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum

/-!
# Erdős Problem 845

`conjecture_refuted` disproves the density-zero conjecture for sums of distinct numbers
of the form `2 ^ k * 3 ^ l`. With ratio bound `9`, the sums contain arbitrarily large
intervals `[a, 3 * a]`. Van Doorn and Everts obtain the sharper bound `6`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace MathlibExt.NumberTheory.ErdosProblem845Wanted

/-- **Erdős Problem 845.** The proposition asserts that for every real number $C > 0$, the set of
all sums $\sum_{(k, l) \in B} 2^k 3^l$, where $B$ is a nonempty finite set of pairs of natural
numbers such that $\max_{(k, l) \in B} 2^k 3^l \le C \min_{(k, l) \in B} 2^k 3^l$, has natural
density $0$. -/
def conjecture : Prop :=
  ∀ (C : ℝ), 0 < C →
    let f : ℕ × ℕ → ℕ := fun (k, l) ↦ 2 ^ k * 3 ^ l
    { ∑ x ∈ B, f x | (B : Finset (ℕ × ℕ)) (h : B.Nonempty)
      (_hB : B.sup f ≤ C * B.inf' h f) }.HasDensity 0

private abbrev value (x : ℕ × ℕ) : ℕ := 2 ^ x.1 * 3 ^ x.2

/-- Sums of distinct terms in the band from `q` to `9 * q`. -/
private def InBand (q n : ℕ) : Prop :=
  ∃ B : Finset (ℕ × ℕ), (∀ x ∈ B, q ≤ value x ∧ value x ≤ 9 * q) ∧ ∑ x ∈ B, value x = n

/-- The subset sums of `{1, 2, 3, 4, 8}` cover the initial interval `[6, 18]`. -/
private lemma initial_band (n : ℕ) (hn : 6 ≤ n) (hn' : n ≤ 18) : InBand 1 n := by
  let seed : Finset (ℕ × ℕ) := {(0, 0), (1, 0), (0, 1), (2, 0), (3, 0)}
  have hs : ∀ x ∈ seed, 1 ≤ value x ∧ value x ≤ 9 * 1 := by decide
  have h : ∀ i : Fin 13, ∃ B ∈ seed.powerset, ∑ x ∈ B, value x = 6 + i.val := by decide
  obtain ⟨B, hB, hsum⟩ := h ⟨n - 6, by omega⟩
  exact ⟨B, fun x hx ↦ hs x (Finset.mem_powerset.mp hB hx), by simpa [hn] using hsum⟩

/-- Double the old summands and adjoin any chosen powers of three in the new band. -/
private lemma double_add {q m : ℕ} (hm : InBand q m) (D : Finset ℕ)
    (hD : ∀ j ∈ D, 2 * q ≤ 3 ^ j ∧ 3 ^ j ≤ 9 * (2 * q)) :
    InBand (2 * q) (2 * m + ∑ j ∈ D, 3 ^ j) := by
  obtain ⟨B, hB, hsum⟩ := hm
  let shift : (ℕ × ℕ) ↪ (ℕ × ℕ) :=
    ⟨fun x ↦ (x.1 + 1, x.2), fun x y h ↦ Prod.ext (by simpa using congrArg Prod.fst h)
      (Prod.mk.inj h).2⟩
  let oddTerm : ℕ ↪ (ℕ × ℕ) := ⟨fun j ↦ (0, j), fun _ _ h ↦ congrArg Prod.snd h⟩
  have hshift (x : ℕ × ℕ) : value (shift x) = 2 * value x := by
    change 2 ^ (x.1 + 1) * 3 ^ x.2 = 2 * (2 ^ x.1 * 3 ^ x.2)
    rw [pow_succ', Nat.mul_assoc]
  have hodd (j : ℕ) : value (oddTerm j) = 3 ^ j := by
    change 2 ^ 0 * 3 ^ j = 3 ^ j
    simp
  have hd : Disjoint (B.map shift) (D.map oddTerm) := by
    rw [Finset.disjoint_left]
    rintro _ hx hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hy
    exact Nat.noConfusion (congrArg Prod.fst hj)
  refine ⟨B.map shift ∪ D.map oddTerm, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      rw [hshift]
      obtain ⟨hlo, hhi⟩ := hB y hy
      omega
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
      simpa only [hodd] using hD j hj
  · rw [Finset.sum_union hd, Finset.sum_map, Finset.sum_map]
    simp only [hshift, hodd, ← Finset.mul_sum, hsum]

/-- Each parity has two possible offsets. The intervals they produce overlap since `p ≤ a`. -/
private lemma choose_offset {a p n : ℕ} (hp : p % 2 = 1) (hpa : p ≤ a)
    (hlo : 2 * a + p ≤ n) (hhi : n ≤ 3 * (2 * a + p)) :
    ∃ m, a ≤ m ∧ m ≤ 3 * a ∧
      (n = 2 * m ∨ n = 2 * m + p ∨ n = 2 * m + 3 * p ∨ n = 2 * m + 4 * p) := by
  by_cases he : n % 2 = 0
  · by_cases hn : n ≤ 6 * a
    · exact ⟨n / 2, by omega⟩
    · exact ⟨(n - 4 * p) / 2, by omega⟩
  · by_cases hn : n ≤ 6 * a + p
    · exact ⟨(n - p) / 2, by omega⟩
    · exact ⟨(n - 3 * p) / 2, by omega⟩

/-- At each scale there is a whole interval of representable sums.
Doubling the preceding interval leaves room for the two odd terms `p` and `3 * p`. -/
private lemma band_intervals (k : ℕ) :
    ∃ a, 6 * 2 ^ k ≤ a ∧ ∀ n, a ≤ n → n ≤ 3 * a → InBand (2 ^ k) n := by
  induction k with
  | zero => exact ⟨6, by decide, by simpa using initial_band⟩
  | succ k ih =>
    obtain ⟨a, ha, h⟩ := ih
    let q := 2 ^ k
    let j := Nat.log 3 (2 * q) + 1
    let p := 3 ^ j
    have hq : 0 < q := pow_pos (by decide) _
    have hlo : 2 * q ≤ p := (Nat.lt_pow_succ_log_self (by decide : 1 < 3) _).le
    have hhi : p ≤ 6 * q := by
      have := Nat.pow_log_le_self 3 (show 2 * q ≠ 0 by omega)
      dsimp [p, j]
      rw [pow_succ]
      omega
    change 6 * q ≤ a at ha
    rw [pow_succ']
    change ∃ a', 6 * (2 * q) ≤ a' ∧ _
    refine ⟨2 * a + p, by omega, ?_⟩
    intro n hn hn'
    have hp : p % 2 = 1 := Nat.odd_iff.mp ((by decide : Odd (3 : ℕ)).pow (n := j))
    obtain ⟨m, hm, hm', hoff⟩ := choose_offset hp (by omega) hn hn'
    have extend := double_add (h m hm hm')
    have hj : 2 * q ≤ 3 ^ j ∧ 3 ^ j ≤ 9 * (2 * q) := by
      change _ ≤ p ∧ p ≤ _
      omega
    have hj' : 2 * q ≤ 3 ^ (j + 1) ∧ 3 ^ (j + 1) ≤ 9 * (2 * q) := by
      rw [pow_succ]
      change _ ≤ p * 3 ∧ p * 3 ≤ _
      omega
    rcases hoff with rfl | rfl | rfl | rfl
    · simpa using extend ∅ (by simp)
    · simpa [p] using extend {j} (by simpa using hj)
    · simpa [pow_succ', p] using extend {j + 1} (by simpa using hj')
    · have he := extend {j, j + 1} (by simpa using And.intro hj hj')
      simpa [pow_succ', p, show 3 ^ j + 3 * 3 ^ j = 4 * 3 ^ j by omega] using he

/--
**Erdős Problem 845 is false.** There is a real number $C > 0$ such that the set of all sums
$\sum_{(k, l) \in B} 2^k 3^l$, where $B$ is a nonempty finite set of pairs of natural numbers such
that $\max_{(k, l) \in B} 2^k 3^l \le C \min_{(k, l) \in B} 2^k 3^l$, does not have natural
density $0$.

Van Doorn and Everts obtain a counterexample with $C = 6$.

Source:
Wouter van Doorn and Anneroos R. F. Everts, Smooth sums with small spacings, arXiv:2511.04585v1
(2025), https://arxiv.org/abs/2511.04585v1. Moved from
`OpenConjectures/NumberTheory/ErdosProblem845`.
-/
theorem conjecture_refuted : ¬ conjecture := by
  intro h
  let S := { ∑ x ∈ B, value x | (B : Finset (ℕ × ℕ)) (h : B.Nonempty)
    (_ : B.sup value ≤ (9 : ℝ) * B.inf' h value) }
  have hz : S.HasDensity 0 := h 9 (by norm_num)
  have hev := hz.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  obtain ⟨a, ha, hrep⟩ := band_intervals N
  have hlarge : N < 2 ^ N := Nat.lt_two_pow_self
  have hsub : Set.Ico a (3 * a) ⊆ S ∩ Set.Iio (3 * a) := by
    intro n ⟨hlo, hhi⟩
    obtain ⟨B, hB, hsum⟩ := hrep n hlo hhi.le
    have hne : B.Nonempty := by
      by_contra! hempty
      simp [hempty] at hsum
      omega
    refine ⟨⟨B, hne, ?_, hsum⟩, hhi⟩
    have hmax := B.sup_le (fun x hx ↦ (hB x hx).2)
    have hmin := Finset.le_inf' hne value (fun x hx ↦ (hB x hx).1)
    exact_mod_cast hmax.trans (Nat.mul_le_mul_left 9 hmin)
  have hcard := Set.ncard_le_ncard hsub ((Set.finite_Iio _).subset Set.inter_subset_right)
  rw [Set.ncard_Ico_nat] at hcard
  have hcount : 2 * a ≤ (S ∩ Set.Iio (3 * a)).ncard := by omega
  have hlt := hN (3 * a) (by omega)
  change S.partialDensity Set.univ (3 * a) < 1 / 2 at hlt
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat] at hlt
  have hpos : (0 : ℝ) < (3 * a : ℕ) := by exact_mod_cast (show 0 < 3 * a by omega)
  rw [div_lt_iff₀ hpos] at hlt
  have hc : (2 : ℝ) * a ≤ (S ∩ Set.Iio (3 * a)).ncard := by exact_mod_cast hcount
  push_cast at hlt hpos
  linarith

end MathlibExt.NumberTheory.ErdosProblem845Wanted
