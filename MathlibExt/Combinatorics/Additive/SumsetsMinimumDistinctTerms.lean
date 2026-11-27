/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import MathlibExt.Combinatorics.AP.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Data.ZMod.Basic
import MathlibExt.Combinatorics.Additive.VosperTheorem

/-!
# Sumsets in cyclic groups

This file proves the Cauchy–Davenport bound for iterated sumsets modulo a prime
and Vosper's characterization of equality when the sumset omits at least two residues.
It also proves Bajnok's lemma, which realizes every residue modulo `d` as a sum
of `t` distinct residues for each `0 < t < d`.
-/

namespace MetaMathlibExt

open Finset
open scoped Pointwise

/-- **Cauchy–Davenport theorem for $h$-fold sumsets.** Let $p$ be a prime, $A$ a nonempty subset
of $\mathbb{Z}/p\mathbb{Z}$ with $|A| = k$, and $h \ge 1$ a natural number. Then the $h$-fold
sumset $hA = \{a_1 + \dots + a_h : a_1, \dots, a_h \in A\}$ satisfies
$|hA| \ge \min(p,\ hk - h + 1)$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 1 (Cauchy–Davenport theorem) (`integers-2025-A12-thm-1`). -/
public theorem cauchy_davenport_nsmul {p : ℕ} (hp : p.Prime) (A : Finset (ZMod p))
    (hA : A.Nonempty) (h : ℕ) (hh : 1 ≤ h) :
    min p (h * A.card - h + 1) ≤ (h • A).card := by
  have hcard : 1 ≤ A.card := hA.card_pos
  suffices min p (h * (A.card - 1) + 1) ≤ (h • A).card by
    simpa only [Nat.mul_sub_left_distrib, Nat.mul_one] using this
  induction h, hh using Nat.le_induction with
  | base =>
    simpa only [one_mul, Nat.sub_add_cancel hcard, one_nsmul] using min_le_right p A.card
  | succ h _ ih =>
    have hne : (h • A).Nonempty := hA.nsmul
    rw [succ_nsmul]
    refine (le_min (min_le_left _ _) ?_).trans (ZMod.cauchy_davenport hp hne hA)
    rcases min_le_iff.mp ih with hsat | hgrowth
    · -- A nonempty summand preserves saturation.
      have hsat' : p ≤ (h • A).card + A.card - 1 := by omega
      exact (min_le_left _ _).trans hsat'
    · exact (min_le_right _ _).trans (by rw [Nat.succ_mul]; omega)

/-- **Vosper's theorem for iterated sumsets.** Let $p$ be a prime, let $A$ be a subset of the
cyclic group $\mathbb{Z}/p\mathbb{Z}$ with $k = |A| \ge 2$ elements, let $h \ge 2$ be an integer,
and let $hA = \{a_1 + \dots + a_h : a_1, \dots, a_h \in A\}$ be the $h$-fold sumset of $A$. If
$|hA| = hk - h + 1$ and $hk - h + 1 \le p - 2$, then $A$ is an arithmetic progression of
length $k$ in $\mathbb{Z}/p\mathbb{Z}$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 3 (Vosper's theorem) (`integers-2025-A12-thm-3`). -/
public theorem vosper_nsmul {p : ℕ} (hp : p.Prime) (A : Finset (ZMod p))
    (hk : 2 ≤ A.card) (h : ℕ) (hh : 2 ≤ h) (hcard : (h • A).card = h * A.card - h + 1)
    (hsmall : h * A.card - h + 1 ≤ p - 2) :
    (A : Set (ZMod p)).IsAPOfLength A.card := by
  have : Fact p.Prime := ⟨hp⟩
  have hp₂ := hp.two_le
  have hA : A.Nonempty := card_pos.mp (by omega)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show h ≠ 0 by omega)
  have hn : 1 ≤ n := by omega
  have hB : (n • A).Nonempty := hA.nsmul
  rw [← Nat.mul_sub_one, Nat.succ_mul] at hcard hsmall
  rw [succ_nsmul] at hcard
  -- The lower bound for nA forces equality in the last Cauchy–Davenport step.
  have hprev := cauchy_davenport_nsmul hp A hA n hn
  rw [← Nat.mul_sub_one, min_eq_right (by omega)] at hprev
  have hcd := ZMod.cauchy_davenport hp hB hA
  have hcrit : (n • A + A).card = (n • A).card + A.card - 1 := by omega
  have hproper : n • A + A ≠ univ := by
    intro heq
    rw [heq, card_univ, ZMod.card] at hcard
    omega
  have hpos : 0 < n * (A.card - 1) := Nat.mul_pos hn (by omega)
  rcases (vosper_eq_iff (n • A) A hB hA hproper).mp hcrit with hmin | ⟨hfull, _⟩ | hAP
  · omega
  · omega
  · obtain ⟨d, _, a, _, ha⟩ := hAP
    exact ⟨a, d, ha⟩

/-- **Bajnok's lemma on subset sums in $\mathbb{Z}/d\mathbb{Z}$.** Let $d$ and $t$ be natural
numbers with $1 \le t \le d - 1$. Then every $\ell \in \mathbb{Z}/d\mathbb{Z}$ is the sum of the
elements of some $t$-element subset $L \subseteq \mathbb{Z}/d\mathbb{Z}$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Lemma 1 (Bajnok) (`integers-2025-A12-lem-1`). -/
public theorem exists_card_eq_sum_eq_zmod (d t : ℕ) (ht : 1 ≤ t) (htd : t ≤ d - 1)
    (ℓ : ZMod d) :
    ∃ L : Finset (ZMod d), L.card = t ∧ L.sum id = ℓ := by
  have : NeZero d := ⟨by omega⟩
  let I := range (t + 1)
  let S := ∑ i ∈ I, (i : ZMod d)
  -- Erasing the remainder and translating by minus the quotient subtracts the whole offset.
  let n := (S - ℓ).val
  let r := n % t
  let q := n / t
  have hr : r ∈ I := mem_range.mpr ((Nat.mod_lt n ht).trans (Nat.lt_succ_self t))
  have hcard : (I.erase r).card = t := by simp [card_erase_of_mem hr, I]
  have hlt {i : ℕ} (hi : i ∈ I.erase r) : i < d := by
    have := mem_range.mp (mem_of_mem_erase hi : i ∈ I)
    omega
  let shift (i : ℕ) := (i : ZMod d) - q
  have hinj : Set.InjOn shift (I.erase r) := by
    intro a ha b hb hab
    exact CharP.natCast_injOn_Iio (ZMod d) d (hlt ha) (hlt hb) (sub_left_inj.mp hab)
  refine ⟨(I.erase r).image shift, (card_image_of_injOn hinj).trans hcard, ?_⟩
  simp only [sum_image hinj, id_eq, shift, sum_sub_distrib]
  rw [sum_erase_eq_sub hr, sum_const, hcard, nsmul_eq_mul, sub_sub, ← Nat.cast_mul,
    ← Nat.cast_add, Nat.mod_add_div, ZMod.natCast_zmod_val, sub_sub_cancel]

end MetaMathlibExt
