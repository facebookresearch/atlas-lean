/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.RelativePositionBinaryWords
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.List.GetD

/-!
# Relative position differences of periodic binary words

Advancing by one block shifts the occurrence index of each letter by its count in the block.
At a common multiple of the two counts, the resulting position shifts are constant in the
occurrence index, so they cancel when taking successive differences of the relative position.
-/

namespace MetaMathlibExt

namespace relativePosition_diff_periodic_of_periodic

variable {w : ℕ → Bool} {q : ℕ} {α : Bool}

private theorem letterCount_pos (hper : Function.Periodic w q) (hq : 0 < q)
    (hα : {i | w i = α}.Infinite) : 0 < letterCount w α q := by
  obtain ⟨i, hi⟩ := hα.nonempty
  have hmod : w (i % q + (i / q) * q) = w (i % q) := hper.nat_mul (i / q) (i % q)
  rw [Nat.mul_comm (i / q) q, Nat.mod_add_div] at hmod
  rw [letterCount, ← Nat.count_eq_card_filter_range]
  exact Nat.pos_of_ne_zero (Nat.count_ne_iff_exists.mpr
    ⟨i % q, Nat.mod_lt i hq, hmod.symm.trans hi⟩)

private theorem letterPosition_add_count (hper : Function.Periodic w q)
    (hα : {i | w i = α}.Infinite) {n : ℕ} (hn : 1 ≤ n) :
    letterPosition w α (n + letterCount w α q) = letterPosition w α n + q := by
  let p := fun i => w i = α
  let j := Nat.nth p (n - 1)
  -- `j` is the n-th occurrence, so exactly n - 1 occurrences precede it.
  have hj : p j := Nat.nth_mem_of_infinite hα _
  have hjcount : Nat.count p j = n - 1 := Nat.count_nth_of_infinite hα _
  have hshift : (fun i => p (q + i)) = p := by
    funext i
    simp only [p, Nat.add_comm q i, hper i]
  have hj' : p (q + j) := congrFun hshift j ▸ hj
  have hqcount : Nat.count p q = letterCount w α q := Nat.count_eq_card_filter_range p q
  have hcount : Nat.count p (q + j) = n + letterCount w α q - 1 := by
    simp only [Nat.count_add, hshift, hjcount, hqcount]
    omega
  change Nat.nth p (n + letterCount w α q - 1) = j + q
  rw [← hcount, Nat.nth_count hj', Nat.add_comm]

private theorem letterPosition_add_mul_count (hper : Function.Periodic w q)
    (hα : {i | w i = α}.Infinite) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    letterPosition w α (n + letterCount w α q * k) = letterPosition w α n + q * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, letterPosition_add_count hper hα (by omega), ih,
      Nat.mul_succ, Nat.add_assoc]

private theorem diff_period_of_period (hw : BothLettersInfinite w)
    (hper : Function.Periodic w q) (hq : 0 < q) :
    let L := Nat.lcm (letterCount w true q) (letterCount w false q)
    0 < L ∧ ∀ n, 1 ≤ n →
      relativePosition w (n + L + 1) - relativePosition w (n + L) =
        relativePosition w (n + 1) - relativePosition w n := by
  let a := letterCount w true q
  let b := letterCount w false q
  let L := Nat.lcm a b
  change 0 < L ∧ _
  refine ⟨Nat.lcm_pos (letterCount_pos hper hq hw.1) (letterCount_pos hper hq hw.2), ?_⟩
  obtain ⟨ka, ha⟩ := Nat.dvd_lcm_left a b
  obtain ⟨kb, hb⟩ := Nat.dvd_lcm_right a b
  have ashift (n : ℕ) (hn : 1 ≤ n) :
      letterPosition w true (n + L) = letterPosition w true n + q * ka := by
    rw [show L = a * ka from ha]
    exact letterPosition_add_mul_count hper hw.1 hn ka
  have bshift (n : ℕ) (hn : 1 ≤ n) :
      letterPosition w false (n + L) = letterPosition w false n + q * kb := by
    rw [show L = b * kb from hb]
    exact letterPosition_add_mul_count hper hw.2 hn kb
  intro n hn
  have hn' : 1 ≤ n + 1 := by omega
  change relativePosition w (n + L + 1) - relativePosition w (n + L) =
    relativePosition w (n + 1) - relativePosition w n
  rw [show n + L + 1 = n + 1 + L by ac_rfl]
  simp only [relativePosition, ashift n hn, bshift n hn, ashift (n + 1) hn',
    bshift (n + 1) hn', Int.natCast_add]
  omega

private theorem letterCount_eq_count_of_prefix (w : ℕ → Bool) (α : Bool) (u : List Bool)
    (h : ∀ i < u.length, w i = u.getD i false) : letterCount w α u.length = u.count α := by
  induction u generalizing w with
  | nil => simp [letterCount_zero]
  | cons b u ih =>
    have h₀ : w 0 = b := h 0 (by simp)
    have hs (i : ℕ) (hi : i < u.length) : w (i + 1) = u.getD i false := by
      simpa only [List.getD_cons_succ] using h (i + 1) (Nat.succ_lt_succ hi)
    have htail := ih (fun i => w (i + 1)) hs
    simp only [letterCount, ← Nat.count_eq_card_filter_range] at htail ⊢
    rw [List.length_cons, Nat.count_add', Nat.count_one, htail, h₀, List.count_cons]
    cases b <;> cases α <;> rfl

end relativePosition_diff_periodic_of_periodic

open relativePosition_diff_periodic_of_periodic in
/-- **Periodicity of the relative position differences.** Let $w = w_0 w_1 w_2 \cdots$ be an
infinite word over $\{a, b\}$ in which both letters occur infinitely often, let $p_a(n)$ and
$p_b(n)$ be the positions of the $n$-th $a$ and the $n$-th $b$ in $w$, let
$r(n) = p_b(n) - p_a(n)$, and let $\Delta r(n) = r(n + 1) - r(n)$. If $w$ is purely periodic
(there is $q > 0$ with $w_{i + q} = w_i$ for all $i \ge 0$), then there is $q > 0$ with
$\Delta r(n + q) = \Delta r(n)$ for all $n \ge 1$. Moreover, if $w = uuu\cdots$ for a nonempty
finite word $u$ containing $k$ letters $a$ and $j$ letters $b$, then
$\Delta r(n + \operatorname{lcm}(k, j)) = \Delta r(n)$ for all $n \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 17
(`jis-2025-25.1.5-cor-17`). -/
public theorem relativePosition_diff_periodic_of_periodic {w : ℕ → Bool}
    (hw : BothLettersInfinite w) :
    let dr := fun n => relativePosition w (n + 1) - relativePosition w n
    ((∃ q, 0 < q ∧ ∀ i, w (i + q) = w i) → ∃ q, 0 < q ∧ ∀ n, 1 ≤ n → dr (n + q) = dr n) ∧
      ∀ u : List Bool, 0 < u.length → (∀ i, w i = u.getD (i % u.length) false) →
        ∀ n, 1 ≤ n → dr (n + Nat.lcm (u.count true) (u.count false)) = dr n := by
  dsimp only
  constructor
  · rintro ⟨q, hq, hper⟩
    exact ⟨_, diff_period_of_period hw hper hq⟩
  · intro u hu h
    have hper : Function.Periodic w u.length := by
      intro i
      rw [h (i + u.length), Nat.add_mod_right, ← h i]
    have hcount (α : Bool) : letterCount w α u.length = u.count α :=
      letterCount_eq_count_of_prefix w α u fun i hi => by
        simpa only [Nat.mod_eq_of_lt hi] using h i
    have hdiff := (diff_period_of_period hw hper hu).2
    rwa [hcount true, hcount false] at hdiff

end MetaMathlibExt
