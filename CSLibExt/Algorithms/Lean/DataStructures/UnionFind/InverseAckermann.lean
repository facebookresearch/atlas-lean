/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.SequenceCost
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# The inverse-Ackermann bound for union by rank with path compression

Tarjan and van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2) (1984)
245–281, §3, Theorem 3: the set union algorithm with linking by rank (or by size) and
compression (or splitting, or halving) runs in `O(n + m α(m + n, n))` time, where `n` is the
number of make-set operations, `m` the number of finds and `α` their inverse Ackermann
function. The bound is optimal for separable algorithms (their §1, Theorem 2). Their proof
uses, and extends, the multiple partition technique of Tarjan, *Efficiency of a good but not
linear set union algorithm*, J. ACM 22(2) (1975) 215–225 (their §3).

The statement uses the cost model of `CSLibExt.Algorithms.Lean.DataStructures.UnionFind.
SequenceCost` for the canonical Batteries union-find (`find` with path compression, union by
rank): a make-set and a link cost one, a find costs the number of nodes on its find path, and a
union is two finds and a link. The weaker `O(n + m log n)` bound is proved as
`UnionByRank.run_empty_cost_le_log`.

The proof counts how many iterated rank thresholds each node's parent has crossed. On a find
path, an edge pays for its visit if an edge farther toward the root crosses a threshold at
the same level. The unpaid edges have distinct levels. The total number of crossings is bounded
using the sum of the ranks and the number of nonroots, both of which can only grow at links.
-/

open Batteries
open scoped BigOperators

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionByRank

namespace run_empty_cost_le_inverseAckermann

/-! ## Rank thresholds -/

private theorem le_iterate {f : ℕ → ℕ} (h : ∀ x, 2 ≤ x → x ≤ f x) {r : ℕ}
    (hr : 2 ≤ r) (j : ℕ) : r ≤ f^[j] r := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (h _ (hr.trans ih))

private theorem iterate_le_iterate {f : ℕ → ℕ} (h : ∀ ⦃x y⦄, 2 ≤ x → x ≤ y → f x ≤ f y)
    (hg : ∀ x, 2 ≤ x → x ≤ f x) {r p : ℕ} (hr : 2 ≤ r) (hp : r ≤ p) (j : ℕ) :
    f^[j] r ≤ f^[j] p := by
  induction j with
  | zero => exact hp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact h (hr.trans (le_iterate hg hr j)) ih

private theorem ack_row_succ (i j : ℕ) :
    ackermannTvL (i + 2) (j + 1) = (ackermannTvL (i + 1))^[j + 1] 2 := by
  induction j with
  | zero => simp [ackermannTvL]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rw [ackermannTvL]

private theorem ack_double (i : ℕ) :
    (∀ j, 1 ≤ j → 2 * j ≤ ackermannTvL (i + 1) j) ∧
    (∀ j, 1 ≤ j → 2 * ackermannTvL (i + 1) j ≤ ackermannTvL (i + 1) (j + 1)) := by
  induction i with
  | zero =>
    constructor
    · intro j _
      simpa only [Nat.zero_add, ackermannTvL] using Nat.mul_le_pow (by decide : (2 : ℕ) ≠ 1) j
    · intro j _
      simp [ackermannTvL, pow_succ, Nat.mul_comm]
  | succ i ih =>
    have step (j : ℕ) : 2 * ackermannTvL (i + 2) (j + 1) ≤
        ackermannTvL (i + 2) (j + 2) := by
      have pos (j : ℕ) : 2 ≤ ackermannTvL (i + 2) (j + 1) := by
        rw [ack_row_succ]
        exact le_iterate (fun x hx => (show x ≤ 2 * x by omega).trans
          (ih.1 x (by omega))) le_rfl _
      conv_rhs => rw [ackermannTvL]
      exact ih.1 _ (by have := pos j; omega)
    constructor
    · intro j hj
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj
      induction k with
      | zero =>
        simpa only [Nat.zero_add, ackermannTvL] using
          (show 2 * 1 ≤ ackermannTvL (i + 1) 2 from (by decide : 2 * 1 ≤ 2 * 2).trans
            (ih.1 2 (by decide)))
      | succ k ihk =>
        have ihk' : 2 * (k + 1) ≤ ackermannTvL (i + 2) (k + 1) := ihk (by omega)
        change 2 * (k + 2) ≤ ackermannTvL (i + 2) (k + 2)
        have := step k
        omega
    · intro j hj
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj
      exact step k

private theorem ack_growth (i j : ℕ) (hj : 1 ≤ j) :
    ackermannTvL (i + 1) j + 1 ≤ ackermannTvL (i + 1) (j + 1) := by
  have := (ack_double i).1 j hj
  have := (ack_double i).2 j hj
  omega

private theorem ack_diagonal (i : ℕ) : i + 2 ≤ ackermannTvL (i + 1) 1 := by
  induction i with
  | zero => simp [ackermannTvL]
  | succ i ih =>
    have hg : ackermannTvL (i + 1) 1 + 1 ≤ ackermannTvL (i + 1) 2 :=
      ack_growth i 1 (by decide)
    rw [ackermannTvL]
    omega

private theorem ack_mono {i j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    ackermannTvL (i + 1) j ≤ ackermannTvL (i + 1) k := by
  induction hjk with
  | refl => rfl
  | @step k hk ih => exact ih.trans ((ack_growth i k (hj.trans hk)).trans' (Nat.le_succ _))

-- The first two rows give thresholds for short rank gaps.
private def threshold : ℕ → ℕ → ℕ
  | 0 => fun r => r + 1
  | 1 => fun r => 2 * r
  | i + 2 => ackermannTvL (i + 1)

private theorem threshold_growth (i r : ℕ) (hr : 2 ≤ r) : r < threshold i r := by
  cases i with
  | zero => exact Nat.lt_succ_self _
  | succ i =>
    cases i with
    | zero => simp only [threshold]; omega
    | succ i =>
      have := (ack_double i).1 r (by omega)
      simp only [threshold]
      omega

private theorem threshold_mono {i r p : ℕ} (hr : 2 ≤ r) (hp : r ≤ p) :
    threshold i r ≤ threshold i p := by
  cases i with
  | zero => simp only [threshold]; omega
  | succ i =>
    cases i with
    | zero => exact Nat.mul_le_mul_left _ hp
    | succ i => exact ack_mono (by omega) hp

private theorem iterate_double (j r : ℕ) : (threshold 1)^[j] r = 2 ^ j * r := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ]
    simp only [threshold]
    ac_rfl

private theorem threshold_next (i r : ℕ) (hr : 2 ≤ r) :
    threshold (i + 1) r ≤ (threshold i)^[r] r := by
  cases i with
  | zero =>
    have eq (j : ℕ) : (threshold 0)^[j] r = r + j := by
      induction j with
      | zero => simp
      | succ j ih => rw [Function.iterate_succ_apply', ih]; rfl
    rw [eq]
    simp only [threshold]
    omega
  | succ i =>
    cases i with
    | zero =>
      rw [iterate_double]
      simpa only [threshold, Nat.zero_add, ackermannTvL] using
        Nat.le_mul_of_pos_right (2 ^ r) (show 0 < r by omega)
    | succ i =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ r by omega)
      change ackermannTvL (i + 2) (j + 1) ≤ (ackermannTvL (i + 1))^[j + 1] (j + 1)
      rw [ack_row_succ]
      apply iterate_le_iterate (fun _ _ hx => ack_mono (by omega))
        (fun x hx => (show x ≤ 2 * x by omega).trans ((ack_double i).1 x (by omega)))
        le_rfl hr

private theorem inverse_threshold {m n : ℕ} (hn : 1 ≤ n) :
    let b := (m + n) / n + 1
    let a := inverseAckermannTvL (m + n) n
    1 ≤ a ∧ 2 ≤ b ∧ Nat.log 2 n + b < threshold (a + 1) b := by
  dsimp
  let q := (m + n) / n
  have hq : 1 ≤ q := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hne : {i : ℕ | 1 ≤ i ∧ Nat.log 2 n < ackermannTvL i q}.Nonempty := by
    refine ⟨Nat.log 2 n + 1, by omega, ?_⟩
    have := (ack_diagonal (Nat.log 2 n)).trans (ack_mono (by decide) hq)
    omega
  have ha : 1 ≤ inverseAckermannTvL (m + n) n ∧
      Nat.log 2 n < ackermannTvL (inverseAckermannTvL (m + n) n) q :=
    Nat.sInf_mem hne
  obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le' ha.1
  change 1 ≤ inverseAckermannTvL (m + n) n ∧ 2 ≤ q + 1 ∧
    Nat.log 2 n + (q + 1) < threshold (inverseAckermannTvL (m + n) n + 1) (q + 1)
  have hlt := ha.2
  rw [hi] at hlt ⊢
  have hd := (ack_double i).2 q hq
  have hg := (ack_double i).1 q hq
  simp only [threshold]
  omega

/-! ## Progress under path compression -/

-- At each level count the thresholds a parent rank has crossed. Capping at the
-- child's shifted rank suffices because the next level begins by that iteration.
private def crossings (i r p : ℕ) : ℕ :=
  ((Finset.range r).filter fun j => (threshold i)^[j + 1] r ≤ p).card

private def score (K r p : ℕ) : ℕ :=
  ∑ i ∈ Finset.range K, crossings i r p

private theorem score_mono {K r p p' : ℕ} (hp : p ≤ p') :
    score K r p ≤ score K r p' :=
  Finset.sum_le_sum fun _ _ =>
    Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ h => h.trans hp)

private theorem score_le (K r p : ℕ) : score K r p ≤ K * r :=
  (Finset.sum_le_sum fun _ _ => Finset.card_filter_le _ _).trans_eq (by simp)

private theorem score_self (K r : ℕ) (hr : 2 ≤ r) : score K r r = 0 := by
  unfold score
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro j _ hj
  have h := le_iterate (fun x hx => (threshold_growth i x hx).le) hr j
  rw [Function.iterate_succ_apply'] at hj
  have hg := threshold_growth i ((threshold i)^[j] r) (hr.trans h)
  omega

private theorem score_lt {K i r p p' : ℕ} (hi : i < K) (hr : 2 ≤ r) (hp : r ≤ p)
    (hnext : p < threshold (i + 1) r) (hnew : threshold i p ≤ p') :
    score K r p < score K r p' := by
  have hmono : crossings i r p < crossings i r p' := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    have hpp' := (threshold_growth i p (hr.trans hp)).le.trans hnew
    refine ⟨Finset.monotone_filter_right _ fun _ _ h => h.trans hpp', ?_⟩
    have hex : ∃ j, p < (threshold i)^[j] r := ⟨r, hnext.trans_le (threshold_next i r hr)⟩
    generalize hj : Nat.find hex = j
    have hjr := Nat.find_min' hex (hnext.trans_le (threshold_next i r hr))
    have hjp := Nat.find_spec hex
    rw [hj] at hjr hjp
    cases j with
    | zero => exact (Nat.not_lt_of_ge hp hjp).elim
    | succ j =>
      have hprev : (threshold i)^[j] r ≤ p :=
        Nat.le_of_not_gt (Nat.find_min hex (by omega))
      have hmem : j ∈ (Finset.range r).filter fun t => (threshold i)^[t + 1] r ≤ p' := by
        rw [Finset.mem_filter, Finset.mem_range, Function.iterate_succ_apply']
        exact ⟨by omega, (threshold_mono (hr.trans (le_iterate
          (fun x hx => (threshold_growth i x hx).le) hr j)) hprev).trans hnew⟩
      intro h
      rw [← h, Finset.mem_filter] at hmem
      exact Nat.not_le_of_gt hjp hmem.2
  apply Finset.sum_lt_sum
  · intro j _
    exact Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ h =>
      h.trans ((threshold_growth i p (hr.trans hp)).le.trans hnew))
  · exact ⟨i, Finset.mem_range.mpr hi, hmono⟩

private theorem exists_level {K r p : ℕ} (h : r < p) (hK : p < threshold K r) :
    ∃ i, i < K ∧ threshold i r ≤ p ∧ p < threshold (i + 1) r := by
  have hex : ∃ j, p < threshold j r := ⟨K, hK⟩
  generalize hj : Nat.find hex = j
  have hle := Nat.find_min' hex hK
  have hlt := Nat.find_spec hex
  rw [hj] at hle hlt
  cases j with
  | zero => exact (Nat.not_lt_of_ge h hlt).elim
  | succ j =>
    exact ⟨j, by omega, Nat.le_of_not_gt (Nat.find_min hex (by omega)), hlt⟩

private def nodeScore (K b : ℕ) (uf : UnionFind) (x : ℕ) : ℕ :=
  score K (uf.rank x + b) (uf.rank (uf.parent x) + b)

private def totalScore (K b : ℕ) (uf : UnionFind) : ℕ :=
  ∑ x ∈ Finset.range uf.size, nodeScore K b uf x

private theorem nodeScore_root {K b x : ℕ} {uf : UnionFind} (hb : 2 ≤ b)
    (hx : uf.parent x = x) : nodeScore K b uf x = 0 := by
  unfold nodeScore
  rw [hx]
  exact score_self _ _ (by omega)

private theorem nodeScore_find_le (K b : ℕ) (uf : UnionFind) (x : Fin uf.size) (y : ℕ) :
    nodeScore K b uf y ≤ nodeScore K b (uf.find x).1 y := by
  unfold nodeScore
  simp only [rank_find]
  apply score_mono
  apply Nat.add_le_add_right
  rcases uf.find_parent_or x y with ⟨hr, _⟩ | hr
  · rw [hr, ← uf.rootD_parent y]
    exact UnionFind.le_rank_root
  · rw [hr]

private theorem find_score {K b : ℕ} (hb : 2 ≤ b) (uf : UnionFind) (x : Fin uf.size)
    (hK : ∀ i, uf.rank i + b < threshold K b) :
    findPathLength uf x + totalScore K b uf ≤ K + totalScore K b (uf.find x).1 := by
  classical
  let d := findPathLength uf x
  let path := fun j : ℕ => uf.parent^[j] x.val
  let r := fun j => uf.rank (path j) + b
  have hr (j : ℕ) : 2 ≤ r j := by dsimp [r]; omega
  have hroot : path d = uf.rootD x := Nat.find_spec (exists_iterate_parent_eq_rootD uf x)
  have hnext (j : ℕ) : path (j + 1) = uf.parent (path j) :=
    Function.iterate_succ_apply' uf.parent j x.val
  have hpath (j : ℕ) : path j < uf.size := by
    induction j with
    | zero => exact x.isLt
    | succ j ih => rw [hnext]; exact (uf.parent_lt _).2 ih
  have hroots (j : ℕ) : uf.rootD (path j) = uf.rootD x := by
    induction j with
    | zero => rfl
    | succ j ih => rw [hnext, UnionFind.rootD_parent, ih]
  have hinc : ∀ j < d, r j < r (j + 1) := by
    intro j hj
    have hp : uf.parent (path j) ≠ path j := by
      intro he
      have he' := (UnionFind.rootD_eq_self.2 he).symm.trans (hroots j)
      exact Nat.find_min (exists_iterate_parent_eq_rootD uf x) hj he'
    dsimp [r]
    rw [hnext]
    exact Nat.add_lt_add_right (UnionFind.rank_lt hp) b
  have hmono {j k : ℕ} (hj : j ≤ k) (hk : k ≤ d) : r j ≤ r k := by
    induction hj with
    | refl => rfl
    | @step i _ ih =>
      exact (ih (by omega)).trans (hinc i (by omega)).le
  have hl (j : ℕ) (hj : j < d) :
      ∃ i, i < K ∧ threshold i (r j) ≤ r (j + 1) ∧ r (j + 1) < threshold (i + 1) (r j) := by
    apply exists_level (hinc j hj)
    exact (hK (path (j + 1))).trans_le (threshold_mono hb (by dsimp [r]; omega))
  let level := fun j : ℕ => if hj : j < d then (hl j hj).choose else 0
  have hlevel (j : ℕ) (hj : j < d) :
      level j < K ∧ threshold (level j) (r j) ≤ r (j + 1) ∧
        r (j + 1) < threshold (level j + 1) (r j) := by
    simpa only [level, dite_eq_left hj] using (hl j hj).choose_spec
  -- Two uncharged edges cannot share a level: the later one would pay for the earlier.
  let good (j : ℕ) : Prop := ∃ k, j < k ∧ k < d ∧ threshold (level j) (r k) ≤ r (k + 1)
  let missed := (Finset.range d).filter fun j => ¬good j
  have hmissed : missed.card ≤ K := by
    rw [← Finset.card_range K]
    apply Finset.card_le_card_of_injOn level
    · intro j hj
      have hj' : j < d := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      exact Finset.mem_range.mpr (hlevel j hj').1
    · intro j hj k hk he
      have hj' : j < d := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hk' : k < d := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      rcases lt_trichotomy j k with hjk | hjk | hkj
      · exact ((Finset.mem_filter.mp hj).2
          ⟨k, hjk, hk', he ▸ (hlevel k hk').2.1⟩).elim
      · exact hjk
      · exact ((Finset.mem_filter.mp hk).2
          ⟨j, hkj, hj', he.symm ▸ (hlevel j hj').2.1⟩).elim
  let charged := (Finset.range d).filter good
  have hcount : d ≤ K + charged.card := by
    have he := Finset.card_filter_add_card_filter_not (s := Finset.range d) good
    change charged.card + missed.card = (Finset.range d).card at he
    rw [Finset.card_range] at he
    omega
  have hinj : Set.InjOn path (charged : Set ℕ) := by
    intro j hj k hk he
    have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hk' := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hre : r j = r k := congrArg (fun y => uf.rank y + b) he
    rcases lt_trichotomy j k with hjk | hjk | hkj
    · exact (Nat.ne_of_lt ((hinc j hj').trans_le (hmono (by omega) (by omega))) hre).elim
    · exact hjk
    · exact (Nat.ne_of_lt ((hinc k hk').trans_le (hmono (by omega) (by omega))) hre.symm).elim
  have hcharged (j : ℕ) (hj : j ∈ charged) :
      nodeScore K b uf (path j) < nodeScore K b (uf.find x).1 (path j) := by
    have ⟨hj', hgood⟩ := Finset.mem_filter.mp hj
    have hjd := Finset.mem_range.mp hj'
    obtain ⟨k, hjk, hkd, hk⟩ := hgood
    unfold nodeScore
    rw [rank_find, UnionFind.find_parent_eq_ite_iterate, ite_eq_left ⟨j, rfl⟩, rank_find,
      ← hroot, ← hnext]
    change score K (r j) (r (j + 1)) < score K (r j) (r d)
    apply score_lt (hlevel j hjd).1 (hr j) (hinc j hjd).le (hlevel j hjd).2.2
    exact (threshold_mono (hr (j + 1)) (hmono (by omega) (by omega))).trans
      (hk.trans (hmono (by omega) (by omega)))
  let nodes := charged.image path
  have hsubset : nodes ⊆ Finset.range uf.size := by
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_range.mpr (hpath j)
  have hsum : totalScore K b uf + charged.card ≤ totalScore K b (uf.find x).1 := by
    unfold totalScore
    rw [UnionFind.find_size, ← Finset.card_image_of_injOn hinj,
      Finset.card_eq_sum_ite hsubset, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    split
    · rename_i hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      exact hcharged j hj
    · simpa only [add_zero] using nodeScore_find_le K b uf x y
  change d + _ ≤ _
  omega

/-! ## Singleton allocation, linking, and the total charge -/

private theorem score_push {K b : ℕ} (hb : 2 ≤ b) (uf : UnionFind) :
    totalScore K b uf.push = totalScore K b uf := by
  have hp : uf.push.parent uf.size = uf.size := by
    rw [UnionFind.parent_push]
    exact UnionFind.parentD_of_not_lt (lt_irrefl _)
  rw [totalScore, size_push, Finset.sum_range_succ, nodeScore_root hb hp, add_zero]
  simp [totalScore, nodeScore]

private theorem rank_link_le (uf : UnionFind) (x y : Fin uf.size)
    (hy : uf.parent y = y) (i : ℕ) :
    uf.rank i ≤ (uf.link x y hy).rank i ∧
      (uf.link x y hy).rank i ≤ uf.rank i + if i = y.val then 1 else 0 := by
  rw [UnionFind.rank_link]
  split
  · rename_i h
    rw [h.2.2]
    simp
  · simp

private theorem score_link_le {K b : ℕ} (hb : 2 ≤ b) (uf : UnionFind) (x y : Fin uf.size)
    (hx : uf.parent x = x) (hy : uf.parent y = y) :
    totalScore K b uf ≤ totalScore K b (uf.link x y hy) := by
  unfold totalScore
  have hs : (uf.link x y hy).size = uf.size := by simp [UnionFind.size]
  rw [hs]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : uf.parent i = i
  · rw [nodeScore_root hb hi]
    exact Nat.zero_le _
  have hix : x.val ≠ i := fun h => hi (h ▸ hx)
  have hiy : y.val ≠ i := fun h => hi (h ▸ hy)
  have hparent : (uf.link x y hy).parent i = uf.parent i := by
    simp [UnionFind.parent_link, hix, hiy]
  have hrank : (uf.link x y hy).rank i = uf.rank i := by
    rw [UnionFind.rank_link]
    simp [hiy]
  unfold nodeScore
  rw [hrank, hparent]
  exact score_mono (Nat.add_le_add_right (rank_link_le uf x y hy _).1 b)

private def nonroot (uf : UnionFind) (i : ℕ) : ℕ :=
  if uf.parent i = i then 0 else 1

-- A link can increase one rank and turn one root into a nonroot.
private def rankAndNonrootSum (uf : UnionFind) : ℕ :=
  ∑ i ∈ Finset.range uf.size, (uf.rank i + nonroot uf i)

private theorem rankAndNonrootSum_push (uf : UnionFind) :
    rankAndNonrootSum uf.push = rankAndNonrootSum uf := by
  have hp : uf.parent uf.size = uf.size := UnionFind.parentD_of_not_lt (lt_irrefl _)
  have hr : uf.rank uf.size = 0 := by simp [UnionFind.rank, UnionFind.rankD]
  simp [rankAndNonrootSum, size_push, Finset.sum_range_succ, nonroot, hp, hr]

private theorem rankAndNonrootSum_find (uf : UnionFind) (x : Fin uf.size) :
    rankAndNonrootSum (uf.find x).1 = rankAndNonrootSum uf := by
  simp only [rankAndNonrootSum, UnionFind.find_size, rank_find]
  apply Finset.sum_congr rfl
  intro i _
  simp only [nonroot, ← UnionFind.rootD_eq_self, UnionFind.find_root_1]

private theorem rankAndNonrootSum_link (uf : UnionFind) (x y : Fin uf.size)
    (hy : uf.parent y = y) :
    rankAndNonrootSum (uf.link x y hy) ≤ rankAndNonrootSum uf + 2 := by
  let loses := if uf.rank y < uf.rank x then y.val else x.val
  have hp (i : ℕ) : nonroot (uf.link x y hy) i ≤ nonroot uf i + if i = loses then 1 else 0 := by
    by_cases h : i = loses
    · rw [ite_eq_left h]
      unfold nonroot
      split <;> omega
    · rw [ite_eq_right h, add_zero]
      suffices he : (uf.link x y hy).parent i = uf.parent i by simp [nonroot, he]
      rw [UnionFind.parent_link]
      split
      · rfl
      · by_cases hlt : uf.rank y < uf.rank x
        · have hi : y.val ≠ i := by simpa [loses, hlt, eq_comm] using h
          simp [hlt, hi]
        · have hi : x.val ≠ i := by simpa [loses, hlt, eq_comm] using h
          simp [hlt, hi]
  have hs : (uf.link x y hy).size = uf.size := by simp [UnionFind.size]
  unfold rankAndNonrootSum
  rw [hs]
  calc
    _ ≤ ∑ i ∈ Finset.range uf.size,
        ((uf.rank i + nonroot uf i) + ((if i = y.val then 1 else 0) +
          (if i = loses then 1 else 0))) := by
      apply Finset.sum_le_sum
      intro i _
      have := (rank_link_le uf x y hy i).2
      have := hp i
      omega
    _ ≤ _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
      split <;> split <;> simp

-- The extra shift above two contributes at most one term per allocated node.
private theorem totalScore_le {K b : ℕ} (hb : 2 ≤ b) (uf : UnionFind) :
    totalScore K b uf ≤ K * (2 * rankAndNonrootSum uf + (b - 2) * uf.size) := by
  unfold totalScore rankAndNonrootSum
  calc
    _ ≤ ∑ i ∈ Finset.range uf.size, K * (2 * (uf.rank i + nonroot uf i) + (b - 2)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : uf.parent i = i
      · rw [nodeScore_root hb hi]
        exact Nat.zero_le _
      · apply (score_le _ _ _).trans
        apply Nat.mul_le_mul_left
        simp only [nonroot, ite_eq_right hi]
        omega
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [Nat.mul_comm]

private theorem eq_of_arr_eq {s t : UnionFind} (h : s.arr = t.arr) : s = t := by
  cases s
  cases t
  cases h
  rfl

private theorem union_score_and_sum {K b : ℕ} (hb : 2 ≤ b) (uf : UnionFind)
    (x y : Fin uf.size) (hK : ∀ i, uf.rank i + b < threshold K b) :
    let mid := (uf.find x).1
    findPathLength uf x + findPathLength mid y + totalScore K b uf ≤
      2 * K + totalScore K b (uf.union x y) ∧
    rankAndNonrootSum (uf.union x y) ≤ rankAndNonrootSum uf + 2 := by
  let first := uf.find x
  let y₁ : Fin first.1.size := ⟨y.val, by rw [first.2.property]; exact y.isLt⟩
  let second := first.1.find y₁
  let rx : Fin second.1.size := ⟨first.2.val.val, by rw [second.2.property]; exact first.2.val.isLt⟩
  have hxVal : rx.val = uf.rootD x := UnionFind.find_root_2 uf x
  have hx : second.1.parent rx = rx := by
    apply UnionFind.rootD_eq_self.mp
    rw [hxVal]
    simp [first, second, UnionFind.rootD_rootD]
  have hy : second.1.parent second.2.val = second.2.val := by
    apply UnionFind.rootD_eq_self.mp
    change (first.1.find y₁).1.rootD (first.1.find y₁).2.val =
      (first.1.find y₁).2.val.val
    rw [UnionFind.find_root_2]
    simp [UnionFind.rootD_rootD]
  have hu : uf.union x y = second.1.link rx second.2.val hy :=
    eq_of_arr_eq (UnionFind.LinkInternal.union_carried uf x y)
  rw [hu]
  constructor
  · have h1 := find_score hb uf x hK
    have h2 := find_score hb first.1 y₁ (fun i => by simpa [first, rank_find] using hK i)
    have h3 := score_link_le (K := K) hb second.1 rx second.2.val hx hy
    change _ + findPathLength first.1 y₁.val + _ ≤ _
    change _ + _ ≤ _ + totalScore K b first.1 at h1
    change _ + totalScore K b first.1 ≤ _ + totalScore K b second.1 at h2
    omega
  · have h1 := rankAndNonrootSum_find uf x
    have h2 := rankAndNonrootSum_find first.1 y₁
    have h3 := rankAndNonrootSum_link second.1 rx second.2.val hy
    change rankAndNonrootSum first.1 = _ at h1
    change rankAndNonrootSum second.1 = _ at h2
    omega

/-! ## From individual operations to the sequence bound -/

private theorem step_bounds {K b n : ℕ} (hb : 2 ≤ b)
    (hlimit : Nat.log 2 n + b < threshold K b) {uf : UnionFind} (huf : Reachable uf)
    (op : Op) (hs : uf.size ≤ n) :
    Reachable (step uf op).1 ∧
    (step uf op).1.size = uf.size + numMakeSet [op] ∧
    rankAndNonrootSum (step uf op).1 ≤ rankAndNonrootSum uf + numFinds [op] ∧
    (step uf op).2 + totalScore K b uf ≤
      numMakeSet [op] + numFinds [op] * (K + 2) + totalScore K b (step uf op).1 := by
  have hK (i : ℕ) : uf.rank i + b < threshold K b :=
    (Nat.add_le_add_right ((rank_le_log huf i).trans (Nat.log_mono_right hs)) b).trans_lt hlimit
  cases op with
  | makeSet =>
    refine ⟨.push huf, size_push uf, ?_, ?_⟩
    · simp [step, rankAndNonrootSum_push, numFinds]
    · simp [step, numMakeSet, numFinds, score_push hb]
  | find x =>
    simp only [step, numMakeSet, numFinds]
    split <;> dsimp only
    · rename_i hx
      refine ⟨.find ⟨x, hx⟩ huf, by simp, ?_, ?_⟩
      · rw [rankAndNonrootSum_find]
        omega
      · have hc := find_score hb uf ⟨x, hx⟩ hK
        dsimp only at hc
        omega
    · exact ⟨huf, rfl, by omega, by omega⟩
  | union x y =>
    simp only [step, numMakeSet, numFinds]
    split <;> dsimp only
    · rename_i hxy
      obtain ⟨hc, hr⟩ := union_score_and_sum hb uf ⟨x, hxy.1⟩ ⟨y, hxy.2⟩ hK
      dsimp only at hc
      exact ⟨.union ⟨x, hxy.1⟩ ⟨y, hxy.2⟩ huf, by simp [size_union], hr, by omega⟩
    · exact ⟨huf, rfl, by omega, by omega⟩

private theorem run_bounds {K b n : ℕ} (hb : 2 ≤ b)
    (hlimit : Nat.log 2 n + b < threshold K b) (ops : List Op) {uf : UnionFind}
    (huf : Reachable uf) (hn : uf.size + numMakeSet ops ≤ n) :
    (run ops uf).1.size = uf.size + numMakeSet ops ∧
    rankAndNonrootSum (run ops uf).1 ≤ rankAndNonrootSum uf + numFinds ops ∧
    (run ops uf).2 + totalScore K b uf ≤
      numMakeSet ops + numFinds ops * (K + 2) + totalScore K b (run ops uf).1 := by
  induction ops generalizing uf with
  | nil => simp [run, numMakeSet, numFinds]
  | cons op ops ih =>
    have hmake : numMakeSet (op :: ops) = numMakeSet [op] + numMakeSet ops := by
      cases op <;> simp [numMakeSet, Nat.add_comm]
    have hfind : numFinds (op :: ops) = numFinds [op] + numFinds ops := by
      cases op <;> simp [numFinds, Nat.add_comm]
    obtain ⟨hreach, hsize, hrank, hcost⟩ := step_bounds hb hlimit huf op (by omega)
    obtain ⟨hs', hr', hc'⟩ := ih hreach (by omega)
    rw [hmake, hfind, Nat.add_mul]
    simp only [run]
    exact ⟨by omega, by omega, by omega⟩

private theorem bound {m n : ℕ} (ops : List Op) (hmake : numMakeSet ops = n)
    (hfind : numFinds ops = m) (hn : 1 ≤ n) :
    (run ops UnionFind.empty).2 ≤ 10 * (n + m * inverseAckermannTvL (m + n) n) := by
  let a := inverseAckermannTvL (m + n) n
  let b := (m + n) / n + 1
  let K := a + 1
  have ⟨ha, hb, hthreshold⟩ : 1 ≤ a ∧ 2 ≤ b ∧ Nat.log 2 n + b < threshold K b :=
    inverse_threshold hn
  have sz : UnionFind.empty.size = 0 := rfl
  have hz : rankAndNonrootSum UnionFind.empty = 0 := by simp [rankAndNonrootSum, sz]
  obtain ⟨hsize, hrank, hcost⟩ :=
    run_bounds (K := K) (b := b) hb hthreshold ops Reachable.empty (by omega)
  let last := (run ops UnionFind.empty).1
  have hlast : last.size = n := by dsimp [last]; omega
  have hr : rankAndNonrootSum last ≤ m := by dsimp [last]; omega
  have hdiv : (b - 2) * n ≤ m := by
    dsimp [b]
    rw [Nat.add_div_right m (by omega : 0 < n)]
    simpa using Nat.div_mul_le_self m n
  have htotal : totalScore K b last ≤ K * (3 * m) := by
    refine (totalScore_le (K := K) (b := b) hb last).trans (Nat.mul_le_mul_left _ ?_)
    rw [hlast]
    omega
  have hcost' : (run ops UnionFind.empty).2 ≤ n + m * (K + 2) + K * (3 * m) := by
    change _ + _ ≤ _ + totalScore K b last at hcost
    rw [hmake, hfind] at hcost
    omega
  refine hcost'.trans ?_
  have hp : m ≤ m * a := by simpa using Nat.mul_le_mul_left m ha
  change _ ≤ 10 * (n + m * a)
  have hlin : m * (K + 2) + K * (3 * m) = 4 * (m * a) + 6 * m := by
    dsimp only [K]
    ring
  rw [Nat.add_assoc, hlin]
  omega

end run_empty_cost_le_inverseAckermann

/-- **Tarjan–van Leeuwen bound for union by rank with path compression.** There is a constant
`C` such that every sequence of set-union operations with `n ≥ 1` make-sets and `m` finds (a
union counting as two finds), run from the empty structure, costs at most
`C (n + m α(m + n, n))`, where `α` is the inverse Ackermann function of Tarjan and van Leeuwen
(Tarjan and van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2) (1984),
§3, Theorem 3, linking by rank with compression). -/
public theorem run_empty_cost_le_inverseAckermann :
    ∃ C : ℕ, ∀ ops : List Op, 1 ≤ numMakeSet ops →
      (run ops Batteries.UnionFind.empty).2 ≤
        C * (numMakeSet ops +
          numFinds ops * inverseAckermannTvL (numFinds ops + numMakeSet ops) (numMakeSet ops))
 := by
  exact ⟨10, fun ops hn => run_empty_cost_le_inverseAckermann.bound ops rfl rfl hn⟩

end Cslib.Algorithms.Lean.UnionByRank
