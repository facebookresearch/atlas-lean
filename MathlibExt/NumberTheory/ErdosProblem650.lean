/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/650.lean` (Formal Conjectures), for the matching function
and the problem statements.
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Zify

/-!
# Matching integers to distinct multiples

For Erdős Problem 650, `conjecture_holds` gives the exact number of distinct multiples
guaranteed in an open interval. The lower bound uses Hall's marriage theorem and the
midpoint pairing of van Doorn, Li and Tang. The upper bound uses a pairwise coprime
rectangular grid and the Chinese remainder theorem.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem650Wanted

open Finset

/-- **Erdős's matching function for multiples in intervals.** For a natural number $m$, $f(m)$ is
the largest natural number $r$ such that for every natural number $N$, every set
$A \subseteq \{1, \dots, N\}$ with exactly $m$ elements and every real $x \ge 1$, there are
distinct $a_1, \dots, a_r \in A$ and distinct natural numbers $b_1, \dots, b_r$ in the open
interval $(x, x + 2N)$ with $a_i \mid b_i$ for every $i$. -/
noncomputable def f (m : ℕ) : ℕ :=
  sSup {r : ℕ | ∀ N : ℕ, ∀ A ⊆ Finset.Icc 1 N, A.card = m → ∀ x : ℝ, 1 ≤ x →
    ∃ a b : Fin r → ℕ, Function.Injective a ∧ Function.Injective b ∧
      (∀ i, a i ∈ A) ∧ (∀ i, (b i : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ))) ∧
      (∀ i, a i ∣ b i)}

/-- **Statement of Erdős Problem 650.** Let $f$ be Erdős's matching function for multiples in
intervals. The statement is the conjunction of four claims: for every natural number $m$,
$f(m) = \min(m, \lceil 2\sqrt{m}\,\rceil)$; it is not the case that $f(m) \le \sqrt{m}$ for every
natural number $m$; $\sqrt{m} \le f(m)$ for every natural number $m$; and $f(m^2) \le 2m$ for
every natural number $m$. -/
def conjecture : Prop :=
  (∀ m : ℕ, f m = min m ⌈2 * Real.sqrt m⌉₊) ∧
  (¬ ∀ m : ℕ, (f m : ℝ) ≤ Real.sqrt m) ∧
  (∀ m : ℕ, Real.sqrt m ≤ (f m : ℝ)) ∧
  (∀ m : ℕ, f (m ^ 2) ≤ 2 * m)

-- A subset admitting distinct pairs across a cut has size at most the product
-- of the two side sizes. AM–GM then bounds it by a quarter of the squared total.
private theorem count_pairs (S B : Finset ℕ) (c : ℕ) (p : ℕ → ℕ × ℕ)
    (hp : ∀ a ∈ S, (p a).1 ∈ B ∧ (p a).2 ∈ B ∧ (p a).1 ≤ c ∧ c < (p a).2)
    (hi : Set.InjOn p S) : 4 * S.card ≤ B.card ^ 2 := by
  let L := B.filter (· ≤ c)
  let R := B.filter (¬ · ≤ c)
  have h : S.card ≤ L.card * R.card := by
    rw [← card_product]
    apply card_le_card_of_injOn p _ hi
    intro a ha
    obtain ⟨hl, hr, h₁, h₂⟩ := hp a ha
    exact mem_product.mpr ⟨mem_filter.mpr ⟨hl, h₁⟩, mem_filter.mpr ⟨hr, h₂.not_ge⟩⟩
  have hs : L.card + R.card = B.card := card_filter_add_card_filter_not _
  zify at h hs ⊢
  nlinarith [sq_nonneg ((L.card : ℤ) - R.card), congrArg (· ^ 2) hs]

-- When the midpoint is reserved, a divisor of it uses a symmetric pair.
-- Double the distance exactly when this avoids a collision with a larger divisor.
private def stepSize (c N a : ℕ) : ℕ :=
  if 2 * a < N ∧ ¬2 * a ∣ c then 2 * a else a

private theorem stepSize_inj {c N a b : ℕ} (ha : a ∣ c) (hb : b ∣ c)
    (h : stepSize c N a = stepSize c N b) : a = b := by
  unfold stepSize at h
  split at h <;> split at h <;> grind

-- A symmetric pair at distance d from the midpoint cannot also be a pair
-- of consecutive multiples of 2d from a divisor strictly smaller than N.
private theorem no_mixed_pair {c N a b l : ℕ} (ha : 0 < b) (hN : a < N)
    (hd : a ∣ l) (h₁ : l + stepSize c N b = c) (h₂ : a = 2 * stepSize c N b) :
    False := by
  unfold stepSize at h₁ h₂
  split at h₁ <;> rename_i h
  · simp only [h] at h₂
    subst a
    exact h.2 (h₁ ▸ dvd_add (dvd_trans (dvd_mul_left _ _) hd) (dvd_refl _))
  · simp only [h, ↓reduceIte] at h₂
    subst a
    have hc : 2 * b ∣ c := of_not_not (fun hn ↦ h ⟨hN, hn⟩)
    have : 2 * b ∣ b := by
      rw [← h₁] at hc
      exact (Nat.dvd_add_right hd).mp hc
    have := Nat.le_of_dvd ha this
    omega

private def midPair (c N a : ℕ) : ℕ × ℕ :=
  if a ∣ c then (c - stepSize c N a, c + stepSize c N a)
  else (c - c % a, c - c % a + a)

private theorem midPair_inj {c N : ℕ} (hc : N ≤ c) {a b : ℕ}
    (ha : 0 < a ∧ a < N) (hb : 0 < b ∧ b < N)
    (he : midPair c N a = midPair c N b) : a = b := by
  have bound (v : ℕ) (hv : v < N) : stepSize c N v < N := by
    unfold stepSize
    split <;> omega
  have ha' := bound a ha.2
  have hb' := bound b hb.2
  unfold midPair at he
  split at he <;> rename_i h₁ <;> split at he <;> rename_i h₂ <;>
    obtain ⟨hl, hr⟩ := Prod.mk.inj he
  · exact stepSize_inj (N := N) h₁ h₂ (by omega)
  · exact (no_mixed_pair (c := c) ha.1 hb.2 (Nat.dvd_sub_mod c) (by omega) (by omega)).elim
  · exact (no_mixed_pair (c := c) hb.1 ha.2 (Nat.dvd_sub_mod c) (by omega) (by omega)).elim
  · omega

private theorem midPair_mem {x N a : ℕ} (ha : 0 < a ∧ a < N) :
    let p := midPair (x + N) N a
    x < p.1 ∧ p.1 < x + N ∧ x + N < p.2 ∧ p.2 < x + 2 * N ∧ a ∣ p.1 ∧ a ∣ p.2 := by
  dsimp only
  unfold midPair
  split <;> rename_i h
  · have hg : 0 < stepSize (x + N) N a ∧ stepSize (x + N) N a < N ∧
        a ∣ stepSize (x + N) N a := by
      unfold stepSize
      split <;> simp_all
    exact ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega,
      Nat.dvd_sub h hg.2.2, dvd_add h hg.2.2⟩
  · have hm := Nat.mod_lt (x + N) ha.1
    have hz := mt Nat.dvd_iff_mod_eq_zero.mpr h
    have hd := Nat.dvd_sub_mod (n := a) (x + N)
    exact ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega,
      hd, dvd_add hd (dvd_refl _)⟩

-- When N divides the midpoint, it can have just one neighbor. Remove the pair
-- (N, midpoint) before counting across the cut, then restore its two vertices.
private theorem neighbors_bound (x N : ℕ) (S B : Finset ℕ)
    (hs : S ⊆ Icc 1 N)
    (hb : ∀ a ∈ S, ∀ b, x < b → b < x + 2 * N → a ∣ b → b ∈ B) :
    S.card ≤ B.card ∨ 4 * S.card ≤ B.card ^ 2 := by
  let c := x + N
  by_cases h : N ∈ S ∧ N ∣ c
  · have hn := (mem_Icc.mp (hs h.1)).1
    have hc : c ∈ B := hb N h.1 c (by dsimp [c]; omega) (by dsimp [c]; omega) h.2
    have sm {a : ℕ} (ha : a ∈ S.erase N) : 0 < a ∧ a < N := by
      obtain ⟨hne, hm⟩ := mem_erase.mp ha
      have := mem_Icc.mp (hs hm)
      omega
    have count := count_pairs (S.erase N) (B.erase c) c (midPair c N) (by
      intro a ha
      obtain ⟨hl, hlc, hcr, hr, dl, dr⟩ := midPair_mem (x := x) (sm ha)
      have hm := mem_of_mem_erase ha
      exact ⟨mem_erase.mpr ⟨hlc.ne, hb a hm _ hl (by dsimp [c]; omega) dl⟩,
        mem_erase.mpr ⟨hcr.ne', hb a hm _ (by dsimp [c]; omega) hr dr⟩, hlc.le, hcr⟩) (by
      intro a ha b hb he
      exact midPair_inj (by dsimp [c]; omega) (sm ha) (sm hb) he)
    rw [card_erase_of_mem h.1, card_erase_of_mem hc] at count
    have hS := card_pos.mpr ⟨_, h.1⟩
    have hB := card_pos.mpr ⟨_, hc⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hB.ne'
    rw [hk] at count ⊢
    simp only [Nat.add_one_sub_one] at count
    rcases k with _ | k
    · left; simp at count; omega
    · by_cases hk : k = 0
      · subst k; left; norm_num at count; omega
      · right
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have : S.card - 1 + 1 = S.card := by omega
        change 4 * S.card ≤ (k + 1 + 1) ^ 2
        nlinarith
  · right
    let u := fun a ↦ c - c % a
    apply count_pairs S B c (fun a ↦ (u a, u a + a))
    · intro a ha
      have ⟨h₁, h₂⟩ := mem_Icc.mp (hs ha)
      have hm := Nat.mod_lt c h₁
      have hd := Nat.dvd_sub_mod (n := a) c
      have ht : a = N → c % a ≠ 0 := by
        rintro rfl hz
        exact h ⟨ha, Nat.dvd_iff_mod_eq_zero.mpr hz⟩
      dsimp [u, c] at *
      exact ⟨hb _ ha _ (by omega) (by omega) hd,
        hb _ ha _ (by omega) (by omega) (dvd_add hd (dvd_refl _)), by omega, by omega⟩
    · intro a _ b _ he
      obtain ⟨hl, hr⟩ := Prod.mk.inj he
      omega

private noncomputable abbrev target (m : ℕ) := min m ⌈2 * Real.sqrt m⌉₊

private theorem hall_arithmetic {m n r : ℕ} (hn : n ≤ m)
    (h : n ≤ r ∨ 4 * n ≤ r ^ 2) : n ≤ r + (m - target m) := by
  have ht : target m ≤ m := min_le_left _ _
  rcases h with h | h
  · omega
  by_cases hr : n ≤ r
  · omega
  have hr₂ : 2 ≤ r := by
    by_contra! hc
    interval_cases r <;> simp_all; omega
  let d := m - n
  have hd : d + n = m := Nat.sub_add_cancel hn
  have hsq : 4 * m ≤ (r + d) ^ 2 := by nlinarith [Nat.mul_le_mul_right d hr₂]
  have hcast : (4 : ℝ) * m ≤ ((r : ℝ) + d) ^ 2 := by exact_mod_cast hsq
  have hceil : ⌈2 * Real.sqrt m⌉₊ ≤ r + d := by
    apply Nat.ceil_le.mpr
    push_cast
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg m), Real.sqrt_nonneg m,
      sq_nonneg ((r : ℝ) + d - 2 * Real.sqrt m)]
  have hmin : target m ≤ r + d := (min_le_right _ _).trans hceil
  omega

-- Complete Hall's matching with m - target m dummy vertices and discard
-- their preimages to obtain the claimed number of genuine representatives.
private theorem interval_matching (x N : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N) :
    ∃ a b : Fin (target A.card) → ℕ, Function.Injective a ∧ Function.Injective b ∧
      (∀ i, a i ∈ A) ∧ (∀ i, x < b i ∧ b i < x + 2 * N) ∧ (∀ i, a i ∣ b i) := by
  classical
  let t (a : A) := (Ioo x (x + 2 * N)).filter (a.val ∣ ·)
  let d := A.card - target A.card
  let pad (a : A) := (t a).disjSum (range d)
  have hall (s : Finset A) : s.card ≤ (s.biUnion pad).card := by
    obtain rfl | ⟨v, hv⟩ := s.eq_empty_or_nonempty
    · simp
    have heq : s.biUnion pad = (s.biUnion t).disjSum (range d) := by
      ext z
      cases z with
      | inl b => simp [pad]
      | inr b =>
        simp only [mem_biUnion, pad, inr_mem_disjSum]
        exact ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨v, hv, h⟩⟩
    rw [heq, card_disjSum, card_range]
    let S := s.image Subtype.val
    have hs : S.card = s.card := card_image_of_injective _ Subtype.val_injective
    have hS : S ⊆ A := by
      intro a ha
      obtain ⟨u, _, rfl⟩ := mem_image.mp ha
      exact u.property
    rw [← hs]
    apply hall_arithmetic (card_le_card hS)
    apply neighbors_bound x N S _ (hS.trans hA)
    intro a ha b hl hr hd
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    exact mem_biUnion.mpr ⟨u, hu, mem_filter.mpr ⟨mem_Ioo.mpr ⟨hl, hr⟩, hd⟩⟩
  obtain ⟨g, hg, hm⟩ := (all_card_le_biUnion_card_iff_existsInjective' pad).mp hall
  let U := univ.image g
  have hU : U.card = A.card := by simp [U, card_image_of_injective _ hg]
  have hR : U.toRight ⊆ range d := by
    intro r hr
    obtain ⟨v, _, hv⟩ := mem_image.mp (mem_toRight.mp hr)
    have := hm v
    rw [hv] at this
    exact inr_mem_disjSum.mp this
  have hL : target A.card ≤ U.toLeft.card := by
    have := card_le_card hR
    have := U.card_toLeft_add_card_toRight
    have : target A.card ≤ A.card := min_le_left _ _
    simp only [card_range] at *
    dsimp only [d] at *
    omega
  obtain ⟨e⟩ : Nonempty (Fin (target A.card) ↪ U.toLeft) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hL)
  have pre (i : Fin (target A.card)) : ∃ v : A, g v = Sum.inl (e i).val := by
    obtain ⟨v, _, hv⟩ := mem_image.mp (mem_toLeft.mp (e i).property)
    exact ⟨v, hv⟩
  choose v hv using pre
  have hb (i) : (e i).val ∈ t (v i) := by
    have := hm (v i)
    rw [hv] at this
    exact inl_mem_disjSum.mp this
  refine ⟨fun i ↦ (v i).val, fun i ↦ (e i).val, ?_, Subtype.val_injective.comp e.injective,
    fun i ↦ (v i).property, fun i ↦ mem_Ioo.mp (mem_filter.mp (hb i)).1,
    fun i ↦ (mem_filter.mp (hb i)).2⟩
  intro i j hij
  have h : v i = v j := Subtype.ext hij
  apply e.injective
  exact Subtype.ext (Sum.inl.inj ((hv i).symm.trans ((congrArg g h).trans (hv j))))

-- Scaling all index differences by n! makes the grid entries pairwise coprime:
-- a common prime would divide n!, whereas every entry is 1 modulo n!.
private theorem grid_coprime {n M i j : ℕ} (hi : i < j) (hj : j < n) :
    Nat.Coprime (1 + n.factorial * (M + i)) (1 + n.factorial * (M + j)) := by
  by_contra h
  obtain ⟨p, hp, ha, hb⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hdiff : p ∣ n.factorial * (j - i) := by
    have he : 1 + n.factorial * (M + j) =
        1 + n.factorial * (M + i) + n.factorial * (j - i) := by
      rw [Nat.mul_sub, Nat.mul_add, Nat.mul_add]
      have := Nat.mul_le_mul_left n.factorial hi.le
      omega
    rw [he] at hb
    exact (Nat.dvd_add_right ha).mp hb
  have hk : p ∣ n.factorial := (hp.dvd_mul.mp hdiff).elim id
    (fun h ↦ h.trans (Nat.dvd_factorial (by omega) (by omega)))
  exact hp.not_dvd_one ((Nat.dvd_add_left (dvd_mul_of_dvd_left hk _)).mp ha)

private theorem two_multiples {a x N u b : ℕ} (hu : a ∣ u) (hb : a ∣ b)
    (hl : x < b) (hr : b < x + 2 * N) (hprev : u ≤ x + a)
    (hnext : x + 2 * N ≤ u + 2 * a) : b = u ∨ b = u + a := by
  obtain ⟨q, rfl⟩ := hu
  obtain ⟨v, rfl⟩ := hb
  by_cases h : v < q
  · have := Nat.mul_le_mul_left a (show v + 1 ≤ q by omega)
    rw [Nat.mul_add_one] at this
    omega
  by_cases h' : q + 2 ≤ v
  · have := Nat.mul_le_mul_left a h'
    rw [Nat.mul_add, Nat.mul_comm a 2] at this
    omega
  obtain h | h : v = q ∨ v = q + 1 := by omega
  · simp [h]
  · simp [h, Nat.mul_add_one]

-- Index an s-by-t rectangle by i = (i % s) + s * (i / s). Its first multiple
-- depends only on the row, and the next multiple depends only on the column.
private theorem grid_example (s t : ℕ) (hs : 0 < s) :
    ∃ (N x : ℕ) (A B : Finset ℕ), 1 ≤ x ∧ A ⊆ Icc 1 N ∧ A.card = s * t ∧
      B.card ≤ s + t ∧ ∀ a ∈ A, ∀ b, x < b → b < x + 2 * N → a ∣ b → b ∈ B := by
  classical
  let n := s * t
  let K := n.factorial
  let M := 4 * (n + 1)
  let H := 1 + K * M
  let v (i : ℕ) := 1 + K * (M + i)
  let N := H + K * n
  have hk : 0 < K := Nat.factorial_pos _
  have hv (i) : v i = H + K * i := by simp [v, H, Nat.mul_add, Nat.add_assoc]
  have hi : Function.Injective v := by
    intro i j he
    simpa [hv, hk.ne'] using he
  have co : Set.Pairwise (range n : Finset ℕ) (Function.onFun Nat.Coprime v) := by
    intro i h₁ j h₂ hn
    have h₁ := mem_range.mp h₁
    have h₂ := mem_range.mp h₂
    rcases lt_or_gt_of_ne hn with h | h
    · exact grid_coprime h h₂
    · exact (grid_coprime h h₁).symm
  let r (i : ℕ) := K * (i % s)
  let sol := Nat.chineseRemainderOfFinset r v (range n) (fun i _ ↦ by simp [v]) co
  let P := ∏ i ∈ range n, v i
  have hP : 0 < P := prod_pos (fun i _ ↦ by dsimp [v]; omega)
  let T := sol.val + (H + 1) * P
  have hT : H < T := by dsimp [T]; nlinarith
  have hH : 3 * (K * n) ≤ H := by dsimp [H, M]; nlinarith
  let x := T - H
  let rows := (range s).image (fun i ↦ T - K * i)
  let cols := (range t).image (fun j ↦ T + H + K * (s * j))
  refine ⟨N, x, (range n).image v, rows ∪ cols, by dsimp [x]; omega, ?_,
    (card_image_of_injective _ hi).trans (card_range _), ?_, ?_⟩
  · intro a ha
    obtain ⟨i, hm, rfl⟩ := mem_image.mp ha
    exact mem_Icc.mpr ⟨by dsimp [v]; omega, by
      rw [hv]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (mem_range.mp hm).le) _⟩
  · exact (card_union_le _ _).trans (Nat.add_le_add
      (card_image_le.trans (card_range _).le) (card_image_le.trans (card_range _).le))
  intro a ha b hl hr db
  obtain ⟨i, him, rfl⟩ := mem_image.mp ha
  have him' := mem_range.mp him
  have hmul := Nat.mod_add_div i s
  have hri : r i ≤ K * n := Nat.mul_le_mul_left _ ((Nat.mod_le _ _).trans him'.le)
  have hTi : r i ≤ T := by omega
  have hmod : T ≡ r i [MOD v i] := by
    have hd : v i ∣ (H + 1) * P :=
      dvd_mul_of_dvd_right (dvd_prod_of_mem v him) _
    simpa only [Nat.add_zero] using (sol.property i him).add (Nat.modEq_zero_iff_dvd.mpr hd)
  have du : v i ∣ T - r i := (Nat.modEq_iff_dvd' hTi).mp hmod.symm
  have hadd : T - r i + v i = T + H + K * (s * (i / s)) := by
    have he := congrArg (K * ·) hmul
    simp only [Nat.mul_add] at he
    dsimp only [r] at *
    rw [hv]
    omega
  have halt : b = T - r i ∨ b = T - r i + v i := by
    apply two_multiples du db hl hr
    · rw [hv]; dsimp [x]; omega
    · have hmi : r i ≤ K * i := Nat.mul_le_mul_left _ (Nat.mod_le _ _)
      rw [hv]; dsimp [N, x]; omega
  rcases halt with h | h
  · exact mem_union_left _ (mem_image.mpr ⟨i % s, mem_range.mpr (Nat.mod_lt _ hs), h.symm⟩)
  · apply mem_union_right
    exact mem_image.mpr ⟨i / s, mem_range.mpr ((Nat.div_lt_iff_lt_mul hs).mpr
      (by simpa [n, Nat.mul_comm] using him')), (h.trans hadd).symm⟩

private theorem card_bound {r : ℕ} {A : Finset ℕ} {a : Fin r → ℕ}
    (ha : Function.Injective a) (hm : ∀ i, a i ∈ A) : r ≤ A.card := by
  let g (i : Fin r) : A := ⟨a i, hm i⟩
  simpa using Fintype.card_le_of_injective g (fun _ _ h ↦ ha (congrArg Subtype.val h))

private theorem balanced_rectangle {m : ℕ} (hm : 0 < m) :
    ∃ s t : ℕ, 0 < s ∧ m ≤ s * t ∧ s + t = ⌈2 * Real.sqrt m⌉₊ := by
  let k := ⌈2 * Real.sqrt m⌉₊
  have hk : 2 * Real.sqrt m ≤ (k : ℝ) := Nat.le_ceil _
  have hsqrt : 1 ≤ Real.sqrt m := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by exact_mod_cast hm)
  have hk₂ : 2 ≤ k := by exact_mod_cast (show (2 : ℝ) ≤ k by linarith)
  have hsq : 4 * m ≤ k ^ 2 := by
    have := mul_self_le_mul_self (by positivity) hk
    exact_mod_cast (show (4 : ℝ) * m ≤ (k : ℝ) ^ 2 by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg m)])
  refine ⟨k / 2, k - k / 2, by omega, ?_, by omega⟩
  have hcases : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
  rcases hcases with h | h
  · have ht : k - k / 2 = k / 2 := by omega
    rw [ht]
    nlinarith [congrArg (· ^ 2) h]
  · have ht : k - k / 2 = k / 2 + 1 := by omega
    rw [ht]
    nlinarith [congrArg (· ^ 2) h]

private theorem exact_matching (m : ℕ) : f m = target m := by
  let G : Set ℕ := {r | ∀ N : ℕ, ∀ A ⊆ Finset.Icc 1 N, A.card = m → ∀ x : ℝ, 1 ≤ x →
    ∃ a b : Fin r → ℕ, Function.Injective a ∧ Function.Injective b ∧
      (∀ i, a i ∈ A) ∧ (∀ i, (b i : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ))) ∧
      (∀ i, a i ∣ b i)}
  change sSup G = target m
  have hlow : target m ∈ G := by
    intro N A hA hcard x hx
    subst m
    obtain ⟨a, b, ha, hb, hm, hI, hd⟩ := interval_matching ⌊x⌋₊ N A hA
    refine ⟨a, b, ha, hb, hm, ?_, hd⟩
    intro i
    have ⟨hl, hr⟩ := hI i
    have hl' : (⌊x⌋₊ : ℝ) + 1 ≤ b i := by exact_mod_cast hl
    have hr' : (b i : ℝ) < (⌊x⌋₊ : ℝ) + 2 * N := by exact_mod_cast hr
    exact ⟨(Nat.lt_floor_add_one x).trans_le hl', by linarith [Nat.floor_le (by linarith : 0 ≤ x)]⟩
  have bound (r) (hr : r ∈ G) : r ≤ m := by
    have hc : (Icc 1 m).card = m := by simp
    obtain ⟨a, _, ha, _, hm, _⟩ := hr m _ Subset.rfl hc 1 le_rfl
    exact (card_bound ha hm).trans hc.le
  apply le_antisymm _ (le_csSup ⟨m, bound⟩ hlow)
  apply csSup_le ⟨_, hlow⟩
  intro r hr
  apply le_min (bound r hr)
  by_cases hm : m = 0
  · simpa [hm] using bound r hr
  obtain ⟨s, t, hs, hp, hk⟩ := balanced_rectangle (Nat.pos_of_ne_zero hm)
  obtain ⟨N, x, A, B, hx, hA, hc, hB, hcover⟩ := grid_example s t hs
  obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq (hp.trans hc.ge)
  obtain ⟨a, b, _, hb, ha, hI, hd⟩ := hr N S (hS.trans hA) hcard x (by exact_mod_cast hx)
  rw [← hk]
  apply le_trans (card_bound hb _) hB
  intro i
  have ⟨hl, hu⟩ := hI i
  exact hcover _ (hS (ha i)) _ (by exact_mod_cast hl) (by exact_mod_cast hu) (hd i)

/--
**Erdős Problem 650: matching integers to distinct multiples.** For a natural number $m$, let
$f(m)$ be the largest natural number $r$ such that for every natural number $N$, every set
$A \subseteq \{1, \dots, N\}$ with exactly $m$ elements and every real $x \ge 1$, there are
distinct $a_1, \dots, a_r \in A$ and distinct natural numbers $b_1, \dots, b_r$ in the open
interval $(x, x + 2N)$ with $a_i \mid b_i$ for every $i$. Then $f(m) = \min(m,
\lceil 2\sqrt{m}\,\rceil)$ for every natural number $m$; it is not the case that
$f(m) \le \sqrt{m}$ for every natural number $m$; $\sqrt{m} \le f(m)$ for every natural number
$m$; and $f(m^2) \le 2m$ for every natural number $m$.

Solved by Erdős–Surányi [ErSu59], Erdős–Selfridge [Er78], [Er86c] and van Doorn–Li–Tang [VLT26].

Source: [VLT26] W. van Doorn, Y. Li and Q. Tang, Optimal bounds
for an Erdős problem on matching integers to distinct multiples, arXiv:2603.28636 (2026),
https://arxiv.org/abs/2603.28636; W. van Doorn, Lean formalization of Erdős Problem 650
(Aristotle-assisted),
https://github.com/Woett/Lean-files/blob/c100ed4a4429e987a9555ee428a1aa524a46e16d/ErdosProblem650.lean.
Moved from `OpenConjectures/NumberTheory/ErdosProblem650`.
-/
public theorem conjecture_holds : conjecture := by
  refine ⟨exact_matching, ?_, ?_, ?_⟩
  · intro h
    have h₄ := h 4
    rw [exact_matching] at h₄
    norm_num [target] at h₄
  · intro m
    rw [exact_matching, target, Nat.cast_min]
    apply le_min
    · apply Real.sqrt_le_self_iff.mpr
      rcases m with _ | m <;> simp
    · have := Nat.le_ceil (2 * Real.sqrt m)
      linarith [Real.sqrt_nonneg m]
  · intro m
    rw [exact_matching]
    apply (min_le_right _ _).trans
    apply Nat.ceil_le.mpr
    push_cast
    rw [Real.sqrt_sq (Nat.cast_nonneg _)]

end MathlibExt.NumberTheory.ErdosProblem650Wanted
