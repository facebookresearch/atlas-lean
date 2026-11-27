/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PathSignature.FactorialEstimate

import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# Lyons's extension theorem

A multiplicative functional of degree `⌊p⌋` and finite `p`-variation (a `p`-rough path) extends
uniquely to a multiplicative functional of every degree with finite `p`-variation, and with the
factorial control `ω^{i/p} / (β (i/p)!)` in every degree once `β` is large enough (T. Lyons,
*Differential equations driven by rough signals*, Rev. Mat. Iberoam. 14 (1998), Theorem 2.2.1).
So the first `⌊p⌋` levels determine all higher "iterated integrals" of a rough path, and in
particular its signature (Boedihardjo, Geng, Lyons and Yang, Adv. Math. 293 (2016),
arXiv:1406.7871, Proposition 2.1, which quotes it for weakly geometric rough paths). The
statements use the coordinates and `ℓ¹` tensor norms of
`MathlibExt.Analysis.PathSignature.RoughPath`.

This file proves existence and uniqueness, `exists_unique_extension`; the factorial control is
`isControlledBy_extension` in `MathlibExt.Analysis.PathSignature.FactorialEstimate`.

The levels above `⌊p⌋` are built one at a time. On a word of length `n + 1 > p`, the cross terms
`c(r, s, t)` of `X_{r,s} ⊗ X_{s,t}` form a cocycle bounded by `K ω(r, t)^θ` with
`θ = (n + 1)/p > 1`, and the new level `D` must satisfy
`D(r, t) = D(r, s) + D(s, t) + c(r, s, t)`. A sewing argument produces it: Riemann sums along
finite partitions are bounded uniformly by a maximal inequality, proved by cutting each partition
near the middle of the control, and their limit along an ultrafilter of finite sets of times is
exactly additive. Uniqueness holds because the difference of two extensions at the first level
where they differ is additive and of size `O(ω^θ)` with `θ > 1`, hence zero.
-/

namespace MathlibExt.Analysis.PathSignature.ExtensionTheoremWanted

open Finset Filter Topology MathlibExt.Analysis.PathSignature

/-! ### Riemann sums along finite sets of times -/

-- The first point of `P` after `x` and before `t`, or `t` itself.
private noncomputable def nextPt (P : Finset ℝ) (t x : ℝ) : ℝ :=
  (insert t (P.filter fun y => x < y ∧ y < t)).min' (insert_nonempty _ _)

-- The sum of `Ξ` over the intervals of the partition of `[s, t]` cut by the points of `P`.
private noncomputable def riemann (Ξ : ℝ → ℝ → ℝ) (P : Finset ℝ) (s t : ℝ) : ℝ :=
  ∑ x ∈ insert s (P.filter fun y => s < y ∧ y < t), Ξ x (nextPt P t x)

private theorem nextPt_le_right (P : Finset ℝ) (t x : ℝ) : nextPt P t x ≤ t :=
  min'_le _ _ (mem_insert_self _ _)

private theorem nextPt_le {P : Finset ℝ} {t x y : ℝ} (hy : y ∈ P) (hxy : x < y) (hyt : y < t) :
    nextPt P t x ≤ y :=
  min'_le _ _ (mem_insert_of_mem (mem_filter.mpr ⟨hy, hxy, hyt⟩))

private theorem nextPt_cases (P : Finset ℝ) (t x : ℝ) :
    nextPt P t x = t ∨ (nextPt P t x ∈ P ∧ x < nextPt P t x ∧ nextPt P t x < t) := by
  rcases mem_insert.mp (min'_mem (insert t (P.filter fun y => x < y ∧ y < t))
    (insert_nonempty _ _)) with h | h
  · exact Or.inl h
  · exact Or.inr (mem_filter.mp h)

private theorem lt_nextPt {P : Finset ℝ} {t x : ℝ} (hxt : x < t) : x < nextPt P t x := by
  rcases nextPt_cases P t x with h | h
  · rw [h]
    exact hxt
  · exact h.2.1

private theorem nextPt_eq_right {P : Finset ℝ} {t x : ℝ} (h : ∀ y ∈ P, x < y → t ≤ y) :
    nextPt P t x = t := by
  rcases nextPt_cases P t x with h' | ⟨hm, hx, ht⟩
  · exact h'
  · exact absurd (h _ hm hx) (not_le.mpr ht)

-- A point `v` of `P` between `x` and `t` does not change the point following `x`.
private theorem nextPt_congr {P : Finset ℝ} {x v t : ℝ} (hv : v ∈ P) (hxv : x < v) (hvt : v < t) :
    nextPt P t x = nextPt P v x := by
  apply le_antisymm
  · rcases nextPt_cases P v x with h | ⟨hm, hx, hlt⟩
    · rw [h]
      exact nextPt_le hv hxv hvt
    · exact nextPt_le hm hx (hlt.trans hvt)
  · rcases nextPt_cases P t x with h | ⟨hm, hx, hlt⟩
    · rw [h]
      exact (nextPt_le_right P v x).trans hvt.le
    · rcases lt_or_ge (nextPt P t x) v with h' | h'
      · exact nextPt_le hm hx h'
      · exact (nextPt_le_right P v x).trans h'

private theorem riemann_of_forall {Ξ : ℝ → ℝ → ℝ} {P : Finset ℝ} {s t : ℝ}
    (h : ∀ y ∈ P, s < y → t ≤ y) : riemann Ξ P s t = Ξ s t := by
  have he : P.filter (fun y => s < y ∧ y < t) = ∅ :=
    filter_eq_empty_iff.mpr fun y hy hst => absurd (h y hy hst.1) (not_le.mpr hst.2)
  rw [riemann, he, insert_empty, sum_singleton, nextPt_eq_right h]

private theorem riemann_self (Ξ : ℝ → ℝ → ℝ) (P : Finset ℝ) (s : ℝ) :
    riemann Ξ P s s = Ξ s s :=
  riemann_of_forall fun _ _ hy => hy.le

-- Cutting at a point of `P` splits the Riemann sum.
private theorem riemann_split (Ξ : ℝ → ℝ → ℝ) (P : Finset ℝ) {s v t : ℝ} (hv : v ∈ P)
    (hsv : s < v) (hvt : v < t) :
    riemann Ξ P s t = riemann Ξ P s v + riemann Ξ P v t := by
  have hset : insert s (P.filter fun y => s < y ∧ y < t) =
      insert s (P.filter fun y => s < y ∧ y < v) ∪
        insert v (P.filter fun y => v < y ∧ y < t) := by
    ext x
    simp only [mem_insert, mem_filter, mem_union]
    constructor
    · rintro (hx | ⟨hx, hsx, hxt⟩)
      · exact Or.inl (Or.inl hx)
      · rcases lt_trichotomy x v with h | h | h
        · exact Or.inl (Or.inr ⟨hx, hsx, h⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨hx, h, hxt⟩)
    · rintro ((hx | ⟨hx, hsx, hxv⟩) | (hx | ⟨hx, hvx, hxt⟩))
      · exact Or.inl hx
      · exact Or.inr ⟨hx, hsx, hxv.trans hvt⟩
      · subst hx
        exact Or.inr ⟨hv, hsv, hvt⟩
      · exact Or.inr ⟨hx, hsv.trans hvx, hxt⟩
  have hlt : ∀ x ∈ insert s (P.filter fun y => s < y ∧ y < v), x < v := by
    intro x hx
    rcases mem_insert.mp hx with h | h
    · rw [h]
      exact hsv
    · exact (mem_filter.mp h).2.2
  have hge : ∀ x ∈ insert v (P.filter fun y => v < y ∧ y < t), v ≤ x := by
    intro x hx
    rcases mem_insert.mp hx with h | h
    · rw [h]
    · exact (mem_filter.mp h).2.1.le
  have hdisj : Disjoint (insert s (P.filter fun y => s < y ∧ y < v))
      (insert v (P.filter fun y => v < y ∧ y < t)) :=
    disjoint_left.mpr fun x hx hx' => absurd (hge x hx') (not_le.mpr (hlt x hx))
  rw [riemann, hset, sum_union hdisj, riemann, riemann, add_left_inj]
  exact sum_congr rfl fun x hx => by rw [nextPt_congr hv (hlt x hx) hvt]

private theorem riemann_split' {Ξ : ℝ → ℝ → ℝ} (P : Finset ℝ) {s v t : ℝ}
    (hv : v ∈ P ∨ v = s ∨ v = t) (hsv : s ≤ v) (hvt : v ≤ t) (hs : Ξ s s = 0)
    (ht : Ξ t t = 0) : riemann Ξ P s t = riemann Ξ P s v + riemann Ξ P v t := by
  rcases eq_or_lt_of_le hsv with h | hsv'
  · subst h
    rw [riemann_self, hs, zero_add]
  rcases eq_or_lt_of_le hvt with h | hvt'
  · subst h
    rw [riemann_self, ht, add_zero]
  rcases hv with hv | h | h
  · exact riemann_split Ξ P hv hsv' hvt'
  · exact absurd h hsv'.ne'
  · exact absurd h hvt'.ne

/-! ### The sewing lemma -/

private theorem germ_self {J : Set ℝ} {ω : ℝ → ℝ → ℝ} (hω : IsControl ω J) {θ K : ℝ}
    (hθ : 1 < θ) {Ξ : ℝ → ℝ → ℝ}
    (hΞ : ∀ s ∈ J, ∀ u ∈ J, ∀ t ∈ J, s ≤ u → u ≤ t → |Ξ s u + Ξ u t - Ξ s t| ≤ K * ω s t ^ θ)
    {x : ℝ} (hx : x ∈ J) : Ξ x x = 0 := by
  have h := hΞ x hx x hx x hx le_rfl le_rfl
  rw [hω.2.1 x hx, Real.zero_rpow (by linarith), mul_zero, add_sub_cancel_right] at h
  exact abs_nonpos_iff.mp h

-- The maximal inequality: Riemann sums of an almost additive germ stay close to the germ,
-- uniformly over all partitions.
private theorem riemann_sub_le {J : Set ℝ} (hJ : J.OrdConnected) {ω : ℝ → ℝ → ℝ}
    (hω : IsControl ω J) {θ K : ℝ} (hθ : 1 < θ) (hK : 0 ≤ K) {Ξ : ℝ → ℝ → ℝ}
    (hΞ : ∀ s ∈ J, ∀ u ∈ J, ∀ t ∈ J, s ≤ u → u ≤ t → |Ξ s u + Ξ u t - Ξ s t| ≤ K * ω s t ^ θ)
    (P : Finset ℝ) (N : ℕ) :
    ∀ s ∈ J, ∀ t ∈ J, s ≤ t → (P.filter fun y => s < y ∧ y < t).card = N →
      |riemann Ξ P s t - Ξ s t| ≤ 2 * K / (1 - 2 ^ (1 - θ)) * ω s t ^ θ := by
  set L := 2 * K / (1 - 2 ^ (1 - θ)) with hL
  have hq : (2 : ℝ) ^ (1 - θ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hL0 : 0 ≤ L := div_nonneg (by positivity) (by linarith)
  have hLeq : 2 ^ (1 - θ) * L + 2 * K = L := by
    rw [hL]
    field_simp
    ring
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro s hs t ht hst hN
  have hωst := hω.2.2.1 s hs t ht hst
  by_cases hemp : ∀ y ∈ P, s < y → t ≤ y
  · rw [riemann_of_forall hemp, sub_self, abs_zero]
    exact mul_nonneg hL0 (Real.rpow_nonneg hωst _)
  push Not at hemp
  obtain ⟨y₀, hy₀P, hsy₀, hy₀t⟩ := hemp
  have hst' : s < t := hsy₀.trans hy₀t
  -- `a`: the last point of the partition with `ω(s, a) ≤ ω(s, t) / 2`; `b`: the next point.
  set A := (insert s (P.filter fun y => s < y ∧ y < t)).filter fun x => ω s x ≤ ω s t / 2
  have hsA : s ∈ A := mem_filter.mpr ⟨mem_insert_self _ _, by
    rw [hω.2.1 s hs]
    linarith⟩
  set a := A.max' ⟨s, hsA⟩
  have haA : a ∈ A := max'_mem _ _
  have haI : a = s ∨ (a ∈ P ∧ s < a ∧ a < t) := by
    rcases mem_insert.mp (mem_filter.mp haA).1 with h | h
    · exact Or.inl h
    · exact Or.inr (mem_filter.mp h)
  have hsa : s ≤ a := le_max' _ _ hsA
  have hat : a < t := by
    rcases haI with h | h
    · rw [h]
      exact hst'
    · exact h.2.2
  have haJ : a ∈ J := hJ.out hs ht ⟨hsa, hat.le⟩
  have hωa : ω s a ≤ ω s t / 2 := (mem_filter.mp haA).2
  set b := nextPt P t a
  have hab : a < b := lt_nextPt hat
  have hbt : b ≤ t := nextPt_le_right P t a
  have hbJ : b ∈ J := hJ.out hs ht ⟨hsa.trans hab.le, hbt⟩
  have hbI : b = t ∨ (b ∈ P ∧ a < b ∧ b < t) := nextPt_cases P t a
  have hωb : ω b t ≤ ω s t / 2 := by
    rcases hbI with h | ⟨hbP, _, hbt'⟩
    · rw [h, hω.2.1 t ht]
      linarith
    · have hnot : ¬ ω s b ≤ ω s t / 2 := fun hle =>
        absurd (le_max' A b (mem_filter.mpr ⟨mem_insert_of_mem
          (mem_filter.mpr ⟨hbP, hsa.trans_lt hab, hbt'⟩), hle⟩)) (not_le.mpr hab)
      linarith [hω.2.2.2 s hs b hbJ t ht (hsa.trans hab.le) hbt]
  have hΞ0 : ∀ x ∈ J, Ξ x x = 0 := fun x hx => germ_self hω hθ hΞ hx
  have hgap : ∀ y ∈ P, a < y → b ≤ y := by
    intro y hy hay
    by_contra hlt
    push Not at hlt
    exact absurd (nextPt_le hy hay (hlt.trans_le hbt)) (not_le.mpr hlt)
  have hsplit : riemann Ξ P s t = riemann Ξ P s a + Ξ a b + riemann Ξ P b t := by
    have ha' : a ∈ P ∨ a = s ∨ a = t := by
      rcases haI with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h.1
    have hb' : b ∈ P ∨ b = a ∨ b = t := by
      rcases hbI with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h.1
    rw [riemann_split' P ha' hsa hat.le (hΞ0 s hs) (hΞ0 t ht),
      riemann_split' P hb' hab.le hbt (hΞ0 a haJ) (hΞ0 t ht), riemann_of_forall hgap]
    ring
  -- Both halves have fewer interior points.
  have hcard1 : (P.filter fun y => s < y ∧ y < a).card < N := by
    rw [← hN]
    apply card_lt_card
    rw [ssubset_iff_of_subset fun y hy => by
      simp only [mem_filter] at hy ⊢
      exact ⟨hy.1, hy.2.1, hy.2.2.trans hat⟩]
    obtain ⟨x, hxI, hax⟩ : ∃ x ∈ P.filter (fun y => s < y ∧ y < t), a ≤ x := by
      rcases haI with h | ⟨haP, hsa', hat'⟩
      · exact ⟨y₀, mem_filter.mpr ⟨hy₀P, hsy₀, hy₀t⟩, by rw [h]; exact hsy₀.le⟩
      · exact ⟨a, mem_filter.mpr ⟨haP, hsa', hat'⟩, le_rfl⟩
    exact ⟨x, hxI, fun hm => absurd (mem_filter.mp hm).2.2 (not_lt.mpr hax)⟩
  have hcard2 : (P.filter fun y => b < y ∧ y < t).card < N := by
    rw [← hN]
    apply card_lt_card
    rw [ssubset_iff_of_subset fun y hy => by
      simp only [mem_filter] at hy ⊢
      exact ⟨hy.1, (hsa.trans_lt hab).trans hy.2.1, hy.2.2⟩]
    obtain ⟨x, hxI, hxb⟩ : ∃ x ∈ P.filter (fun y => s < y ∧ y < t), x ≤ b := by
      rcases hbI with h | ⟨hbP, hab', hbt'⟩
      · exact ⟨y₀, mem_filter.mpr ⟨hy₀P, hsy₀, hy₀t⟩, by rw [h]; exact hy₀t.le⟩
      · exact ⟨b, mem_filter.mpr ⟨hbP, hsa.trans_lt hab', hbt'⟩, le_rfl⟩
    exact ⟨x, hxI, fun hm => absurd (mem_filter.mp hm).2.1 (not_lt.mpr hxb)⟩
  have h1 := ih _ hcard1 s hs a haJ hsa rfl
  have h2 := ih _ hcard2 b hbJ t ht hbt rfl
  have h3 := hΞ s hs a haJ b hbJ hsa hab.le
  have h4 := hΞ s hs b hbJ t ht (hsa.trans hab.le) hbt
  have hωsb : ω s b ≤ ω s t := by
    linarith [hω.2.2.2 s hs b hbJ t ht (hsa.trans hab.le) hbt, hω.2.2.1 b hbJ t ht hbt]
  have e1 : L * ω s a ^ θ ≤ L * (ω s t / 2) ^ θ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (hω.2.2.1 s hs a haJ hsa) hωa (by linarith)) hL0
  have e2 : L * ω b t ^ θ ≤ L * (ω s t / 2) ^ θ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (hω.2.2.1 b hbJ t ht hbt) hωb (by linarith)) hL0
  have e3 : K * ω s b ^ θ ≤ K * ω s t ^ θ := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (hω.2.2.1 s hs b hbJ (hsa.trans hab.le)) hωsb (by linarith)) hK
  have e4 : L * (ω s t / 2) ^ θ + L * (ω s t / 2) ^ θ + K * ω s t ^ θ + K * ω s t ^ θ =
      L * ω s t ^ θ := by
    have hq' : (2 : ℝ) ^ (1 - θ) = 2 / 2 ^ θ := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    rw [Real.div_rpow hωst (by norm_num)]
    calc L * (ω s t ^ θ / 2 ^ θ) + L * (ω s t ^ θ / 2 ^ θ) + K * ω s t ^ θ + K * ω s t ^ θ =
        ω s t ^ θ * (2 / 2 ^ θ * L + 2 * K) := by ring
      _ = L * ω s t ^ θ := by rw [← hq', hLeq, mul_comm]
  have hrw : riemann Ξ P s a + Ξ a b + riemann Ξ P b t - Ξ s t =
      (riemann Ξ P s a - Ξ s a) + (riemann Ξ P b t - Ξ b t) + (Ξ s a + Ξ a b - Ξ s b) +
        (Ξ s b + Ξ b t - Ξ s t) := by ring
  rw [hsplit, hrw]
  have t1 := abs_add_le ((riemann Ξ P s a - Ξ s a) + (riemann Ξ P b t - Ξ b t) +
    (Ξ s a + Ξ a b - Ξ s b)) (Ξ s b + Ξ b t - Ξ s t)
  have t2 := abs_add_le ((riemann Ξ P s a - Ξ s a) + (riemann Ξ P b t - Ξ b t))
    (Ξ s a + Ξ a b - Ξ s b)
  have t3 := abs_add_le (riemann Ξ P s a - Ξ s a) (riemann Ξ P b t - Ξ b t)
  linarith

-- The additive sewing lemma, with the limit taken along an ultrafilter on finite sets of times.
private theorem exists_additive {J : Set ℝ} (hJ : J.OrdConnected) {ω : ℝ → ℝ → ℝ}
    (hω : IsControl ω J) {θ K : ℝ} (hθ : 1 < θ) (hK : 0 ≤ K) (Ξ : ℝ → ℝ → ℝ)
    (hΞ : ∀ s ∈ J, ∀ u ∈ J, ∀ t ∈ J, s ≤ u → u ≤ t → |Ξ s u + Ξ u t - Ξ s t| ≤ K * ω s t ^ θ) :
    ∃ I : ℝ → ℝ → ℝ, (∀ s ∈ J, ∀ u ∈ J, ∀ t ∈ J, s ≤ u → u ≤ t → I s t = I s u + I u t) ∧
      ∀ s ∈ J, ∀ t ∈ J, s ≤ t → |I s t - Ξ s t| ≤ 2 * K / (1 - 2 ^ (1 - θ)) * ω s t ^ θ := by
  set L := 2 * K / (1 - 2 ^ (1 - θ))
  let U : Ultrafilter (Finset ℝ) := Ultrafilter.of atTop
  have hmem : ∀ v : ℝ, ∀ᶠ P in (U : Filter (Finset ℝ)), v ∈ P := fun v =>
    Ultrafilter.of_le (atTop : Filter (Finset ℝ))
      ((eventually_ge_atTop {v}).mono fun P hP => hP (mem_singleton_self v))
  have hbound : ∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∀ P : Finset ℝ, |riemann Ξ P s t - Ξ s t| ≤
      L * ω s t ^ θ := fun s hs t ht hst P =>
    riemann_sub_le hJ hω hθ hK hΞ P _ s hs t ht hst rfl
  have hlim : ∀ s ∈ J, ∀ t ∈ J, s ≤ t → Tendsto (fun P => riemann Ξ P s t) (U : Filter _)
      (𝓝 (limUnder (U : Filter (Finset ℝ)) fun P => riemann Ξ P s t)) := by
    intro s hs t ht hst
    apply tendsto_nhds_limUnder
    obtain ⟨x, -, hx⟩ := (isCompact_Icc (a := Ξ s t - L * ω s t ^ θ)
      (b := Ξ s t + L * ω s t ^ θ)).ultrafilter_le_nhds (U.map fun P => riemann Ξ P s t) (by
        rw [Ultrafilter.coe_map, le_principal_iff, Filter.mem_map]
        refine univ_mem' fun P => ?_
        have h := abs_sub_le_iff.mp (hbound s hs t ht hst P)
        exact Set.mem_Icc.mpr ⟨by linarith [h.2], by linarith [h.1]⟩)
    exact ⟨x, hx⟩
  refine ⟨fun s t => limUnder (U : Filter (Finset ℝ)) fun P => riemann Ξ P s t, ?_, ?_⟩
  · intro s hs u hu t ht hsu hut
    refine tendsto_nhds_unique ((hlim s hs t ht (hsu.trans hut)).congr' ?_)
      ((hlim s hs u hu hsu).add (hlim u hu t ht hut))
    filter_upwards [hmem u] with P hP
    exact riemann_split' P (Or.inl hP) hsu hut (germ_self hω hθ hΞ hs) (germ_self hω hθ hΞ ht)
  · intro s hs t ht hst
    exact le_of_tendsto' (((hlim s hs t ht hst).sub_const (Ξ s t)).abs) (hbound s hs t ht hst)

-- A cocycle bounded by `K ω^θ`, `θ > 1`, is the coboundary of a two-parameter function bounded
-- by a multiple of `ω^θ`.
private theorem exists_coboundary {J : Set ℝ} (hJ : J.OrdConnected) {ω : ℝ → ℝ → ℝ}
    (hω : IsControl ω J) {θ K : ℝ} (hθ : 1 < θ) (hK : 0 ≤ K) (c : ℝ → ℝ → ℝ → ℝ)
    (hcoc : ∀ r ∈ J, ∀ s ∈ J, ∀ u ∈ J, ∀ t ∈ J, r ≤ s → s ≤ u → u ≤ t →
      c r s t + c s u t = c r s u + c r u t)
    (hc : ∀ r ∈ J, ∀ s ∈ J, ∀ t ∈ J, r ≤ s → s ≤ t → |c r s t| ≤ K * ω r t ^ θ) :
    ∃ d : ℝ → ℝ → ℝ,
      (∀ r ∈ J, ∀ s ∈ J, ∀ t ∈ J, r ≤ s → s ≤ t → d r t = d r s + d s t + c r s t) ∧
      ∀ s ∈ J, ∀ t ∈ J, s ≤ t → |d s t| ≤ 2 * K / (1 - 2 ^ (1 - θ)) * ω s t ^ θ := by
  rcases J.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨fun _ _ => 0, fun r hr => absurd hr (Set.notMem_empty r),
      fun s hs => absurd hs (Set.notMem_empty s)⟩
  -- An exact solution without bounds, built from the base point `a`.
  let g : ℝ → ℝ → ℝ := fun x y => if a ≤ x then -c a x y else if a ≤ y then c x a y else -c x y a
  have hg : ∀ r ∈ J, ∀ s ∈ J, ∀ t ∈ J, r ≤ s → s ≤ t → g r t = g r s + g s t + c r s t := by
    intro r hr s hs t ht hrs hst
    simp only [g]
    split_ifs <;> first
      | linarith [hcoc a ha r hr s hs t ht (by linarith) hrs hst]
      | linarith [hcoc r hr a ha s hs t ht (by linarith) (by linarith) hst]
      | linarith [hcoc r hr s hs a ha t ht hrs (by linarith) (by linarith)]
      | linarith [hcoc r hr s hs t ht a ha hrs hst (by linarith)]
  obtain ⟨I, hI, hIb⟩ := exists_additive hJ hω hθ hK (fun x y => -g x y) (by
    intro s hs u hu t ht hsu hut
    rw [show -g s u + -g u t - -g s t = c s u t by linarith [hg s hs u hu t ht hsu hut]]
    exact hc s hs u hu t ht hsu hut)
  refine ⟨fun x y => g x y + I x y, fun r hr s hs t ht hrs hst => ?_, fun s hs t ht hst => ?_⟩
  · beta_reduce
    rw [hg r hr s hs t ht hrs hst, hI r hr s hs t ht hrs hst]
    ring
  · have h := hIb s hs t ht hst
    rwa [sub_neg_eq_add, add_comm] at h

/-! ### Tensor products of coefficient families -/

section Levels

variable {ι : Type*}

private theorem tensorMul_nil (F G : List ι → ℝ) : tensorMul F G [] = F [] * G [] := by
  simp [tensorMul]

-- The terms of a product at a word of length `n + 1`: the two ends and the cross terms.
private theorem tensorMul_split (F G : List ι → ℝ) {n : ℕ} {w : List ι}
    (hw : w.length = n + 1) :
    tensorMul F G w = F [] * G w + F w * G [] +
      ∑ m ∈ range n, F (w.take (m + 1)) * G (w.drop (m + 1)) := by
  rw [tensorMul, hw, sum_range_succ, sum_range_succ', List.take_of_length_le hw.le,
    List.drop_of_length_le hw.le]
  simp only [List.take_zero, List.drop_zero]
  ring

private theorem tensorMul_assoc (F G H : List ι → ℝ) (w : List ι) :
    tensorMul (tensorMul F G) H w = tensorMul F (tensorMul G H) w := by
  unfold tensorMul
  have hL : ∀ m ∈ range (w.length + 1),
      (∑ j ∈ range ((w.take m).length + 1), F ((w.take m).take j) * G ((w.take m).drop j)) *
        H (w.drop m) =
      ∑ j ∈ range (m + 1), F (w.take j) * G ((w.drop j).take (m - j)) *
        H ((w.drop j).drop (m - j)) := by
    intro m hm
    have hm' : m ≤ w.length := Nat.lt_succ_iff.mp (mem_range.mp hm)
    rw [List.length_take, min_eq_left hm', sum_mul]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [List.take_take, min_eq_left hj', List.drop_take, List.drop_drop, Nat.add_sub_cancel' hj']
  have hR : ∀ j ∈ range (w.length + 1),
      F (w.take j) * ∑ k ∈ range ((w.drop j).length + 1),
        G ((w.drop j).take k) * H ((w.drop j).drop k) =
      ∑ k ∈ range (w.length + 1 - j), F (w.take j) * G ((w.drop j).take k) *
        H ((w.drop j).drop k) := by
    intro j hj
    have hj' : j ≤ w.length := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [List.length_drop, mul_sum, show w.length - j + 1 = w.length + 1 - j by omega]
    exact sum_congr rfl fun k _ => by ring
  rw [sum_congr rfl hL, sum_congr rfl hR]
  exact sum_range_diag_flip (w.length + 1) fun j k =>
    F (w.take j) * G ((w.drop j).take k) * H ((w.drop j).drop k)

-- The cross terms of `X_{r,s} ⊗ X_{s,t}` at a word of length `n + 1`.
private noncomputable def cross (n : ℕ) (X : ℝ → ℝ → List ι → ℝ) (w : List ι) (r s t : ℝ) : ℝ :=
  ∑ m ∈ range n, X r s (w.take (m + 1)) * X s t (w.drop (m + 1))

-- Associativity makes the cross terms a cocycle.
private theorem cross_cocycle {n : ℕ} {X : ℝ → ℝ → List ι → ℝ} {J : Set ℝ}
    (hX : IsMultiplicativeFunctional n X J) {w : List ι} (hw : w.length = n + 1) {r s u t : ℝ}
    (hr : r ∈ J) (hs : s ∈ J) (hu : u ∈ J) (ht : t ∈ J) (hrs : r ≤ s) (hsu : s ≤ u)
    (hut : u ≤ t) :
    cross n X w r s t + cross n X w s u t = cross n X w r s u + cross n X w r u t := by
  have hmid1 : ∑ m ∈ range n, tensorMul (X r s) (X s u) (w.take (m + 1)) *
      X u t (w.drop (m + 1)) = cross n X w r u t := by
    refine sum_congr rfl fun m hm => ?_
    have := mem_range.mp hm
    rw [← hX.2 r hr s hs u hu hrs hsu _ (by rw [List.length_take]; omega)]
  have hmid2 : ∑ m ∈ range n, X r s (w.take (m + 1)) *
      tensorMul (X s u) (X u t) (w.drop (m + 1)) = cross n X w r s t := by
    refine sum_congr rfl fun m hm => ?_
    have := mem_range.mp hm
    rw [← hX.2 s hs u hu t ht hsu hut _ (by rw [List.length_drop]; omega)]
  have hL : tensorMul (tensorMul (X r s) (X s u)) (X u t) w =
      X u t w + X s u w + X r s w + cross n X w r s u + cross n X w r u t := by
    rw [tensorMul_split (tensorMul (X r s) (X s u)) (X u t) hw, hmid1, tensorMul_nil,
      tensorMul_split (X r s) (X s u) hw, hX.1 r hr s hs hrs, hX.1 s hs u hu hsu,
      hX.1 u hu t ht hut]
    unfold cross
    ring
  have hR : tensorMul (X r s) (tensorMul (X s u) (X u t)) w =
      X u t w + X s u w + X r s w + cross n X w s u t + cross n X w r s t := by
    rw [tensorMul_split (X r s) (tensorMul (X s u) (X u t)) hw, hmid2, tensorMul_nil,
      tensorMul_split (X s u) (X u t) hw, hX.1 r hr s hs hrs, hX.1 s hs u hu hsu,
      hX.1 u hu t ht hut]
    unfold cross
    ring
  linarith [tensorMul_assoc (X r s) (X s u) (X u t) w]

variable [Fintype ι]

private theorem abs_le_levelNorm (F : List ι → ℝ) {v : List ι} {i : ℕ} (hv : v.length = i) :
    |F v| ≤ levelNorm F i := by
  subst hv
  unfold levelNorm
  calc |F v| = |F (List.ofFn v.get)| := by rw [List.ofFn_get]
    _ ≤ _ := single_le_sum (f := fun g : Fin v.length → ι => |F (List.ofFn g)|)
      (fun g _ => abs_nonneg _) (mem_univ _)

private theorem abs_cross_le {p β : ℝ} (hp : 0 < p) (hβ : 0 < β) {n : ℕ}
    {X : ℝ → ℝ → List ι → ℝ} {ω : ℝ → ℝ → ℝ} {J : Set ℝ} (hω : IsControl ω J)
    (hctl : IsControlledBy p β n X ω J) {w : List ι} (hw : w.length = n + 1) {r s t : ℝ}
    (hr : r ∈ J) (hs : s ∈ J) (ht : t ∈ J) (hrs : r ≤ s) (hst : s ≤ t) :
    |cross n X w r s t| ≤ (∑ m ∈ range n, (β * Real.Gamma (((m + 1 : ℕ) : ℝ) / p + 1))⁻¹ *
      (β * Real.Gamma (((n - m : ℕ) : ℝ) / p + 1))⁻¹) * ω r t ^ (((n + 1 : ℕ) : ℝ) / p) := by
  rw [cross, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
  have hm' : m < n := mem_range.mp hm
  have hl1 : (w.take (m + 1)).length = m + 1 := by
    rw [List.length_take]
    omega
  have hl2 : (w.drop (m + 1)).length = n - m := by
    rw [List.length_drop]
    omega
  have hrt := hω.2.2.1 r hr t ht (hrs.trans hst)
  have hωrs : ω r s ≤ ω r t := by
    linarith [hω.2.2.2 r hr s hs t ht hrs hst, hω.2.2.1 s hs t ht hst]
  have hωst : ω s t ≤ ω r t := by
    linarith [hω.2.2.2 r hr s hs t ht hrs hst, hω.2.2.1 r hr s hs hrs]
  have hG1 := Real.Gamma_pos_of_pos (show 0 < ((m + 1 : ℕ) : ℝ) / p + 1 by positivity)
  have hG2 := Real.Gamma_pos_of_pos (show 0 < ((n - m : ℕ) : ℝ) / p + 1 by positivity)
  have h1 : |X r s (w.take (m + 1))| ≤ ω r t ^ (((m + 1 : ℕ) : ℝ) / p) *
      (β * Real.Gamma (((m + 1 : ℕ) : ℝ) / p + 1))⁻¹ := by
    refine (abs_le_levelNorm _ hl1).trans
      ((hctl (m + 1) (by omega) (by omega) r hr s hs hrs).trans ?_)
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (hω.2.2.1 r hr s hs hrs) hωrs (by positivity)) (by positivity)
  have h2 : |X s t (w.drop (m + 1))| ≤ ω r t ^ (((n - m : ℕ) : ℝ) / p) *
      (β * Real.Gamma (((n - m : ℕ) : ℝ) / p + 1))⁻¹ := by
    refine (abs_le_levelNorm _ hl2).trans
      ((hctl (n - m) (by omega) (by omega) s hs t ht hst).trans ?_)
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (hω.2.2.1 s hs t ht hst) hωst (by positivity)) (by positivity)
  have hexp : ((n + 1 : ℕ) : ℝ) / p = ((m + 1 : ℕ) : ℝ) / p + ((n - m : ℕ) : ℝ) / p := by
    push_cast [Nat.cast_sub hm'.le]
    ring
  rw [abs_mul, hexp, Real.rpow_add_of_nonneg hrt (by positivity) (by positivity)]
  calc |X r s (w.take (m + 1))| * |X s t (w.drop (m + 1))| ≤
        (ω r t ^ (((m + 1 : ℕ) : ℝ) / p) * (β * Real.Gamma (((m + 1 : ℕ) : ℝ) / p + 1))⁻¹) *
          (ω r t ^ (((n - m : ℕ) : ℝ) / p) * (β * Real.Gamma (((n - m : ℕ) : ℝ) / p + 1))⁻¹) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-! ### Existence -/

-- One more level: a multiplicative functional of degree `n ≥ ⌊p⌋` controlled by `ω` extends to
-- degree `n + 1`, still controlled by `ω`.
private theorem extend_step {p : ℝ} (hp : 1 ≤ p) {J : Set ℝ} (hJ : J.OrdConnected)
    {ω : ℝ → ℝ → ℝ} (hω : IsControl ω J) {n : ℕ} (hn : ⌊p⌋₊ ≤ n) {X : ℝ → ℝ → List ι → ℝ}
    (hX : IsMultiplicativeFunctional n X J) {β : ℝ} (hβ : 0 < β)
    (hctl : IsControlledBy p β n X ω J) :
    ∃ X' : ℝ → ℝ → List ι → ℝ, (∀ s t w, w.length ≤ n → X' s t w = X s t w) ∧
      IsMultiplicativeFunctional (n + 1) X' J ∧ ∃ β' > 0, IsControlledBy p β' (n + 1) X' ω J := by
  have hp0 : 0 < p := by linarith
  set θ : ℝ := ((n + 1 : ℕ) : ℝ) / p with hθ
  have hθ1 : 1 < θ := by
    rw [hθ, one_lt_div hp0]
    have h1 := Nat.lt_floor_add_one p
    have h2 : (⌊p⌋₊ : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    linarith
  set K : ℝ := ∑ m ∈ range n, (β * Real.Gamma (((m + 1 : ℕ) : ℝ) / p + 1))⁻¹ *
      (β * Real.Gamma (((n - m : ℕ) : ℝ) / p + 1))⁻¹
  have hK0 : 0 ≤ K := sum_nonneg fun m _ => by
    have := Real.Gamma_pos_of_pos (show 0 < ((m + 1 : ℕ) : ℝ) / p + 1 by positivity)
    have := Real.Gamma_pos_of_pos (show 0 < ((n - m : ℕ) : ℝ) / p + 1 by positivity)
    positivity
  set L : ℝ := 2 * K / (1 - 2 ^ (1 - θ)) with hL
  have hq : (2 : ℝ) ^ (1 - θ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hL0 : 0 ≤ L := div_nonneg (by positivity) (by linarith)
  have hcob : ∀ w : List ι, w.length = n + 1 → ∃ d : ℝ → ℝ → ℝ,
      (∀ r ∈ J, ∀ s ∈ J, ∀ t ∈ J, r ≤ s → s ≤ t → d r t = d r s + d s t + cross n X w r s t) ∧
      ∀ s ∈ J, ∀ t ∈ J, s ≤ t → |d s t| ≤ L * ω s t ^ θ := fun w hw =>
    exists_coboundary hJ hω hθ1 hK0 (cross n X w)
      (fun r hr s hs u hu t ht hrs hsu hut => cross_cocycle hX hw hr hs hu ht hrs hsu hut)
      (fun r hr s hs t ht hrs hst => abs_cross_le hp0 hβ hω hctl hw hr hs ht hrs hst)
  choose! d hd hdb using hcob
  let X' : ℝ → ℝ → List ι → ℝ := fun s t w => if w.length = n + 1 then d w s t else X s t w
  have hlo : ∀ s t w, w.length ≤ n → X' s t w = X s t w := fun s t w hw => by
    simp only [X', show w.length ≠ n + 1 by omega, ite_false]
  have htop : ∀ s t w, w.length = n + 1 → X' s t w = d w s t := fun s t w hw => by
    simp only [X', hw, ite_true]
  have hmult : IsMultiplicativeFunctional (n + 1) X' J := by
    refine ⟨fun s hs t ht hst => by rw [hlo s t [] (Nat.zero_le _)]; exact hX.1 s hs t ht hst, ?_⟩
    intro r hr s hs t ht hrs hst w hw
    rcases Nat.lt_or_ge w.length (n + 1) with hlt | hge
    · have hle : w.length ≤ n := by omega
      rw [hlo r t w hle, hX.2 r hr s hs t ht hrs hst w hle]
      unfold tensorMul
      refine sum_congr rfl fun m _ => ?_
      rw [hlo r s _ (by rw [List.length_take]; omega), hlo s t _ (by rw [List.length_drop]; omega)]
    · have hw' : w.length = n + 1 := le_antisymm hw hge
      have hmid : ∑ m ∈ range n, X' r s (w.take (m + 1)) * X' s t (w.drop (m + 1)) =
          cross n X w r s t := by
        refine sum_congr rfl fun m hm => ?_
        have := mem_range.mp hm
        rw [hlo r s _ (by rw [List.length_take]; omega),
          hlo s t _ (by rw [List.length_drop]; omega)]
      rw [htop r t w hw', hd w hw' r hr s hs t ht hrs hst, tensorMul_split _ _ hw', hmid,
        hlo r s [] (Nat.zero_le _), hlo s t [] (Nat.zero_le _), hX.1 r hr s hs hrs,
        hX.1 s hs t ht hst, htop r s w hw', htop s t w hw']
      ring
  have hG : 0 < Real.Gamma (θ + 1) := Real.Gamma_pos_of_pos (by positivity)
  set M : ℝ := (Fintype.card (Fin (n + 1) → ι) : ℝ) * L + 1
  have hM : 0 < M := by positivity
  have hβ' : 0 < min β (M * Real.Gamma (θ + 1))⁻¹ := lt_min hβ (by positivity)
  refine ⟨X', hlo, hmult, min β (M * Real.Gamma (θ + 1))⁻¹, hβ', ?_⟩
  intro i hi1 hin s hs t ht hst
  have hωst := hω.2.2.1 s hs t ht hst
  rcases Nat.lt_or_ge i (n + 1) with hlt | hge
  · have hle : i ≤ n := by omega
    have heq : levelNorm (X' s t) i = levelNorm (X s t) i := by
      unfold levelNorm
      exact sum_congr rfl fun g _ => by rw [hlo s t _ (by rw [List.length_ofFn]; exact hle)]
    rw [heq]
    refine (hctl i hi1 hle s hs t ht hst).trans ?_
    have hGi := Real.Gamma_pos_of_pos (show 0 < (i : ℝ) / p + 1 by positivity)
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hωst _) (mul_pos hβ' hGi)
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hGi.le)
  · obtain rfl : i = n + 1 := le_antisymm hin hge
    have hle : min β (M * Real.Gamma (θ + 1))⁻¹ * Real.Gamma (θ + 1) ≤ M⁻¹ := by
      calc min β (M * Real.Gamma (θ + 1))⁻¹ * Real.Gamma (θ + 1)
          ≤ (M * Real.Gamma (θ + 1))⁻¹ * Real.Gamma (θ + 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hG.le
        _ = M⁻¹ := by
          rw [mul_inv, mul_assoc, inv_mul_cancel₀ hG.ne', mul_one]
    calc levelNorm (X' s t) (n + 1) = ∑ g : Fin (n + 1) → ι, |d (List.ofFn g) s t| := by
          unfold levelNorm
          exact sum_congr rfl fun g _ => by rw [htop s t _ (List.length_ofFn)]
      _ ≤ ∑ _g : Fin (n + 1) → ι, L * ω s t ^ θ :=
          sum_le_sum fun g _ => hdb _ List.length_ofFn s hs t ht hst
      _ = (Fintype.card (Fin (n + 1) → ι) : ℝ) * L * ω s t ^ θ := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          ring
      _ ≤ M * ω s t ^ θ :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hωst _)
      _ = ω s t ^ θ / M⁻¹ := by rw [div_inv_eq_mul, mul_comm]
      _ ≤ ω s t ^ θ / (min β (M * Real.Gamma (θ + 1))⁻¹ * Real.Gamma (θ + 1)) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hωst _) (mul_pos hβ' hG) hle

private theorem exists_extension {p : ℝ} (hp : 1 ≤ p) {J : Set ℝ} (hJ : J.OrdConnected)
    (X : ℝ → ℝ → List ι → ℝ) (hX : IsMultiplicativeFunctional ⌊p⌋₊ X J)
    (hXp : HasFinitePVariation p ⌊p⌋₊ X J) :
    ∃ Y : ℝ → ℝ → List ι → ℝ, (∀ s t w, w.length ≤ ⌊p⌋₊ → Y s t w = X s t w) ∧
      ∀ m, IsMultiplicativeFunctional m Y J ∧ HasFinitePVariation p m Y J := by
  obtain ⟨ω, hω, β₀, hβ₀, hctl₀⟩ := hXp
  have step : ∀ (k : ℕ) (Z : ℝ → ℝ → List ι → ℝ),
      (IsMultiplicativeFunctional (⌊p⌋₊ + k) Z J ∧
        ∃ β > 0, IsControlledBy p β (⌊p⌋₊ + k) Z ω J) →
      ∃ Z' : ℝ → ℝ → List ι → ℝ, (IsMultiplicativeFunctional (⌊p⌋₊ + k + 1) Z' J ∧
        ∃ β > 0, IsControlledBy p β (⌊p⌋₊ + k + 1) Z' ω J) ∧
        ∀ s t w, w.length ≤ ⌊p⌋₊ + k → Z' s t w = Z s t w := by
    rintro k Z ⟨hZ, β, hβ, hZc⟩
    obtain ⟨Z', hagree, hmult, hctl⟩ := extend_step hp hJ hω (Nat.le_add_right _ _) hZ hβ hZc
    exact ⟨Z', ⟨hmult, hctl⟩, hagree⟩
  choose! F hF hFagree using step
  let seq : ℕ → ℝ → ℝ → List ι → ℝ := fun k =>
    Nat.rec (motive := fun _ => ℝ → ℝ → List ι → ℝ) X (fun k Z => F k Z) k
  have hseq : ∀ k, IsMultiplicativeFunctional (⌊p⌋₊ + k) (seq k) J ∧
      ∃ β > 0, IsControlledBy p β (⌊p⌋₊ + k) (seq k) ω J := by
    intro k
    induction k with
    | zero => exact ⟨hX, β₀, hβ₀, hctl₀⟩
    | succ k ih => exact hF k (seq k) ih
  have hstab : ∀ k j, k ≤ j → ∀ s t w, w.length ≤ ⌊p⌋₊ + k → seq j s t w = seq k s t w := by
    intro k j hkj s t w hw
    induction j, hkj using Nat.le_induction with
    | base => rfl
    | succ j hkj ih =>
      rw [← ih]
      exact hFagree j (seq j) (hseq j) s t w (by omega)
  have hY : ∀ m s t w, w.length ≤ m → seq w.length s t w = seq m s t w := fun m s t w hw =>
    (hstab w.length m hw s t w (Nat.le_add_left _ _)).symm ▸ rfl
  refine ⟨fun s t w => seq w.length s t w, fun s t w hw => ?_, fun m => ?_⟩
  · exact hstab 0 w.length (Nat.zero_le _) s t w (by simpa using hw)
  obtain ⟨hmult, β, hβ, hc⟩ := hseq m
  refine ⟨⟨fun s hs t ht hst => ?_, fun r hr s hs t ht hrs hst w hw => ?_⟩, ω, hω, β, hβ,
    fun i hi1 him s hs t ht hst => ?_⟩
  · exact (hY m s t [] (Nat.zero_le _)).trans (hmult.1 s hs t ht hst)
  · change seq w.length r t w = tensorMul (fun v => seq v.length r s v)
      (fun v => seq v.length s t v) w
    rw [hY m r t w hw, hmult.2 r hr s hs t ht hrs hst w (by omega)]
    unfold tensorMul
    refine sum_congr rfl fun j _ => ?_
    beta_reduce
    rw [hY m r s (w.take j) (by rw [List.length_take]; omega),
      hY m s t (w.drop j) (by rw [List.length_drop]; omega)]
  · have heq : levelNorm (fun v => seq v.length s t v) i = levelNorm (seq m s t) i := by
      unfold levelNorm
      refine sum_congr rfl fun g _ => ?_
      beta_reduce
      rw [hY m s t (List.ofFn g) (by rw [List.length_ofFn]; exact him)]
    change levelNorm (fun v => seq v.length s t v) i ≤ _
    rw [heq]
    exact hc i hi1 (by omega) s hs t ht hst

/-! ### Uniqueness -/

private theorem control_add {J : Set ℝ} {ω η : ℝ → ℝ → ℝ} (hω : IsControl ω J)
    (hη : IsControl η J) : IsControl (fun s t => ω s t + η s t) J :=
  ⟨hω.1.add hη.1, fun t ht => by simp [hω.2.1 t ht, hη.2.1 t ht],
    fun s hs t ht hst => add_nonneg (hω.2.2.1 s hs t ht hst) (hη.2.2.1 s hs t ht hst),
    fun s hs t ht u hu hst htu => by
      linarith [hω.2.2.2 s hs t ht u hu hst htu, hη.2.2.2 s hs t ht u hu hst htu]⟩

private theorem exists_bisect {J : Set ℝ} (hJ : J.OrdConnected) {ω : ℝ → ℝ → ℝ}
    (hω : IsControl ω J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t) :
    ∃ u ∈ J, s ≤ u ∧ u ≤ t ∧ ω s u ≤ ω s t / 2 ∧ ω u t ≤ ω s t / 2 := by
  have hmem : Set.Icc s t ⊆ J := hJ.out hs ht
  have hc : ContinuousOn (ω s) (Set.Icc s t) :=
    hω.1.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hu => ⟨hs, hmem hu, hu.1⟩)
  have hnn := hω.2.2.1 s hs t ht hst
  obtain ⟨u, hu, he⟩ := intermediate_value_Icc hst hc
    (show ω s t / 2 ∈ Set.Icc (ω s s) (ω s t) by rw [hω.2.1 s hs]; constructor <;> linarith)
  exact ⟨u, hmem hu, hu.1, hu.2, he.le, by
    linarith [hω.2.2.2 s hs u (hmem hu) t ht hu.1 hu.2]⟩

-- An additive function of size `O(ω^θ)` with `θ > 1` vanishes.
private theorem eq_zero_of_additive {J : Set ℝ} (hJ : J.OrdConnected) {ω : ℝ → ℝ → ℝ}
    (hω : IsControl ω J) {θ K : ℝ} (hθ : 1 < θ) (hK : 0 ≤ K) {D : ℝ → ℝ → ℝ}
    (hadd : ∀ s ∈ J, ∀ u ∈ J, ∀ t ∈ J, s ≤ u → u ≤ t → D s t = D s u + D u t)
    (hD : ∀ s ∈ J, ∀ t ∈ J, s ≤ t → |D s t| ≤ K * ω s t ^ θ) :
    ∀ s ∈ J, ∀ t ∈ J, s ≤ t → D s t = 0 := by
  set q : ℝ := 2 ^ (1 - θ) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hiter : ∀ l : ℕ, ∀ s ∈ J, ∀ t ∈ J, s ≤ t → |D s t| ≤ q ^ l * K * ω s t ^ θ := by
    intro l
    induction l with
    | zero => simpa using hD
    | succ l ih =>
      intro s hs t ht hst
      obtain ⟨u, hu, hsu, hut, h1, h2⟩ := exists_bisect hJ hω hs ht hst
      have hωst := hω.2.2.1 s hs t ht hst
      have hc : 0 ≤ q ^ l * K := by positivity
      have e1 : ω s u ^ θ ≤ (ω s t / 2) ^ θ :=
        Real.rpow_le_rpow (hω.2.2.1 s hs u hu hsu) h1 (by linarith)
      have e2 : ω u t ^ θ ≤ (ω s t / 2) ^ θ :=
        Real.rpow_le_rpow (hω.2.2.1 u hu t ht hut) h2 (by linarith)
      have e3 : (ω s t / 2) ^ θ = q / 2 * ω s t ^ θ := by
        rw [Real.div_rpow hωst (by norm_num), hq, Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
          Real.rpow_one]
        have h2θ : (0 : ℝ) < 2 ^ θ := by positivity
        field_simp
      rw [hadd s hs u hu t ht hsu hut]
      calc |D s u + D u t| ≤ |D s u| + |D u t| := abs_add_le _ _
        _ ≤ q ^ l * K * ω s u ^ θ + q ^ l * K * ω u t ^ θ :=
          add_le_add (ih s hs u hu hsu) (ih u hu t ht hut)
        _ ≤ q ^ l * K * (ω s t / 2) ^ θ + q ^ l * K * (ω s t / 2) ^ θ :=
          add_le_add (mul_le_mul_of_nonneg_left e1 hc) (mul_le_mul_of_nonneg_left e2 hc)
        _ = q ^ (l + 1) * K * ω s t ^ θ := by
          rw [e3, pow_succ]
          ring
  intro s hs t ht hst
  have hlim : Tendsto (fun l : ℕ => q ^ l * K * ω s t ^ θ) atTop (𝓝 (0 * K * ω s t ^ θ)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const K).mul_const _
  rw [zero_mul, zero_mul] at hlim
  exact abs_nonpos_iff.mp (ge_of_tendsto' hlim fun l => hiter l s hs t ht hst)

-- Two extensions that agree up to level `⌊p⌋` agree up to the common degree.
private theorem eq_of_agree {p : ℝ} (hp : 1 ≤ p) {J : Set ℝ} (hJ : J.OrdConnected) {m : ℕ}
    {Y Z : ℝ → ℝ → List ι → ℝ}
    (hagree : ∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∀ w : List ι, w.length ≤ ⌊p⌋₊ → Z s t w = Y s t w)
    (hY : IsMultiplicativeFunctional m Y J) (hYp : HasFinitePVariation p m Y J)
    (hZ : IsMultiplicativeFunctional m Z J) (hZp : HasFinitePVariation p m Z J) (k : ℕ) :
    ∀ w : List ι, w.length = k → k ≤ m → ∀ s ∈ J, ∀ t ∈ J, s ≤ t → Z s t w = Y s t w := by
  have hp0 : 0 < p := by linarith
  obtain ⟨ωY, hωY, βY, hβY, hYc⟩ := hYp
  obtain ⟨ωZ, hωZ, βZ, hβZ, hZc⟩ := hZp
  have hω := control_add hωZ hωY
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro w hwk hkm s hs t ht hst
  by_cases hkp : k ≤ ⌊p⌋₊
  · exact hagree s hs t ht hst w (hwk.le.trans hkp)
  push Not at hkp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set θ : ℝ := ((k' + 1 : ℕ) : ℝ) / p with hθ
  have hθ1 : 1 < θ := by
    rw [hθ, one_lt_div hp0]
    have h1 := Nat.lt_floor_add_one p
    have h2 : ((⌊p⌋₊ + 1 : ℕ) : ℝ) ≤ ((k' + 1 : ℕ) : ℝ) := by exact_mod_cast hkp
    push_cast at h2 ⊢
    linarith
  have hG := Real.Gamma_pos_of_pos (show 0 < θ + 1 by positivity)
  set K : ℝ := (βZ * Real.Gamma (θ + 1))⁻¹ + (βY * Real.Gamma (θ + 1))⁻¹
  have hK0 : 0 ≤ K := by positivity
  have hwm : w.length ≤ m := hwk.le.trans hkm
  have hadd : ∀ a ∈ J, ∀ u ∈ J, ∀ b ∈ J, a ≤ u → u ≤ b →
      Z a b w - Y a b w = (Z a u w - Y a u w) + (Z u b w - Y u b w) := by
    intro a ha u hu b hb hau hub
    have hmid : ∑ j ∈ range k', Z a u (w.take (j + 1)) * Z u b (w.drop (j + 1)) =
        ∑ j ∈ range k', Y a u (w.take (j + 1)) * Y u b (w.drop (j + 1)) := by
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.mp hj
      rw [ih (j + 1) (by omega) _ (by rw [List.length_take]; omega) (by omega) a ha u hu hau,
        ih (k' - j) (by omega) _ (by rw [List.length_drop]; omega) (by omega) u hu b hb hub]
    rw [hZ.2 a ha u hu b hb hau hub w hwm, hY.2 a ha u hu b hb hau hub w hwm,
      tensorMul_split _ _ hwk, tensorMul_split _ _ hwk, hZ.1 a ha u hu hau, hZ.1 u hu b hb hub,
      hY.1 a ha u hu hau, hY.1 u hu b hb hub, hmid]
    ring
  have hD : ∀ a ∈ J, ∀ b ∈ J, a ≤ b →
      |Z a b w - Y a b w| ≤ K * (fun s t => ωZ s t + ωY s t) a b ^ θ := by
    intro a ha b hb hab
    have hZa := hωZ.2.2.1 a ha b hb hab
    have hYa := hωY.2.2.1 a ha b hb hab
    have h1 : |Z a b w| ≤ ωZ a b ^ θ / (βZ * Real.Gamma (θ + 1)) :=
      (abs_le_levelNorm _ hwk).trans (hZc (k' + 1) (by omega) hkm a ha b hb hab)
    have h2 : |Y a b w| ≤ ωY a b ^ θ / (βY * Real.Gamma (θ + 1)) :=
      (abs_le_levelNorm _ hwk).trans (hYc (k' + 1) (by omega) hkm a ha b hb hab)
    have e1 : ωZ a b ^ θ ≤ (ωZ a b + ωY a b) ^ θ :=
      Real.rpow_le_rpow hZa (by linarith) (by linarith)
    have e2 : ωY a b ^ θ ≤ (ωZ a b + ωY a b) ^ θ :=
      Real.rpow_le_rpow hYa (by linarith) (by linarith)
    have hZG : 0 < βZ * Real.Gamma (θ + 1) := mul_pos hβZ hG
    have hYG : 0 < βY * Real.Gamma (θ + 1) := mul_pos hβY hG
    calc |Z a b w - Y a b w| ≤ |Z a b w| + |Y a b w| := abs_sub_le_iff.mpr ⟨by
          linarith [le_abs_self (Z a b w), neg_abs_le (Y a b w)], by
          linarith [neg_abs_le (Z a b w), le_abs_self (Y a b w)]⟩ |>.trans le_rfl
      _ ≤ ωZ a b ^ θ / (βZ * Real.Gamma (θ + 1)) + ωY a b ^ θ / (βY * Real.Gamma (θ + 1)) :=
          add_le_add h1 h2
      _ ≤ (ωZ a b + ωY a b) ^ θ / (βZ * Real.Gamma (θ + 1)) +
          (ωZ a b + ωY a b) ^ θ / (βY * Real.Gamma (θ + 1)) :=
          add_le_add (div_le_div_of_nonneg_right e1 hZG.le) (div_le_div_of_nonneg_right e2 hYG.le)
      _ = K * (fun s t => ωZ s t + ωY s t) a b ^ θ := by
          simp only [K, div_eq_mul_inv]
          ring
  exact sub_eq_zero.mp (eq_zero_of_additive hJ hω hθ1 hK0 hadd hD s hs t ht hst)

end Levels

/-! ### The extension theorem -/

/-- **Lyons's extension theorem: existence and uniqueness.** Let `p ≥ 1`, let `J` be an interval
and let `X` be a multiplicative functional of degree `⌊p⌋` on `J` with finite `p`-variation. Then
there is a multiplicative functional `Y` of every degree, agreeing with `X` on the levels
`0, …, ⌊p⌋`, with finite `p`-variation in every degree; and any multiplicative functional of some
degree `m` with finite `p`-variation that agrees with `X` up to level `⌊p⌋` agrees with `Y` up to
level `m` (T. Lyons, *Differential equations driven by rough signals*, Rev. Mat. Iberoam. 14
(1998), Theorem 2.2.1). -/
public theorem exists_unique_extension {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 ≤ p)
    {J : Set ℝ} (hJ : J.OrdConnected) (X : ℝ → ℝ → List ι → ℝ)
    (hX : IsMultiplicativeFunctional ⌊p⌋₊ X J) (hXp : HasFinitePVariation p ⌊p⌋₊ X J) :
    ∃ Y : ℝ → ℝ → List ι → ℝ,
      (∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∀ w : List ι, w.length ≤ ⌊p⌋₊ → Y s t w = X s t w) ∧
      (∀ m, IsMultiplicativeFunctional m Y J ∧ HasFinitePVariation p m Y J) ∧
      ∀ (m : ℕ) (Z : ℝ → ℝ → List ι → ℝ),
        (∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∀ w : List ι, w.length ≤ ⌊p⌋₊ → Z s t w = X s t w) →
        IsMultiplicativeFunctional m Z J → HasFinitePVariation p m Z J →
        ∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∀ w : List ι, w.length ≤ m → Z s t w = Y s t w := by
  obtain ⟨Y, hYX, hY⟩ := exists_extension hp hJ X hX hXp
  refine ⟨Y, fun s _ t _ _ w hw => hYX s t w hw, hY, fun m Z hZX hZ hZp s hs t ht hst w hw => ?_⟩
  exact eq_of_agree hp hJ (fun s hs t ht hst w hw => by rw [hZX s hs t ht hst w hw, hYX s t w hw])
    (hY m).1 (hY m).2 hZ hZp w.length w rfl hw s hs t ht hst

end MathlibExt.Analysis.PathSignature.ExtensionTheoremWanted
