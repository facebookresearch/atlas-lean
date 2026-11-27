/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity

/-! # Multiplicities of Beatty floor fibers

For `1 / (k + 1) < α < 1 / k`, every fiber `{n : ℕ | 0 < n ∧ ⌊n * α⌋ = t}`
has cardinality `k` or `k + 1`, and each multiplicity occurs for infinitely many `t`
(`beatty_floor_fiber_card_eq_or_eq_succ`).

Statements from G. Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104 (arXiv:2305.15361).
-/

namespace MetaMathlibExt

namespace beatty_floor_fiber_card_eq_or_eq_succ

/-- The slope bounds force `1 ≤ k`, `0 < α` and `k < 1 / α < k + 1`. -/
private theorem bounds {α : ℝ} {k : ℕ} (h1 : 1 / ((k : ℝ) + 1) < α)
    (h2 : α < 1 / (k : ℝ)) : 1 ≤ k ∧ 0 < α ∧ (k : ℝ) < 1 / α ∧ 1 / α < (k : ℝ) + 1 := by
  have hk : 1 ≤ k := by
    by_contra h
    simp only [not_le] at h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [Nat.cast_zero, zero_add, div_one] at h1
    simp only [Nat.cast_zero, div_zero] at h2
    linarith
  have hα : 0 < α := lt_trans (by positivity) h1
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := zero_lt_one.trans_le hkR
  have hkp : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hlo : (k : ℝ) < 1 / α := by
    rw [lt_div_iff₀ hα]
    have h2' : α * k < 1 := (lt_div_iff₀ hkpos).mp h2
    calc (k : ℝ) * α = α * k := mul_comm _ _
      _ < 1 := h2'
  have hhi : 1 / α < (k : ℝ) + 1 := by
    rw [div_lt_iff₀ hα]
    have h1' : 1 < α * ((k : ℝ) + 1) := (div_lt_iff₀ hkp).mp h1
    calc (1 : ℝ) < α * (↑k + 1) := h1'
      _ = (↑k + 1) * α := mul_comm _ _
  exact ⟨hk, hα, hlo, hhi⟩

/-- Shifting the argument of `Nat.ceil` by `d ∈ (k, k + 1)` adds `k` or `k + 1`. -/
private theorem ceil_add_sub_eq_or (x d : ℝ) (k : ℕ) (hx : 0 ≤ x)
    (hlo : (k : ℝ) < d) (hhi : d < (k : ℝ) + 1) :
    ⌈x + d⌉₊ - ⌈x⌉₊ = k ∨ ⌈x + d⌉₊ - ⌈x⌉₊ = k + 1 := by
  have hub : ⌈x + d⌉₊ ≤ ⌈x⌉₊ + k + 1 := by
    rw [Nat.ceil_le]
    push_cast
    linarith [Nat.le_ceil x, hhi]
  have hlb : ⌈x⌉₊ + k ≤ ⌈x + d⌉₊ := by
    by_contra h
    simp only [not_le] at h
    have h4 : ⌈x + d⌉₊ + 1 ≤ ⌈x⌉₊ + k := by omega
    have hle : (⌈x + d⌉₊ : ℝ) + 1 ≤ (⌈x⌉₊ : ℝ) + k := by exact_mod_cast h4
    have h2 : x + d ≤ (⌈x + d⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
    linarith
  omega

/-- Positive indices giving the value `t` form a half-open interval of naturals. -/
private theorem fiber_ncard {α : ℝ} (hα : 0 < α) (t : ℕ) :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard =
      ⌈((t + 1 : ℕ) : ℝ) / α⌉₊ - max 1 ⌈(t : ℝ) / α⌉₊ := by
  rw [← Set.ncard_Ico_nat]
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, Int.floor_eq_iff, Int.cast_natCast, Set.mem_Ico, max_le_iff,
    Nat.ceil_le, Nat.lt_ceil, div_le_iff₀ hα, lt_div_iff₀ hα, Nat.cast_add_one, and_assoc,
    Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

/-- The fiber over `0` has exactly `k` elements. -/
private theorem fiber_zero {α : ℝ} {k : ℕ} (h1 : 1 / ((k : ℝ) + 1) < α)
    (h2 : α < 1 / (k : ℝ)) :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = ((0 : ℕ) : ℤ)}.ncard = k := by
  obtain ⟨_, hα, hlo, hhi⟩ := bounds h1 h2
  rw [fiber_ncard hα 0]
  have h10 : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
  have h0c : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
  rw [h10, h0c, zero_div, Nat.ceil_zero, max_eq_left zero_le_one]
  have hck : ⌈1 / α⌉₊ = k + 1 := by
    apply le_antisymm
    · rw [Nat.ceil_le]
      push_cast
      linarith [hhi]
    · have hle : (k : ℝ) < (⌈1 / α⌉₊ : ℝ) := lt_of_lt_of_le hlo (Nat.le_ceil _)
      have hlt : k < ⌈1 / α⌉₊ := by exact_mod_cast hle
      omega
  rw [hck]
  omega

/-- For `t ≥ 1` the fiber count is the difference of two consecutive ceils. -/
private theorem fiber_diff {α : ℝ} {k : ℕ} (h1 : 1 / ((k : ℝ) + 1) < α)
    (h2 : α < 1 / (k : ℝ)) {t : ℕ} (ht : 1 ≤ t) :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard =
      ⌈((t + 1 : ℕ) : ℝ) / α⌉₊ - ⌈(t : ℝ) / α⌉₊ := by
  obtain ⟨_, hα, _, _⟩ := bounds h1 h2
  rw [fiber_ncard hα t]
  have hmax : max 1 ⌈(t : ℝ) / α⌉₊ = ⌈(t : ℝ) / α⌉₊ := by
    apply max_eq_right
    have hpos : (0 : ℝ) < (t : ℝ) / α := by
      apply div_pos _ hα
      exact_mod_cast (by omega : 0 < t)
    have h := Nat.ceil_pos.mpr hpos
    omega
  rw [hmax]

/-- Every fiber has `k` or `k + 1` elements. -/
private theorem fiber_eq_or {α : ℝ} {k : ℕ} (h1 : 1 / ((k : ℝ) + 1) < α)
    (h2 : α < 1 / (k : ℝ)) (t : ℕ) :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k ∨
      {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1 := by
  obtain ⟨_, hα, hlo, hhi⟩ := bounds h1 h2
  by_cases ht : t = 0
  · subst ht
    rw [fiber_zero h1 h2]
    exact Or.inl rfl
  · rw [fiber_diff h1 h2 (by omega : 1 ≤ t)]
    have hsplit : ((t + 1 : ℕ) : ℝ) / α = (t : ℝ) / α + 1 / α := by
      push_cast
      ring
    rw [hsplit]
    exact ceil_add_sub_eq_or _ _ _ (div_nonneg (Nat.cast_nonneg _) hα.le) hlo hhi

/-- The ceil endpoints are monotone in the numerator. -/
private theorem ceil_div_mono {α : ℝ} (hα : 0 < α) {a b : ℕ} (h : a ≤ b) :
    ⌈(a : ℝ) / α⌉₊ ≤ ⌈(b : ℝ) / α⌉₊ := by
  apply Nat.ceil_le_ceil
  gcongr

/-- Fiber counts telescope over any interval above `0`. -/
private theorem sum_fiber_Icc {α : ℝ} {k : ℕ} (h1 : 1 / ((k : ℝ) + 1) < α)
    (h2 : α < 1 / (k : ℝ)) (T : ℕ) : ∀ L : ℕ, L ≤ T → 1 ≤ L →
    ∑ t ∈ Finset.Icc L T, {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard =
      ⌈((T + 1 : ℕ) : ℝ) / α⌉₊ - ⌈(L : ℝ) / α⌉₊ := by
  obtain ⟨_, hα, _, _⟩ := bounds h1 h2
  induction T with
  | zero =>
      intro L hLT hL
      omega
  | succ T ih =>
      intro L hLT hL
      by_cases h : L = T + 1
      · subst h
        rw [Finset.Icc_self, Finset.sum_singleton]
        exact fiber_diff h1 h2 (by omega)
      · have hLT' : L ≤ T := by omega
        rw [Finset.sum_Icc_succ_top (by omega : L ≤ T + 1)]
        rw [ih L hLT' hL]
        rw [fiber_diff h1 h2 (by omega : 1 ≤ T + 1)]
        have m1 := ceil_div_mono hα (show L ≤ T + 1 by omega)
        have m2 := ceil_div_mono hα (show T + 1 ≤ T + 1 + 1 by omega)
        omega

/-- Fibers cannot be eventually constant: the telescoped count would miss the ceil bounds. -/
private theorem not_eventually_eq {α : ℝ} {k : ℕ} (h1 : 1 / ((k : ℝ) + 1) < α)
    (h2 : α < 1 / (k : ℝ)) (d : ℕ) (hd : k = d ∨ k + 1 = d) :
    ¬∃ M, ∀ t : ℕ, M < t →
      {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = d := by
  obtain ⟨_, hα, hlo, hhi⟩ := bounds h1 h2
  rintro ⟨M, hM⟩
  rcases hd with rfl | rfl
  · have hδ : (0 : ℝ) < 1 / α - k := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt
      (max ((((⌈((M + 1 : ℕ) : ℝ) / α⌉₊ : ℕ) : ℝ) - ((M : ℝ) + 1) / α + 1) / (1 / α - k)) 0)
    have hNpos : 0 < N := by
      have h0 : (0 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
      exact_mod_cast h0
    have hNgrow : ((⌈((M + 1 : ℕ) : ℝ) / α⌉₊ : ℕ) : ℝ) - ((M : ℝ) + 1) / α + 1 <
        (N : ℝ) * (1 / α - k) := by
      have hlt := lt_of_le_of_lt (le_max_left _ _) hN
      exact (div_lt_iff₀ hδ).mp hlt
    have htele := sum_fiber_Icc h1 h2 (M + N) (M + 1) (by omega) (by omega)
    have hall : ∀ t ∈ Finset.Icc (M + 1) (M + N),
        {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k := by
      intro t ht
      apply hM
      rw [Finset.mem_Icc] at ht
      omega
    have hsum : ∑ t ∈ Finset.Icc (M + 1) (M + N),
        {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = N * k := by
      rw [Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
      congr 1
      omega
    have hmono : ⌈((M + 1 : ℕ) : ℝ) / α⌉₊ ≤ ⌈((M + N + 1 : ℕ) : ℝ) / α⌉₊ :=
      ceil_div_mono hα (by omega)
    have hB : N * k + ⌈((M + 1 : ℕ) : ℝ) / α⌉₊ = ⌈((M + N + 1 : ℕ) : ℝ) / α⌉₊ := by
      omega
    have hBcast : (N : ℝ) * k + (⌈((M + 1 : ℕ) : ℝ) / α⌉₊ : ℝ) =
        (⌈((M + N + 1 : ℕ) : ℝ) / α⌉₊ : ℝ) := by exact_mod_cast hB
    have hcast : ((M + N + 1 : ℕ) : ℝ) = (M : ℝ) + (N : ℝ) + 1 := by push_cast; ring
    have hceil_lo : ((M : ℝ) + (N : ℝ) + 1) / α ≤ (N : ℝ) * k + ⌈((M + 1 : ℕ) : ℝ) / α⌉₊ := by
      have h := Nat.le_ceil (((M + N + 1 : ℕ) : ℝ) / α)
      rwa [← hBcast, hcast] at h
    have hsplitM : ((M : ℝ) + (N : ℝ) + 1) / α = ((M : ℝ) + 1) / α + (N : ℝ) / α := by ring
    have hδdef : (N : ℝ) * (1 / α - k) = (N : ℝ) / α - (N : ℝ) * k := by ring
    linarith [hceil_lo, hsplitM, hδdef, hNgrow]
  · have hε : (0 : ℝ) < (k : ℝ) + 1 - 1 / α := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt
      (max ((((M : ℝ) + 1) / α + 1 - ((⌈((M + 1 : ℕ) : ℝ) / α⌉₊ : ℕ) : ℝ) + 1) /
        ((k : ℝ) + 1 - 1 / α)) 0)
    have hNpos : 0 < N := by
      have h0 : (0 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
      exact_mod_cast h0
    have hNgrow : ((M : ℝ) + 1) / α + 1 - ((⌈((M + 1 : ℕ) : ℝ) / α⌉₊ : ℕ) : ℝ) + 1 <
        (N : ℝ) * ((k : ℝ) + 1 - 1 / α) := by
      have hlt := lt_of_le_of_lt (le_max_left _ _) hN
      exact (div_lt_iff₀ hε).mp hlt
    have htele := sum_fiber_Icc h1 h2 (M + N) (M + 1) (by omega) (by omega)
    have hall : ∀ t ∈ Finset.Icc (M + 1) (M + N),
        {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1 := by
      intro t ht
      apply hM
      rw [Finset.mem_Icc] at ht
      omega
    have hsum : ∑ t ∈ Finset.Icc (M + 1) (M + N),
        {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = N * (k + 1) := by
      rw [Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
      congr 1
      omega
    have hmono : ⌈((M + 1 : ℕ) : ℝ) / α⌉₊ ≤ ⌈((M + N + 1 : ℕ) : ℝ) / α⌉₊ :=
      ceil_div_mono hα (by omega)
    have hB : N * (k + 1) + ⌈((M + 1 : ℕ) : ℝ) / α⌉₊ = ⌈((M + N + 1 : ℕ) : ℝ) / α⌉₊ := by
      omega
    have hBcast : (N : ℝ) * ((k + 1 : ℕ) : ℝ) + (⌈((M + 1 : ℕ) : ℝ) / α⌉₊ : ℝ) =
        (⌈((M + N + 1 : ℕ) : ℝ) / α⌉₊ : ℝ) := by exact_mod_cast hB
    have hcast : ((M + N + 1 : ℕ) : ℝ) = (M : ℝ) + (N : ℝ) + 1 := by push_cast; ring
    have hnonneg : (0 : ℝ) ≤ ((M + N + 1 : ℕ) : ℝ) / α :=
      div_nonneg (Nat.cast_nonneg _) hα.le
    have hceil_hi : (N : ℝ) * ((k + 1 : ℕ) : ℝ) + ⌈((M + 1 : ℕ) : ℝ) / α⌉₊ <
        ((M : ℝ) + (N : ℝ) + 1) / α + 1 := by
      have h := Nat.ceil_lt_add_one hnonneg
      rwa [← hBcast, hcast] at h
    have hsplitM : ((M : ℝ) + (N : ℝ) + 1) / α = ((M : ℝ) + 1) / α + (N : ℝ) / α := by ring
    have hεdef : (N : ℝ) * ((k : ℝ) + 1 - 1 / α) =
        (N : ℝ) * ((k + 1 : ℕ) : ℝ) - (N : ℝ) / α := by
      push_cast
      ring
    linarith [hceil_hi, hsplitM, hεdef, hNgrow]

end beatty_floor_fiber_card_eq_or_eq_succ

/-- **Multiplicities of the values of $\lfloor n\alpha\rfloor$ for $1/(k + 1) < \alpha < 1/k$.**
Let $k$ be a positive integer and let $\alpha$ be a real number with
$1/(k + 1) < \alpha < 1/k$. Then every non-negative integer $t$ equals $\lfloor n\alpha\rfloor$
for exactly $k$ or exactly $k + 1$ positive integers $n$, there are infinitely many $t$ for which
it is exactly $k$, and there are infinitely many $t$ for which it is exactly $k + 1$.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Lemma 1 (`integers-2025-A104-lem-1`). -/
public theorem beatty_floor_fiber_card_eq_or_eq_succ {α : ℝ} {k : ℕ}
    (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) :
    (∀ t : ℕ, {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k ∨
        {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1) ∧
      {t : ℕ | {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k}.Infinite ∧
      {t : ℕ | {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1}.Infinite := by
  refine ⟨fun t ↦ beatty_floor_fiber_card_eq_or_eq_succ.fiber_eq_or h1 h2 t, ?_, ?_⟩
  · by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨M, hM⟩ := hfin.bddAbove
    have hev : ∀ t : ℕ, M < t →
        {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1 := by
      intro t ht
      rcases beatty_floor_fiber_card_eq_or_eq_succ.fiber_eq_or h1 h2 t with h | h
      · exfalso
        have hmem : t ∈ {t : ℕ | {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k} := h
        have hle := (mem_upperBounds.mp hM) t hmem
        omega
      · exact h
    exact beatty_floor_fiber_card_eq_or_eq_succ.not_eventually_eq h1 h2 (k + 1) (Or.inr rfl)
      ⟨M, hev⟩
  · by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨M, hM⟩ := hfin.bddAbove
    have hev : ∀ t : ℕ, M < t →
        {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k := by
      intro t ht
      rcases beatty_floor_fiber_card_eq_or_eq_succ.fiber_eq_or h1 h2 t with h | h
      · exact h
      · exfalso
        have hmem : t ∈ {t : ℕ | {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1} := h
        have hle := (mem_upperBounds.mp hM) t hmem
        omega
    exact beatty_floor_fiber_card_eq_or_eq_succ.not_eventually_eq h1 h2 k (Or.inl rfl) ⟨M, hev⟩

end MetaMathlibExt
