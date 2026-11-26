/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Rayleigh
public import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat

/-! # Multiplicities of `⌊nα⌋` as `k` plus the indicator of a Beatty set

For an irrational `α` with `1/(k + 1) < α < 1/k`, the main result
`beatty_floor_fiber_card_eq_add_indicator` says that each non-negative integer `t` is the value of
`⌊nα⌋` for exactly `k + 1` positive integers `n` when `t` lies in the Beatty set of
`δ = 1/(α⁻¹ - k)`, and for exactly `k` of them otherwise.

The proof is direct. The positive integers `n` with `⌊nα⌋ = t` are those in `(t/α, (t + 1)/α)`,
so there are `⌊(t + 1)/α⌋ - ⌊t/α⌋ = k + ⌊(t + 1)φ⌋ - ⌊tφ⌋` of them, where `φ = α⁻¹ - k` lies in
`(0, 1)`. The last difference is the indicator of the Beatty set of `φ⁻¹`: it is `1` exactly when
some integer `m ≥ 1` lies in `(tφ, (t + 1)φ)`, or equivalently when `t = ⌊m/φ⌋`. We prove this
floor-increment identity directly rather than iterating Polanco's map `α ↦ α/(1 - α)`.

## References

* Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*, INTEGERS **25**
  (2025), Article A104, pp. 1–19, Lemmas 2 and 3 and Corollary 2. The floor-increment identity
  on p. 9 credits the next two references.
* Geremias Polanco, *The logarithm of irrational numbers and Beatty sequences*, Acta Arithmetica
  **179** (2017), pp. 101–123.
* Jean-Paul Allouche and Jeffrey Shallit, *Automatic Sequences: Theory, Applications,
  Generalizations*, Cambridge University Press (2003), Chapter 9, pp. 283–297, Lemma 9.1.3.
-/

namespace MetaMathlibExt

open Set

namespace beatty_floor_fiber_card_eq_add_indicator

/-- For irrational `α > 0`, the positive integers `n` with `⌊nα⌋ = t` are those in
`(⌊t/α⌋, ⌊(t + 1)/α⌋]`. -/
private theorem fiber_eq {α : ℝ} (hα : 0 < α) (hirr : Irrational α) (t : ℕ) :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t} = Ioc ⌊(t : ℝ) / α⌋₊ ⌊((t : ℝ) + 1) / α⌋₊ := by
  ext n
  -- The endpoints `t/α` (for `t ≠ 0`) and `(t + 1)/α` are irrational, so neither equals `n`.
  have hlo : (t : ℝ) / α < n ↔ 0 < n ∧ (t : ℝ) / α ≤ n := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · have hne : (t : ℝ) / α ≠ n := (hirr.natCast_div ht.ne').ne_nat n
      refine ⟨fun h ↦ ⟨?_, h.le⟩, fun h ↦ h.2.lt_of_ne hne⟩
      exact_mod_cast (div_nonneg (Nat.cast_nonneg t) hα.le).trans_lt h
  have hhi : n ≤ ⌊((t : ℝ) + 1) / α⌋₊ ↔ (n : ℝ) < ((t : ℝ) + 1) / α := by
    have hne : ((t : ℝ) + 1) / α ≠ n := by
      simpa using (hirr.natCast_div (Nat.succ_ne_zero t)).ne_nat n
    rw [Nat.le_floor_iff (by positivity)]
    exact ⟨fun h ↦ h.lt_of_ne hne.symm, le_of_lt⟩
  rw [mem_ofPred_eq, mem_Ioc, Nat.floor_lt (by positivity), hhi, hlo, Int.floor_eq_iff,
    Int.cast_natCast, div_le_iff₀ hα, lt_div_iff₀ hα, and_assoc]

/-- Writing `α⁻¹ = k + φ` with `φ ≥ 0`, the floor of `j/α` is `⌊jφ⌋ + jk`. -/
private theorem floor_div_eq {α φ : ℝ} {k : ℕ} (hαφ : α⁻¹ = k + φ) (hφ : 0 ≤ φ) (j : ℕ) :
    ⌊(j : ℝ) / α⌋₊ = ⌊(j : ℝ) * φ⌋₊ + j * k := by
  have h : (j : ℝ) / α = j * φ + ((j * k : ℕ) : ℝ) := by
    rw [div_eq_mul_inv, hαφ]
    push_cast
    ring
  rw [h, Nat.floor_add_natCast (mul_nonneg (Nat.cast_nonneg j) hφ)]

/-- For `0 ≤ φ < 1`, the floor of `(t + 1)φ` exceeds the floor of `tφ` by at most one. -/
private theorem floor_succ_mul_le {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (t : ℕ) :
    ⌊((t : ℝ) + 1) * φ⌋₊ ≤ ⌊(t : ℝ) * φ⌋₊ + 1 := by
  apply Nat.le_of_lt_succ
  rw [Nat.floor_lt (by positivity)]
  push_cast
  linarith [Nat.lt_floor_add_one ((t : ℝ) * φ)]

/-- For irrational `φ > 0`, a natural number `t` lies in the Beatty set of `φ⁻¹` exactly when the
floor of `(t + 1)φ` exceeds the floor of `tφ`. -/
private theorem mem_beattySeq_iff {φ : ℝ} (hφ : 0 < φ) (hirr : Irrational φ) (t : ℕ) :
    (t : ℤ) ∈ {beattySeq φ⁻¹ m | m > 0} ↔ ⌊(t : ℝ) * φ⌋₊ < ⌊((t : ℝ) + 1) * φ⌋₊ := by
  constructor
  · -- If `t = ⌊m/φ⌋` with `m ≥ 1`, then `tφ < m < (t + 1)φ`, as `m/φ` is irrational.
    rintro ⟨m, hm, hmt⟩
    lift m to ℕ using hm.le
    have hm0 : m ≠ 0 := by exact_mod_cast hm.ne'
    rw [beattySeq, Int.cast_natCast, Int.floor_eq_iff, Int.cast_natCast] at hmt
    have hne : (t : ℝ) ≠ m * φ⁻¹ := fun h ↦ (hirr.inv.natCast_mul hm0).ne_nat t h.symm
    have hlo : (t : ℝ) * φ < m := by
      rw [← lt_div_iff₀ hφ, div_eq_mul_inv]
      exact hmt.1.lt_of_ne hne
    have hhi : (m : ℝ) < ((t : ℝ) + 1) * φ := by
      rw [← div_lt_iff₀ hφ, div_eq_mul_inv]
      exact hmt.2
    calc ⌊(t : ℝ) * φ⌋₊ < m := (Nat.floor_lt (by positivity)).2 hlo
      _ ≤ ⌊((t : ℝ) + 1) * φ⌋₊ := Nat.le_floor hhi.le
  · -- Conversely `m = ⌊(t + 1)φ⌋` satisfies `tφ < m < (t + 1)φ`, so `t = ⌊m/φ⌋`.
    intro h
    set m := ⌊((t : ℝ) + 1) * φ⌋₊
    refine ⟨m, by exact_mod_cast (Nat.zero_le _).trans_lt h, ?_⟩
    rw [beattySeq, Int.cast_natCast, Int.floor_eq_iff, Int.cast_natCast]
    have hlo : (t : ℝ) * φ < m := (Nat.floor_lt (by positivity)).1 h
    have hhi : (m : ℝ) ≤ ((t : ℝ) + 1) * φ := Nat.floor_le (by positivity)
    have hne : (m : ℝ) ≠ ((t : ℝ) + 1) * φ := by
      have h' := (hirr.natCast_mul (Nat.succ_ne_zero t)).ne_nat m
      push_cast at h'
      exact fun h ↦ h' h.symm
    constructor
    · rw [← div_eq_mul_inv, le_div_iff₀ hφ]
      exact hlo.le
    · rw [← div_eq_mul_inv, div_lt_iff₀ hφ]
      exact hhi.lt_of_ne hne

end beatty_floor_fiber_card_eq_add_indicator

/-- **Explicit Beatty slope for floor-fiber multiplicities.**
Let `k` be a positive integer and let `α` be irrational with `1 / (k + 1) < α < 1 / k`.
The slope `γ = (α⁻¹ - k)⁻¹` is irrational and greater than one.
For every natural number `t`, the number of positive indices `n` with `⌊nα⌋ = t` equals `k + 1`
if `t` lies in the positive-index Beatty set of `γ`, and `k` otherwise. -/
public theorem beatty_floor_fiber_card_eq_add_indicator_explicit {α : ℝ} {k : ℕ}
    (hirr : Irrational α) (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) :
    1 < (α⁻¹ - (k : ℝ))⁻¹ ∧ Irrational (α⁻¹ - (k : ℝ))⁻¹ ∧
      ∀ t : ℕ, {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard =
        k + {beattySeq (α⁻¹ - (k : ℝ))⁻¹ m | m > 0}.indicator (1 : ℤ → ℕ) t := by
  have hα : 0 < α := lt_trans (by positivity) h1
  -- `1 / 0 = 0` in Lean, so `h2` rules out `k = 0`.
  have hk : (0 : ℝ) < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [CharP.cast_eq_zero, div_zero] at h2
      exact absurd h2 hα.not_gt
    · exact_mod_cast hk
  -- Write `α⁻¹ = k + φ` with `0 < φ < 1` irrational; the Beatty slope is `δ = φ⁻¹`.
  let φ : ℝ := α⁻¹ - k
  have hαφ : α⁻¹ = k + φ := by dsimp [φ]; ring
  have hφ0 : 0 < φ := by
    have : (k : ℝ) < α⁻¹ := by rwa [lt_inv_comm₀ hk hα, ← one_div]
    linarith
  have hφ1 : φ < 1 := by
    have : α⁻¹ < k + 1 := by rwa [inv_lt_comm₀ hα (by positivity), ← one_div]
    linarith
  have hφirr : Irrational φ := by
    simpa [hαφ] using hirr.inv.sub_natCast k
  refine ⟨(one_lt_inv₀ hφ0).2 hφ1, hφirr.inv, fun t ↦ ?_⟩
  have hsucc := beatty_floor_fiber_card_eq_add_indicator.floor_div_eq hαφ hφ0.le (t + 1)
  rw [Nat.cast_add_one] at hsucc
  rw [beatty_floor_fiber_card_eq_add_indicator.fiber_eq hα hirr t, ncard_Ioc_nat, hsucc,
    beatty_floor_fiber_card_eq_add_indicator.floor_div_eq hαφ hφ0.le t, add_one_mul t k]
  have hle := beatty_floor_fiber_card_eq_add_indicator.floor_succ_mul_le hφ0.le hφ1 t
  have hmono : ⌊(t : ℝ) * φ⌋₊ ≤ ⌊((t : ℝ) + 1) * φ⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hφ0.le)
  have hmem := beatty_floor_fiber_card_eq_add_indicator.mem_beattySeq_iff hφ0 hφirr t
  by_cases ht : (t : ℤ) ∈ {beattySeq φ⁻¹ m | m > 0}
  · rw [indicator_of_mem ht, Pi.one_apply]
    have := hmem.1 ht
    omega
  · rw [indicator_of_notMem ht]
    have := hmem.not.1 ht
    omega

/-- **Multiplicities of $\lfloor n\alpha\rfloor$ are $k$ plus the indicator of a Beatty set.** Let
$k$ be a positive integer and let $\alpha$ be an irrational number with
$1/(k + 1) < \alpha < 1/k$. Then there is a real number $\delta > 0$ such that, writing $D$ for
the set of the numbers $\lfloor m\delta\rfloor$ for positive integers $m$, every non-negative
integer $t$ equals $\lfloor n\alpha\rfloor$ for exactly $k + 1$ positive integers $n$ if $t \in D$,
and for exactly $k$ positive integers $n$ if $t \notin D$.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Corollary 2 (`integers-2025-A104-cor-2`). -/
public theorem beatty_floor_fiber_card_eq_add_indicator {α : ℝ} {k : ℕ}
    (hirr : Irrational α) (h1 : 1 / ((k : ℝ) + 1) < α) (h2 : α < 1 / (k : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℕ, {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard =
      k + {beattySeq δ m | m > 0}.indicator (1 : ℤ → ℕ) t := by
  obtain ⟨hδ, _, hcard⟩ := beatty_floor_fiber_card_eq_add_indicator_explicit hirr h1 h2
  exact ⟨_, zero_lt_one.trans hδ, hcard⟩

end MetaMathlibExt
