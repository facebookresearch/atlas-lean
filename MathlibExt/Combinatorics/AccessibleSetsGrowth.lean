/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.AccessibleSets
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Eventual growth and two-accessibility

If a positive gap sequence eventually grows by a factor of at least $3 + \delta$ for some
$\delta > 0$, its range is not two-accessible.
-/

namespace MetaMathlibExt

namespace not_two_accessible_of_growth

/-- Nest intervals of scales on which the fractional part of the scaled gap is in
`[ε, 1/2]`. The initial interval also controls gaps smaller than `a 0`. -/
private lemma exists_scale (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) {ε : ℝ}
    (hε : 0 < ε) (hhalf : ε ≤ 1 / 2)
    (hwidth : ∀ n, 3 / 2 * a n ≤ (1 / 2 - ε) * a (n + 1)) :
    ∃ α ∈ Set.Icc (ε / a 0) ((1 / 2) / a 0),
      ∀ n, Int.fract (α * a n) ∈ Set.Icc ε (1 / 2) := by
  -- At the next scale, round the previous lower endpoint up to an integer.
  let k : ℕ → ℤ := Nat.rec 0 fun n (z : ℤ) => ⌈((z : ℝ) + ε) / a n * a (n + 1)⌉
  let lo (n : ℕ) : ℝ := (Int.cast (k n) + ε) / a n
  let hi (n : ℕ) : ℝ := (Int.cast (k n) + 1 / 2) / a n
  have hlo : Monotone lo := monotone_nat_of_le_succ fun n => by
    apply (le_div_iff₀ (ha _)).2
    exact (Int.le_ceil (lo n * a (n + 1))).trans (le_add_of_nonneg_right hε.le)
  have hhi : Antitone hi := antitone_nat_of_succ_le fun n => by
    apply (div_le_iff₀ (ha _)).2
    have hlen : 3 / 2 ≤ (hi n - lo n) * a (n + 1) := by
      dsimp only [hi, lo]
      rw [← sub_div, add_sub_add_left_eq_sub, div_mul_eq_mul_div]
      exact (le_div_iff₀ (ha n)).2 (hwidth n)
    have hceil : Int.cast (k (n + 1)) < lo n * a (n + 1) + 1 :=
      Int.ceil_lt_add_one _
    linarith only [hceil, hlen]
  have hle (n : ℕ) : lo n ≤ hi n :=
    div_le_div_of_nonneg_right (add_le_add_right hhalf _) (ha n).le
  obtain ⟨α, hl, hu⟩ := exists_between_of_forall_le
    (Set.range_nonempty lo) (Set.range_nonempty hi) (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact (hlo (le_max_left i j)).trans ((hle _).trans (hhi (le_max_right i j))))
  have bounds (n : ℕ) : α ∈ Set.Icc (lo n) (hi n) :=
    ⟨hl (Set.mem_range_self n), hu (Set.mem_range_self n)⟩
  refine ⟨α, by simpa [lo, hi, k] using bounds 0, fun n => ?_⟩
  have lower := (div_le_iff₀ (ha n)).1 (bounds n).1
  have upper := (le_div_iff₀ (ha n)).1 (bounds n).2
  have hfloor : ⌊α * a n⌋ = k n :=
    Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  simp only [Int.fract, hfloor, Set.mem_Icc]
  constructor <;> linarith

end not_two_accessible_of_growth

/-- **Fast eventual growth rules out 2-accessibility.** Let $d_0 < d_1 < d_2 < \cdots$ be a
strictly increasing sequence of natural numbers with $d_0 > 0$, and let
$D = \{d_n : n \in \mathbb{N}\}$. Suppose there are a real number $\delta > 0$ and a natural
number $N \ge 1$ such that $d_{n+1} \ge (3 + \delta) d_n$ for every $n \in \mathbb{N}$ with
$n + 1 \ge N$. Then $D$ is not $2$-accessible.

Source: Oscar Quester, *On Some Properties of Accessible Sets*, INTEGERS 25 (2025), Article A64,
        Corollary 1. -/
public theorem not_two_accessible_of_growth (D : Set ℕ) (d : ℕ → ℕ)
    (hmono : StrictMono d) (hD : D = Set.range d) (hd0 : 0 < d 0)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : 0 < N)
    (hgrowth : ∀ n : ℕ, N ≤ n + 1 →
      (d (n + 1) : ℝ) ≥ (3 + δ) * (d n : ℝ)) :
    ¬ IsRAccessible 2 D := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  let a (n : ℕ) : ℝ := d (m + n)
  have hd (n : ℕ) : 0 < (d n : ℝ) := by
    exact_mod_cast hd0.trans_le (hmono.monotone (Nat.zero_le n))
  let ε : ℝ := δ / (2 * (3 + δ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hwidth : (1 / 2 - ε) * (3 + δ) = 3 / 2 := by
    dsimp [ε]
    field_simp
    ring
  have hpos : 0 < 1 / 2 - ε := by
    apply pos_of_mul_pos_left (b := 3 + δ) _ (by positivity)
    rw [hwidth]
    norm_num
  obtain ⟨α, hα, htail⟩ := not_two_accessible_of_growth.exists_scale a
    (fun n => hd _) hε (by linarith) (fun n => calc
      3 / 2 * a n = (1 / 2 - ε) * ((3 + δ) * a n) := by rw [← mul_assoc, hwidth]
      _ ≤ (1 / 2 - ε) * a (n + 1) :=
        mul_le_mul_of_nonneg_left (hgrowth (m + n) (by omega)) hpos.le)
  have hαpos : 0 < α := (div_pos hε (hd _)).trans_le hα.1
  -- Before the tail starts, all scaled gaps already lie in the first half of the unit interval.
  have hfrac (n : ℕ) : Int.fract (α * (d n : ℝ)) ∈ Set.Icc (min α ε) (1 / 2) := by
    rcases le_total m n with h | h
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      exact ⟨(min_le_right ..).trans (htail j).1, (htail j).2⟩
    · have h₁ : 1 ≤ (d n : ℝ) := by
        exact_mod_cast hd0.trans_le (hmono.monotone (Nat.zero_le n))
      have hlo : α ≤ α * (d n : ℝ) := le_mul_of_one_le_right hαpos.le h₁
      have hhi : α * (d n : ℝ) ≤ 1 / 2 := calc
        _ ≤ α * a 0 := mul_le_mul_of_nonneg_left (by
          dsimp [a]
          exact_mod_cast hmono.monotone h) hαpos.le
        _ ≤ 1 / 2 := (le_div_iff₀ (hd _)).1 hα.2
      rw [Int.fract_eq_self.mpr ⟨hαpos.le.trans hlo, hhi.trans_lt (by norm_num)⟩]
      exact ⟨(min_le_left ..).trans hlo, hhi⟩
  obtain ⟨c, hc⟩ := coloring_avoids_diffsequence_of_fractional_bounds 2 (by decide)
    D d hmono hD hd0 α (min α ε) (lt_min hαpos hε) (by simpa using hfrac)
  exact fun h => hc (h.2.2 c _ (Nat.le_add_left 1 _))

end MetaMathlibExt
