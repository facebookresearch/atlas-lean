/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.Bonding.PairPotentials
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.CondensedMatter.Bonding.PairPotentials`

* Lennard-Jones numeric instance (`ε = 1`, `σ = 1`): `φ(r₀) = -1`, `φ'(r₀) = 0`,
  `φ''(r₀) = 72 / 2 ^ (1/3)`; non-equilibrium check `φ'(1) = -24 ≠ 0`.
* Madelung partial sums `N = 1, 2, 3, 4` exactly (`2`, `1`, `5 / 3`, `7 / 6`);
  sandwich bounds: `N = 4` within `2 / 5` and `N = 20` within `0.1` of `2 * log 2`,
  plus certified `log 2` bounds.
* Bond model numeric instance: `72 / √2`.
* Born-Lande numeric instance and negativity.
* Boundary checks: the Lennard-Jones hypotheses force `r₀ ≠ 0` (derived through
  `lennardJones_eq_at_min`); `madelung_one_dim` is pinned to the limit of the
  ordered partial sums over `Finset.range N`.
-/

@[expose] public section

open scoped Topology

namespace PhyslibExtTest.CondensedMatter.Bonding.PairPotentials

open _root_.PairPotentials

/-! ### Lennard-Jones numeric checks -/

/-- `r₀ = 2 ^ (1/6)` satisfies the radius hypothesis at `σ = 1`. -/
lemma hr0_num : Real.rpow 2 (1 / 6) = Real.rpow 2 (1 / 6) * 1 := (mul_one _).symm

-- Lennard-Jones numeric instance `ε = 1`, `σ = 1`: `φ(r₀) = -1`.
example : 4 * (1 : ℝ) * ((((1 : ℝ)) / Real.rpow 2 (1 / 6)) ^ 12 -
    (((1 : ℝ)) / Real.rpow 2 (1 / 6)) ^ 6) = -1 :=
  lennardJones_eq_at_min 1 1 (Real.rpow 2 (1 / 6)) one_pos one_pos hr0_num

-- Lennard-Jones numeric instance: `φ'(r₀) = 0`.
example : HasDerivAt (fun r => 4 * (1 : ℝ) * ((((1 : ℝ)) / r) ^ 12 - (((1 : ℝ)) / r) ^ 6))
    0 (Real.rpow 2 (1 / 6)) :=
  lennardJones_deriv_at_min 1 1 (Real.rpow 2 (1 / 6)) one_pos one_pos hr0_num

-- Lennard-Jones numeric instance: `φ''(r₀) = 72 / 2 ^ (1/3)`.
example : HasDerivAt (deriv (fun r => 4 * (1 : ℝ) * ((((1 : ℝ)) / r) ^ 12 - (((1 : ℝ)) / r) ^ 6)))
    (72 / Real.rpow 2 (1 / 3)) (Real.rpow 2 (1 / 6)) := by
  have h := lennardJones_second_deriv_at_min 1 1 (Real.rpow 2 (1 / 6)) one_pos one_pos hr0_num
  have hval : (72 * (1 : ℝ) / (Real.rpow 2 (1 / 3) * (1 : ℝ) ^ 2)) =
      72 / Real.rpow 2 (1 / 3) := by
    norm_num
  rw [hval] at h
  exact h

/-- Non-equilibrium check: at `r = 1` (with `ε = σ = 1`) the derivative is `-24`. -/
lemma deriv_lj_at_one :
    deriv (fun r => 4 * (1 : ℝ) * ((((1 : ℝ)) / r) ^ 12 - (((1 : ℝ)) / r) ^ 6)) 1 = -24 := by
  have hbase : HasDerivAt (fun r => (1 : ℝ) / r) ((0 * 1 - 1 * 1) / (1 : ℝ) ^ 2) (1 : ℝ) :=
    (hasDerivAt_const 1 1).div (hasDerivAt_id' 1) (by norm_num)
  have h := ((hbase.pow 12).sub (hbase.pow 6)).const_mul (4 * (1 : ℝ))
  have h2 : HasDerivAt (fun r => 4 * (1 : ℝ) * ((((1 : ℝ)) / r) ^ 12 - (((1 : ℝ)) / r) ^ 6))
      ((4 * (1 : ℝ)) * ((((12 : ℕ) : ℝ) * ((1 : ℝ) / 1) ^ 11 * ((0 * 1 - 1 * 1) / (1 : ℝ) ^ 2)) -
        (((6 : ℕ) : ℝ) * ((1 : ℝ) / 1) ^ 5 * ((0 * 1 - 1 * 1) / (1 : ℝ) ^ 2)))) (1 : ℝ) := h
  have hval : ((4 * (1 : ℝ)) * ((((12 : ℕ) : ℝ) * ((1 : ℝ) / 1) ^ 11 * ((0 * 1 - 1 * 1) / (1 : ℝ) ^ 2)) -
      (((6 : ℕ) : ℝ) * ((1 : ℝ) / 1) ^ 5 * ((0 * 1 - 1 * 1) / (1 : ℝ) ^ 2)))) = -24 := by
    norm_num
  rw [hval] at h2
  exact h2.deriv

example : deriv (fun r => 4 * (1 : ℝ) * ((((1 : ℝ)) / r) ^ 12 - (((1 : ℝ)) / r) ^ 6)) 1 = -24 :=
  deriv_lj_at_one

example : deriv (fun r => 4 * (1 : ℝ) * ((((1 : ℝ)) / r) ^ 12 - (((1 : ℝ)) / r) ^ 6)) 1 ≠ 0 := by
  rw [deriv_lj_at_one]
  norm_num

/-! ### Madelung partial sums and sandwich bounds -/

-- Madelung partial sums `N = 1, 2, 3, 4`, exact rational values (doubled).
example : 2 * (∑ k ∈ Finset.range 1, ((-1 : ℝ) ^ k / (k + 1))) = 2 := by
  rw [Finset.sum_range_one]
  norm_num

example : 2 * (∑ k ∈ Finset.range 2, ((-1 : ℝ) ^ k / (k + 1))) = 1 := by
  have r2 : (2 : ℕ) = 1 + 1 := rfl
  rw [r2, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num

example : 2 * (∑ k ∈ Finset.range 3, ((-1 : ℝ) ^ k / (k + 1))) = 5 / 3 := by
  have h3 : (∑ k ∈ Finset.range 3, ((-1 : ℝ) ^ k / (k + 1))) =
      (∑ k ∈ Finset.range 2, ((-1 : ℝ) ^ k / (k + 1))) + (-1 : ℝ) ^ (2 : ℕ) / (((2 : ℕ) : ℝ) + 1) :=
    Finset.sum_range_succ _ 2
  have h2 : (∑ k ∈ Finset.range 2, ((-1 : ℝ) ^ k / (k + 1))) =
      (∑ k ∈ Finset.range 1, ((-1 : ℝ) ^ k / (k + 1))) + (-1 : ℝ) ^ (1 : ℕ) / (((1 : ℕ) : ℝ) + 1) :=
    Finset.sum_range_succ _ 1
  rw [h3, h2, Finset.sum_range_one]
  norm_num

example : 2 * (∑ k ∈ Finset.range 4, ((-1 : ℝ) ^ k / (k + 1))) = 7 / 6 := by
  have h4 : (∑ k ∈ Finset.range 4, ((-1 : ℝ) ^ k / (k + 1))) =
      (∑ k ∈ Finset.range 3, ((-1 : ℝ) ^ k / (k + 1))) + (-1 : ℝ) ^ (3 : ℕ) / (((3 : ℕ) : ℝ) + 1) :=
    Finset.sum_range_succ _ 3
  have h3 : (∑ k ∈ Finset.range 3, ((-1 : ℝ) ^ k / (k + 1))) =
      (∑ k ∈ Finset.range 2, ((-1 : ℝ) ^ k / (k + 1))) + (-1 : ℝ) ^ (2 : ℕ) / (((2 : ℕ) : ℝ) + 1) :=
    Finset.sum_range_succ _ 2
  have h2 : (∑ k ∈ Finset.range 2, ((-1 : ℝ) ^ k / (k + 1))) =
      (∑ k ∈ Finset.range 1, ((-1 : ℝ) ^ k / (k + 1))) + (-1 : ℝ) ^ (1 : ℕ) / (((1 : ℕ) : ℝ) + 1) :=
    Finset.sum_range_succ _ 1
  rw [h4, h3, h2, Finset.sum_range_one]
  norm_num

/-- Even partial sums of the alternating harmonic series increase. -/
lemma madelung_even_mono :
    Monotone (fun M => ∑ k ∈ Finset.range (2 * M), ((-1 : ℝ) ^ k / (k + 1))) := by
  apply monotone_nat_of_le_succ
  intro M
  have e : 2 * (M + 1) = (2 * M + 1) + 1 := by ring
  rw [e, Finset.sum_range_succ, Finset.sum_range_succ]
  have h_even : (-1 : ℝ) ^ (2 * M) = 1 := by rw [pow_mul]; norm_num
  have h_odd : (-1 : ℝ) ^ (2 * M + 1) = -1 := by rw [pow_succ, h_even]; ring
  rw [h_even, h_odd]
  have hA : (0 : ℝ) < (((2 * M : ℕ)) : ℝ) + 1 := by positivity
  have hAB : ((((2 * M : ℕ)) : ℝ) + 1) ≤ ((((2 * M + 1 : ℕ))) : ℝ) + 1 := by
    have hle : ((2 * M : ℕ) : ℝ) ≤ ((2 * M + 1 : ℕ) : ℝ) := by
      have h : 2 * M ≤ 2 * M + 1 := by omega
      exact_mod_cast h
    linarith
  have hle := one_div_le_one_div_of_le hA hAB
  have hneg : (-1 : ℝ) / (((((2 * M + 1 : ℕ))) : ℝ) + 1) =
      -(1 / (((((2 * M + 1 : ℕ))) : ℝ) + 1)) := by rw [neg_div]
  rw [hneg]
  linarith

/-- Odd partial sums of the alternating harmonic series decrease. -/
lemma madelung_odd_anti :
    Antitone (fun M => ∑ k ∈ Finset.range (2 * M + 1), ((-1 : ℝ) ^ k / (k + 1))) := by
  apply antitone_nat_of_succ_le
  intro M
  have e : 2 * (M + 1) + 1 = (2 * M + 2) + 1 := by ring
  rw [e, Finset.sum_range_succ]
  have e2 : 2 * M + 2 = (2 * M + 1) + 1 := by ring
  rw [e2, Finset.sum_range_succ]
  have h_odd : (-1 : ℝ) ^ (2 * M + 1) = -1 := by
    have h_even : (-1 : ℝ) ^ (2 * M) = 1 := by rw [pow_mul]; norm_num
    rw [pow_succ, h_even]; ring
  have h_even2 : (-1 : ℝ) ^ (2 * M + 2) = 1 := by
    have e3 : 2 * M + 2 = 2 * (M + 1) := by ring
    rw [e3, pow_mul]; norm_num
  rw [h_odd, h_even2]
  have hA : (0 : ℝ) < (((((2 * M + 1 : ℕ))) : ℝ) + 1) := by positivity
  have hAB : ((((((2 * M + 1 : ℕ))) : ℝ) + 1)) ≤ (((((2 * M + 2 : ℕ)))) : ℝ) + 1 := by
    have hle : ((2 * M + 1 : ℕ) : ℝ) ≤ ((2 * M + 2 : ℕ) : ℝ) := by
      have h : 2 * M + 1 ≤ 2 * M + 2 := by omega
      exact_mod_cast h
    linarith
  have hle := one_div_le_one_div_of_le hA hAB
  have hneg : (-1 : ℝ) / (((((2 * M + 1 : ℕ))) : ℝ) + 1) =
      -(1 / (((((2 * M + 1 : ℕ))) : ℝ) + 1)) := by rw [neg_div]
  rw [hneg]
  linarith

lemma h2M_even : Filter.Tendsto (fun M : ℕ => 2 * M) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun M hM => by omega⟩

lemma h2M_odd : Filter.Tendsto (fun M : ℕ => 2 * M + 1) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun M hM => by omega⟩

/-- Doubled even partial sums sit below `2 * log 2`. -/
lemma madelung_two_mul_even_le (M : ℕ) :
    2 * (∑ k ∈ Finset.range (2 * M), ((-1 : ℝ) ^ k / (k + 1))) ≤ 2 * Real.log 2 := by
  have h2sub : Filter.Tendsto
      (fun M : ℕ => 2 * ∑ k ∈ Finset.range (2 * M), ((-1 : ℝ) ^ k / (k + 1)))
      Filter.atTop (𝓝 (2 * Real.log 2)) :=
    madelung_one_dim.comp h2M_even
  have hmono2 : Monotone
      (fun M : ℕ => 2 * ∑ k ∈ Finset.range (2 * M), ((-1 : ℝ) ^ k / (k + 1))) :=
    fun a b hab => by
      have h := madelung_even_mono hab
      linarith
  exact ge_of_tendsto h2sub (Filter.eventually_atTop.mpr ⟨M, fun m hm => hmono2 hm⟩)

/-- Doubled odd partial sums sit above `2 * log 2`. -/
lemma madelung_two_mul_odd_ge (M : ℕ) :
    2 * Real.log 2 ≤ 2 * (∑ k ∈ Finset.range (2 * M + 1), ((-1 : ℝ) ^ k / (k + 1))) := by
  have h2sub : Filter.Tendsto
      (fun M : ℕ => 2 * ∑ k ∈ Finset.range (2 * M + 1), ((-1 : ℝ) ^ k / (k + 1)))
      Filter.atTop (𝓝 (2 * Real.log 2)) :=
    madelung_one_dim.comp h2M_odd
  have hanti2 : Antitone
      (fun M : ℕ => 2 * ∑ k ∈ Finset.range (2 * M + 1), ((-1 : ℝ) ^ k / (k + 1))) :=
    fun a b hab => by
      have h := madelung_odd_anti hab
      linarith
  exact le_of_tendsto h2sub (Filter.eventually_atTop.mpr ⟨M, fun m hm => hanti2 hm⟩)

-- The `N = 4` partial sum is within `2 / 5` of `2 * log 2`.
example : |2 * (∑ k ∈ Finset.range 4, ((-1 : ℝ) ^ k / (k + 1))) - 2 * Real.log 2| ≤ 2 / 5 := by
  have hlo : 2 * (∑ k ∈ Finset.range 4, ((-1 : ℝ) ^ k / (k + 1))) ≤ 2 * Real.log 2 :=
    madelung_two_mul_even_le 2
  have hhi : 2 * Real.log 2 ≤ 2 * (∑ k ∈ Finset.range 5, ((-1 : ℝ) ^ k / (k + 1))) :=
    madelung_two_mul_odd_ge 2
  have hdiff : 2 * (∑ k ∈ Finset.range 5, ((-1 : ℝ) ^ k / (k + 1))) -
      2 * (∑ k ∈ Finset.range 4, ((-1 : ℝ) ^ k / (k + 1))) = 2 / 5 := by
    have e5 : (5 : ℕ) = 4 + 1 := rfl
    have h4 : (-1 : ℝ) ^ (4 : ℕ) = 1 := by norm_num
    rw [e5, Finset.sum_range_succ, h4]
    norm_num
  rw [abs_le]
  constructor <;> linarith

-- The `N = 20` partial sum is within `0.1` of `2 * log 2`.
example : |2 * (∑ k ∈ Finset.range 20, ((-1 : ℝ) ^ k / (k + 1))) - 2 * Real.log 2| < 1 / 10 := by
  have hlo : 2 * (∑ k ∈ Finset.range 20, ((-1 : ℝ) ^ k / (k + 1))) ≤ 2 * Real.log 2 :=
    madelung_two_mul_even_le 10
  have hhi : 2 * Real.log 2 ≤ 2 * (∑ k ∈ Finset.range 21, ((-1 : ℝ) ^ k / (k + 1))) :=
    madelung_two_mul_odd_ge 10
  have hdiff : 2 * (∑ k ∈ Finset.range 21, ((-1 : ℝ) ^ k / (k + 1))) -
      2 * (∑ k ∈ Finset.range 20, ((-1 : ℝ) ^ k / (k + 1))) = 2 / 21 := by
    have e21 : (21 : ℕ) = 20 + 1 := rfl
    have h20 : (-1 : ℝ) ^ (20 : ℕ) = 1 := by norm_num
    rw [e21, Finset.sum_range_succ, h20]
    norm_num
  rw [abs_lt]
  constructor <;> linarith

-- Numerical tie to `log 2` via Mathlib's certified bounds.
example : (7 / 6 : ℝ) < 2 * Real.log 2 := by
  have h := Real.log_two_gt_d9
  linarith

example : 2 * Real.log 2 < (5 / 3 : ℝ) := by
  have h := Real.log_two_lt_d9
  linarith

/-! ### Bond-model and Born-Lande numeric checks -/

-- Bond model numeric instance `ε = 1`, `σ = 1`.
example : bondModulusEstimate (72 / Real.rpow 2 (1 / 3)) (Real.rpow 2 (1 / 6)) =
    72 / Real.sqrt 2 := by
  have h := bondModulusEstimate_lennardJones 1 1 one_pos one_pos
  have e1 : (72 * (1 : ℝ) / (Real.rpow 2 (1 / 3) * (1 : ℝ) ^ 2)) =
      72 / Real.rpow 2 (1 / 3) := by
    norm_num
  have e2 : Real.rpow 2 (1 / 6) * (1 : ℝ) = Real.rpow 2 (1 / 6) := mul_one _
  have e3 : (72 * (1 : ℝ) / (Real.sqrt 2 * (1 : ℝ) ^ 3)) = 72 / Real.sqrt 2 := by
    norm_num
  rw [e1, e2, e3] at h
  exact h

-- Born-Lande numeric instance: all parameters `1` except `n = 2`.
example : bornLandeEnergy 1 1 1 1 1 1 1 2 = -(1 / (4 * Real.pi)) * (1 / 2) := by
  simp only [bornLandeEnergy]
  norm_num

example : bornLandeEnergy 1 1 1 1 1 1 1 2 < 0 :=
  bornLandeEnergy_neg_of_pos 1 1 1 1 1 1 1 2 one_pos one_pos one_pos one_pos one_pos
    one_pos one_pos (by norm_num)

/-! ### Boundary checks -/

-- Boundary check: the Lennard-Jones hypotheses force `r₀ ≠ 0`. If `r₀ = 0`, then
-- `σ / r₀ = 0` and `φ(r₀) = 0`, contradicting `lennardJones_eq_at_min` (`φ(r₀) = -ε < 0`).
example (ε σ r₀ : ℝ) (hε : 0 < ε) (hσ : 0 < σ) (hr₀ : r₀ = Real.rpow 2 (1 / 6) * σ) :
    r₀ ≠ 0 := by
  intro h0
  have h := lennardJones_eq_at_min ε σ r₀ hε hσ hr₀
  rw [h0, div_zero] at h
  norm_num at h
  linarith

-- Boundary check: `madelung_one_dim` is the limit of the ordered partial sums over
-- `Finset.range N`, not a `tsum`; this ascription fails if the statement changes shape.
example : Filter.Tendsto (fun N : ℕ => 2 * ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k / (k + 1))
    Filter.atTop (𝓝 (2 * Real.log 2)) :=
  madelung_one_dim


end PhyslibExtTest.CondensedMatter.Bonding.PairPotentials
