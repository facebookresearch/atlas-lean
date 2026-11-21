/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DifferentialPrivacy
public import Cslib.Probability.PMF
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Basic.ENNReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Discrete differential-privacy mechanisms

Randomized response on a single bit, the exponential mechanism on a finite
type, and the two-sided geometric mechanism on integers, proved against
`CSLibExt.Privacy.DifferentialPrivacy.IsDP` directly.

Informal sources: Dwork and Roth, *The Algorithmic Foundations of
Differential Privacy* (2014), §3.2 for randomized response and Theorem 3.10
for the exponential mechanism (privacy and utility), and the standard
two-sided geometric (discrete Laplace) distribution of Ghosh, Roughgarden,
and Sundararajan (2009).
-/

@[expose] public section

namespace CSLibExt.Privacy.DiscreteMechanisms

open CSLibExt.Privacy.DifferentialPrivacy
open scoped ENNReal

/-! ## M1: randomized response -/

/-- Single-bit adjacency: distinct bits are adjacent. -/
def rrAdj : Bool → Bool → Prop := fun b b' => b ≠ b'

/-- Randomized-response mass: report the input bit with probability `p`. -/
noncomputable def rrMass (p : ℝ) (b o : Bool) : ℝ≥0∞ :=
  if o = b then ENNReal.ofReal p else ENNReal.ofReal (1 - p)

/-- The randomized-response masses sum to one for `p ∈ [0, 1]`. -/
theorem rrMass_sum_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    ∑ o, rrMass p b o = 1 := by
  have h1p : (0 : ℝ) ≤ 1 - p := by linarith
  rw [Fintype.sum_bool]
  cases b
  · simp only [rrMass, Bool.true_eq_false, ite_true, ite_false]
    rw [← ENNReal.ofReal_add h1p hp0, sub_add_cancel, ENNReal.ofReal_one]
  · simp only [rrMass, Bool.false_eq_true, ite_true, ite_false]
    rw [← ENNReal.ofReal_add hp0 h1p, add_sub_cancel, ENNReal.ofReal_one]

/-- Randomized response on a single bit. -/
noncomputable def rrMech (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : PMF Bool :=
  PMF.ofFintype (rrMass p b) (rrMass_sum_one p hp0 hp1 b)

/-- Truthful-report mass. -/
theorem rrMech_apply_self (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    rrMech p hp0 hp1 b b = ENNReal.ofReal p := by
  simp [rrMech, rrMass]

/-- Mislabeled-report mass. -/
theorem rrMech_apply_ne (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b o : Bool)
    (h : o ≠ b) : rrMech p hp0 hp1 b o = ENNReal.ofReal (1 - p) := by
  simp [rrMech, rrMass, h]

/-- Every output equals one of two adjacent bits. -/
theorem rrAdj_cover (b b' o : Bool) (hadj : rrAdj b b') : o = b ∨ o = b' := by
  cases b <;> cases b' <;> cases o <;> simp_all [rrAdj]

/-- Randomized response is `log (p / (1 - p))`-DP for `1 / 2 < p < 1`. -/
theorem isDP_rrMech (p : ℝ) (hp_half : 1 / 2 < p) (hp1 : p < 1) :
    IsDP (rrMech p (by linarith) (by linarith)) rrAdj
      (Real.log (p / (1 - p))) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hpr : (0 : ℝ) < p / (1 - p) := div_pos hp0 h1p
  have hle1 : (1 : ℝ) ≤ p / (1 - p) := by
    rw [le_div_iff₀ h1p]
    linarith
  have hε : (0 : ℝ) ≤ Real.log (p / (1 - p)) := Real.log_nonneg hle1
  have hexp : Real.exp (Real.log (p / (1 - p))) = p / (1 - p) :=
    Real.exp_log hpr
  refine ⟨hε, fun b b' hadj o => ?_⟩
  rcases rrAdj_cover b b' o hadj with rfl | rfl
  · rw [rrMech_apply_self, rrMech_apply_ne _ _ _ _ _ hadj, hexp,
      ← ENNReal.ofReal_mul (le_of_lt hpr)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_mul_cancel₀ _ (ne_of_gt h1p)]
  · rw [rrMech_apply_ne _ _ _ _ _ (Ne.symm hadj), rrMech_apply_self, hexp,
      ← ENNReal.ofReal_mul (le_of_lt hpr)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_mul_eq_mul_div, le_div_iff₀ h1p]
    nlinarith [hp_half]

/-- Randomized response with `p = 1 / 2` is `0`-DP. -/
theorem isDP_rrMech_half :
    IsDP (rrMech (1 / 2) (by norm_num) (by norm_num)) rrAdj 0 := by
  have hmass : ∀ x y : Bool,
      rrMech (1 / 2) (by norm_num) (by norm_num) x y =
        ENNReal.ofReal (1 / 2) := by
    intro x y
    by_cases h : y = x
    · rw [h]
      exact rrMech_apply_self _ _ _ _
    · rw [rrMech_apply_ne _ _ _ _ _ h]
      congr 1
      norm_num
  refine ⟨le_rfl, fun b b' _ o => ?_⟩
  rw [hmass, hmass, Real.exp_zero, ENNReal.ofReal_one, one_mul]

/-! ## M2: exponential mechanism -/

/-- Unnormalized exponential-mechanism score. -/
noncomputable def expScore (ε Δ u : ℝ) : ℝ := Real.exp (ε * u / (2 * Δ))

/-- Unnormalized exponential-mechanism weight. -/
noncomputable def expWeight (ε Δ u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (expScore ε Δ u)

/-- Partition function: total weight. -/
noncomputable def expZ {R : Type*} [Fintype R] (u : R → ℝ) (ε Δ : ℝ) : ℝ≥0∞ :=
  ∑ r, expWeight ε Δ (u r)

/-- Real-valued partition function. -/
noncomputable def expZReal {R : Type*} [Fintype R] (u : R → ℝ) (ε Δ : ℝ) : ℝ :=
  ∑ r, expScore ε Δ (u r)

theorem expScore_pos (ε Δ u : ℝ) : 0 < expScore ε Δ u := Real.exp_pos _

theorem expWeight_pos (ε Δ u : ℝ) : 0 < expWeight ε Δ u :=
  ENNReal.ofReal_pos.mpr (expScore_pos ε Δ u)

theorem expWeight_ne_top (ε Δ u : ℝ) : expWeight ε Δ u ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem expZ_pos {R : Type*} [Fintype R] [Nonempty R] (u : R → ℝ) (ε Δ : ℝ) :
    0 < expZ u ε Δ := by
  obtain ⟨r0⟩ := ‹Nonempty R›
  have h1 : expWeight ε Δ (u r0) ≤ expZ u ε Δ :=
    Finset.single_le_sum (fun r _ => le_of_lt (expWeight_pos ε Δ (u r)))
      (Finset.mem_univ r0)
  exact lt_of_lt_of_le (expWeight_pos ε Δ (u r0)) h1

theorem expZ_ne_zero {R : Type*} [Fintype R] [Nonempty R] (u : R → ℝ) (ε Δ : ℝ) :
    expZ u ε Δ ≠ 0 :=
  ne_of_gt (expZ_pos u ε Δ)

theorem expZ_ne_top {R : Type*} [Fintype R] (u : R → ℝ) (ε Δ : ℝ) :
    expZ u ε Δ ≠ ⊤ := by
  show (∑ r, expWeight ε Δ (u r)) ≠ ⊤
  exact ENNReal.sum_ne_top.mpr fun r _ => expWeight_ne_top ε Δ (u r)

/-- The partition function is the image of the real one. -/
theorem expZ_eq_ofReal {R : Type*} [Fintype R] (u : R → ℝ) (ε Δ : ℝ) :
    expZ u ε Δ = ENNReal.ofReal (expZReal u ε Δ) := by
  unfold expZ expZReal
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun r _ => le_of_lt (expScore_pos ε Δ (u r)))]
  rfl

theorem expZReal_pos {R : Type*} [Fintype R] [Nonempty R] (u : R → ℝ)
    (ε Δ : ℝ) : 0 < expZReal u ε Δ := by
  unfold expZReal
  exact Finset.sum_pos (fun r _ => expScore_pos ε Δ (u r))
    Finset.univ_nonempty

/-- Normalized exponential-mechanism mass: weight over partition sum. -/
noncomputable def expMass {R : Type*} [Fintype R] (u : R → ℝ) (ε Δ : ℝ)
    (r : R) : ℝ≥0∞ :=
  expWeight ε Δ (u r) / expZ u ε Δ

theorem expMass_sum_one {R : Type*} [Fintype R] [Nonempty R] (u : R → ℝ)
    (ε Δ : ℝ) : ∑ r, expMass u ε Δ r = 1 := by
  simp_rw [expMass, div_eq_mul_inv, ← Finset.sum_mul]
  exact ENNReal.mul_inv_cancel (expZ_ne_zero u ε Δ) (expZ_ne_top u ε Δ)

/-- The exponential mechanism. -/
noncomputable def expMech {R D : Type*} [Fintype R] [Nonempty R]
    (u : D → R → ℝ) (ε Δ : ℝ) (d : D) : PMF R :=
  PMF.ofFintype (expMass (u d) ε Δ) (expMass_sum_one (u d) ε Δ)

theorem expMech_apply {R D : Type*} [Fintype R] [Nonempty R] (u : D → R → ℝ)
    (ε Δ : ℝ) (d : D) (r : R) :
    expMech u ε Δ d r = expWeight ε Δ (u d r) / expZ (u d) ε Δ := rfl

/-- One-sided score ratio from a one-sided utility bound. -/
theorem expScore_le_mul (ε Δ : ℝ) (hε : 0 ≤ ε) (hΔ : 0 < Δ) (a b : ℝ)
    (h : a - b ≤ Δ) :
    expScore ε Δ a ≤ Real.exp (ε / 2) * expScore ε Δ b := by
  have h2Δ : (0 : ℝ) < 2 * Δ := by linarith
  have hle : ε * (a - b) / (2 * Δ) ≤ ε / 2 := by
    rw [div_le_iff₀ h2Δ]
    calc ε * (a - b) ≤ ε * Δ := mul_le_mul_of_nonneg_left h hε
      _ = ε / 2 * (2 * Δ) := by ring
  have hdiff : ε * a / (2 * Δ) - ε * b / (2 * Δ)
      = ε * (a - b) / (2 * Δ) := by
    rw [← sub_div]
    congr 1
    ring
  have h3 : ε * a / (2 * Δ) ≤ ε / 2 + ε * b / (2 * Δ) := by
    linarith [hdiff, hle]
  unfold expScore
  calc Real.exp (ε * a / (2 * Δ))
      ≤ Real.exp (ε / 2 + ε * b / (2 * Δ)) := Real.exp_le_exp.mpr h3
    _ = Real.exp (ε / 2) * Real.exp (ε * b / (2 * Δ)) := Real.exp_add _ _

/-- One-sided partition-function ratio from sensitivity. -/
theorem expZReal_le_mul {R : Type*} [Fintype R] [Nonempty R] {D : Type*}
    (u : D → R → ℝ) (ε Δ : ℝ) (hε : 0 ≤ ε) (hΔ : 0 < Δ) (d d' : D)
    (hsens : ∀ r, u d' r - u d r ≤ Δ) :
    expZReal (u d') ε Δ ≤ Real.exp (ε / 2) * expZReal (u d) ε Δ := by
  unfold expZReal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  exact expScore_le_mul ε Δ hε hΔ (u d' r) (u d r) (hsens r)

/-- The exponential mechanism is `ε`-DP under sensitivity `Δ`. -/
theorem isDP_expMech {R D : Type*} [Fintype R] [Nonempty R] (u : D → R → ℝ)
    (ε Δ : ℝ) (hε : 0 ≤ ε) (hΔ : 0 < Δ) (adj : D → D → Prop)
    (hsens : ∀ d d', adj d d' → ∀ r, |u d r - u d' r| ≤ Δ) :
    IsDP (expMech u ε Δ) adj ε := by
  refine ⟨hε, fun d d' hadj r => ?_⟩
  have hs1 : ∀ s, u d s - u d' s ≤ Δ :=
    fun s => le_of_abs_le (hsens d d' hadj s)
  have hs2 : ∀ s, u d' s - u d s ≤ Δ := fun s => by
    have h := neg_le_of_abs_le (hsens d d' hadj s)
    linarith [h]
  have hw : expScore ε Δ (u d r)
      ≤ Real.exp (ε / 2) * expScore ε Δ (u d' r) :=
    expScore_le_mul ε Δ hε hΔ _ _ (hs1 r)
  have hZ : expZReal (u d') ε Δ
      ≤ Real.exp (ε / 2) * expZReal (u d) ε Δ :=
    expZReal_le_mul u ε Δ hε hΔ d d' hs2
  have hZd : 0 < expZReal (u d) ε Δ := expZReal_pos (u d) ε Δ
  have hZd' : 0 < expZReal (u d') ε Δ := expZReal_pos (u d') ε Δ
  have hw' : 0 < expScore ε Δ (u d' r) := expScore_pos ε Δ (u d' r)
  have hE : 0 < Real.exp (ε / 2) := Real.exp_pos _
  have hmul : expScore ε Δ (u d r) * expZReal (u d') ε Δ ≤
      (Real.exp ε * expScore ε Δ (u d' r)) * expZReal (u d) ε Δ := by
    have hEE : Real.exp (ε / 2) * Real.exp (ε / 2) = Real.exp ε := by
      rw [← Real.exp_add, add_halves]
    calc expScore ε Δ (u d r) * expZReal (u d') ε Δ
        ≤ (Real.exp (ε / 2) * expScore ε Δ (u d' r)) *
            (Real.exp (ε / 2) * expZReal (u d) ε Δ) :=
          mul_le_mul hw hZ (le_of_lt hZd')
            (mul_nonneg (le_of_lt hE) (le_of_lt hw'))
      _ = (Real.exp ε * expScore ε Δ (u d' r)) * expZReal (u d) ε Δ := by
          have hrw : (Real.exp (ε / 2) * expScore ε Δ (u d' r)) *
              (Real.exp (ε / 2) * expZReal (u d) ε Δ)
              = (Real.exp (ε / 2) * Real.exp (ε / 2)) *
                (expScore ε Δ (u d' r) * expZReal (u d) ε Δ) := by ring
          rw [hrw, hEE]
          ring
  have hreal : expScore ε Δ (u d r) / expZReal (u d) ε Δ ≤
      Real.exp ε * (expScore ε Δ (u d' r) / expZReal (u d') ε Δ) := by
    rw [← mul_div_assoc, div_le_iff₀ hZd, div_mul_eq_mul_div,
      le_div_iff₀ hZd']
    exact hmul
  show expMech u ε Δ d r
      ≤ ENNReal.ofReal (Real.exp ε) * expMech u ε Δ d' r
  simp only [expMech_apply, expWeight, expZ_eq_ofReal]
  rw [← ENNReal.ofReal_div_of_pos hZd, ← ENNReal.ofReal_div_of_pos hZd',
    ← ENNReal.ofReal_mul (Real.exp_pos ε).le]
  exact ENNReal.ofReal_le_ofReal hreal

/-- With zero budget the exponential mechanism is uniform. -/
theorem expMech_eps_zero {R : Type*} [Fintype R] [Nonempty R] {D : Type*}
    (u : D → R → ℝ) (Δ : ℝ) (d : D) :
    expMech u 0 Δ d = Cslib.Probability.PMF.uniformOfFintype R := by
  have hw : ∀ s, expWeight (0 : ℝ) Δ (u d s) = 1 := by
    intro s
    simp only [expWeight, expScore, zero_mul, zero_div, Real.exp_zero,
      ENNReal.ofReal_one]
  have hZ : expZ (u d) 0 Δ = (Fintype.card R : ℝ≥0∞) := by
    show (∑ s, expWeight 0 Δ (u d s)) = _
    simp_rw [hw]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ext r
  rw [expMech_apply, Cslib.Probability.PMF.uniformOfFintype_apply, hw r, hZ,
    one_div]

/-! ## M5: database-independent utility -/

/-- A database-independent utility gives a fixed output distribution, hence
`0`-DP. The fixed PMF is uniform only under further assumptions (`ε = 0`
or utility constant across outputs); no uniformity is claimed here. -/
theorem isDP_expMech_const_utility {R D : Type*} [Fintype R] [Nonempty R]
    (u : D → R → ℝ) (ε Δ : ℝ) (adj : D → D → Prop)
    (hconst : ∀ d d' r, u d r = u d' r) :
    IsDP (expMech u ε Δ) adj 0 := by
  refine ⟨le_rfl, fun d d' _ r => ?_⟩
  have hud : u d = u d' := funext fun s => hconst d d' s
  have hMech : expMech u ε Δ d = expMech u ε Δ d' := by
    unfold expMech
    simp only [hud]
  show expMech u ε Δ d r
      ≤ ENNReal.ofReal (Real.exp 0) * expMech u ε Δ d' r
  simp [hMech, Real.exp_zero]

/-! ## M4: two-sided geometric mechanism -/

/-- Geometric decay rate from the privacy budget. -/
noncomputable def geomAlpha (ε : ℝ) : ℝ := Real.exp (-ε)

/-- Unnormalized two-sided geometric mass. -/
noncomputable def geomUnnorm (ρ : ℝ≥0∞) (z : ℤ) : ℝ≥0∞ := ρ ^ z.natAbs

/-- Total unnormalized mass of the two-sided geometric. -/
theorem geomUnnorm_tsum (ρ : ℝ≥0∞) :
    ∑' z : ℤ, geomUnnorm ρ z = (1 - ρ)⁻¹ + ρ * (1 - ρ)⁻¹ := by
  have hnat : ∀ n : ℕ, ((-((n : ℤ) + 1))).natAbs = n + 1 := by
    intro n
    rw [Int.natAbs_neg, ← Nat.cast_one, ← Nat.cast_add, Int.natAbs_natCast]
  have hsplit : ∑' z : ℤ, geomUnnorm ρ z
      = (∑' n : ℕ, geomUnnorm ρ (n : ℤ))
        + ∑' n : ℕ, geomUnnorm ρ (-((n : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable
  have h1 : (∑' n : ℕ, geomUnnorm ρ (n : ℤ)) = (1 - ρ)⁻¹ := by
    simp_rw [geomUnnorm, Int.natAbs_natCast]
    exact ENNReal.tsum_geometric ρ
  have h2 : (∑' n : ℕ, geomUnnorm ρ (-((n : ℤ) + 1))) = ρ * (1 - ρ)⁻¹ := by
    simp_rw [geomUnnorm, hnat]
    exact ENNReal.tsum_geometric_add_one ρ
  rw [hsplit, h1, h2]

theorem geomUnnorm_tsum_ne_zero (ρ : ℝ≥0∞) (_hρ0 : 0 < ρ) (_hρ1 : ρ < 1) :
    ∑' z : ℤ, geomUnnorm ρ z ≠ 0 := by
  rw [geomUnnorm_tsum]
  have hsub : (1 : ℝ≥0∞) - ρ ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top)
  have hpos : (0 : ℝ≥0∞) < (1 - ρ)⁻¹ := ENNReal.inv_pos.mpr hsub
  have hle : (1 - ρ)⁻¹ ≤ (1 - ρ)⁻¹ + ρ * (1 - ρ)⁻¹ :=
    le_add_right le_rfl
  exact ne_of_gt (lt_of_lt_of_le hpos hle)

theorem geomUnnorm_tsum_ne_top (ρ : ℝ≥0∞) (_hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∑' z : ℤ, geomUnnorm ρ z ≠ ⊤ := by
  rw [geomUnnorm_tsum]
  have hpos : (0 : ℝ≥0∞) < 1 - ρ :=
    tsub_pos_iff_not_le.mpr (not_le.mpr hρ1)
  have hX : (1 - ρ)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ne_of_gt hpos)
  have hρtop : ρ ≠ ⊤ := ne_of_lt (lt_trans hρ1 ENNReal.one_lt_top)
  exact ENNReal.add_ne_top.mpr ⟨hX, ENNReal.mul_ne_top hρtop hX⟩

/-- Normalized mass coefficient `(1 - ρ) / (1 + ρ)`. -/
theorem geomUnnorm_inv_tsum (ρ : ℝ≥0∞) (_hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∑' z : ℤ, geomUnnorm ρ z)⁻¹ = (1 - ρ) / (1 + ρ) := by
  have hpos : (0 : ℝ≥0∞) < 1 - ρ :=
    tsub_pos_iff_not_le.mpr (not_le.mpr hρ1)
  have hρtop : ρ ≠ ⊤ := ne_of_lt (lt_trans hρ1 ENNReal.one_lt_top)
  have hplus0 : (1 : ℝ≥0∞) + ρ ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_add_right le_rfl))
  have hplustop : (1 : ℝ≥0∞) + ρ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ne_of_lt ENNReal.one_lt_top, hρtop⟩
  rw [geomUnnorm_tsum,
    show (1 - ρ)⁻¹ + ρ * (1 - ρ)⁻¹ = (1 + ρ) * (1 - ρ)⁻¹ by
      rw [add_mul, one_mul],
    ENNReal.mul_inv (Or.inl hplus0) (Or.inl hplustop),
    inv_inv, ENNReal.div_eq_inv_mul]

/-- Shifting the center does not change the total mass. -/
theorem geomUnnorm_tsum_shift (ρ : ℝ≥0∞) (μ : ℤ) :
    ∑' o : ℤ, geomUnnorm ρ (o - μ) = ∑' z : ℤ, geomUnnorm ρ z := by
  have htsum := Equiv.tsum_eq (Equiv.addRight (-μ)) (geomUnnorm ρ)
  rw [← htsum]
  apply tsum_congr
  intro o
  show geomUnnorm ρ (o - μ) = geomUnnorm ρ (o + -μ)
  simp only [sub_eq_add_neg]

theorem geomUnnorm_tsum_shift_ne_zero (ρ : ℝ≥0∞) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (μ : ℤ) : ∑' o : ℤ, geomUnnorm ρ (o - μ) ≠ 0 := by
  rw [geomUnnorm_tsum_shift]
  exact geomUnnorm_tsum_ne_zero ρ hρ0 hρ1

theorem geomUnnorm_tsum_shift_ne_top (ρ : ℝ≥0∞) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (μ : ℤ) : ∑' o : ℤ, geomUnnorm ρ (o - μ) ≠ ⊤ := by
  rw [geomUnnorm_tsum_shift]
  exact geomUnnorm_tsum_ne_top ρ hρ0 hρ1

theorem geomAlpha_pos (ε : ℝ) : 0 < geomAlpha ε := Real.exp_pos _

theorem geomAlpha_lt_one (ε : ℝ) (hε : 0 < ε) : geomAlpha ε < 1 := by
  unfold geomAlpha
  rw [Real.exp_lt_one_iff]
  linarith

theorem geomRho_pos (ε : ℝ) : 0 < ENNReal.ofReal (geomAlpha ε) :=
  ENNReal.ofReal_pos.mpr (geomAlpha_pos ε)

theorem geomRho_lt_one (ε : ℝ) (hε : 0 < ε) :
    ENNReal.ofReal (geomAlpha ε) < 1 := by
  rw [← ENNReal.ofReal_one,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)]
  exact geomAlpha_lt_one ε hε

/-- The privacy factor is the inverse decay rate. -/
theorem geomExp_eq_inv (ε : ℝ) :
    ENNReal.ofReal (Real.exp ε) = (ENNReal.ofReal (geomAlpha ε))⁻¹ := by
  have hα : (Real.exp (-ε))⁻¹ = Real.exp ε := by
    rw [Real.exp_neg, inv_inv]
  have h := ENNReal.ofReal_inv_of_pos (Real.exp_pos (-ε))
  unfold geomAlpha
  rw [← h, hα]

/-- Absolute-value sensitivity gives a `natAbs` bound. -/
theorem natAbs_le_one_of_abs_le (x : ℤ) (h : |x| ≤ 1) : x.natAbs ≤ 1 := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have h3 : x = -1 ∨ x = 0 ∨ x = 1 := by omega
  rcases h3 with rfl | rfl | rfl <;> decide

/-- Two-sided geometric mechanism: report `f d` plus geometric noise. -/
noncomputable def geomMech {D : Type*} (f : D → ℤ) (ε : ℝ) (hε : 0 < ε)
    (d : D) : PMF ℤ :=
  PMF.normalize (fun o => geomUnnorm (ENNReal.ofReal (geomAlpha ε)) (o - f d))
    (geomUnnorm_tsum_shift_ne_zero _ (geomRho_pos ε) (geomRho_lt_one ε hε)
      (f d))
    (geomUnnorm_tsum_shift_ne_top _ (geomRho_pos ε) (geomRho_lt_one ε hε)
      (f d))

theorem geomMech_apply {D : Type*} (f : D → ℤ) (ε : ℝ) (hε : 0 < ε) (d : D)
    (o : ℤ) : geomMech f ε hε d o
      = geomUnnorm (ENNReal.ofReal (geomAlpha ε)) (o - f d)
        * (∑' z, geomUnnorm (ENNReal.ofReal (geomAlpha ε)) z)⁻¹ := by
  unfold geomMech
  rw [PMF.normalize_apply, geomUnnorm_tsum_shift]

/-- The two-sided geometric mechanism is `ε`-DP under sensitivity one. -/
theorem isDP_geomMech {D : Type*} (f : D → ℤ) (ε : ℝ) (hε : 0 < ε)
    (adj : D → D → Prop)
    (hsens : ∀ d d', adj d d' → |f d - f d'| ≤ 1) :
    IsDP (geomMech f ε hε) adj ε := by
  have hρ0 : (0 : ℝ≥0∞) < ENNReal.ofReal (geomAlpha ε) := geomRho_pos ε
  have hρ1 : ENNReal.ofReal (geomAlpha ε) < 1 := geomRho_lt_one ε hε
  have hρtop : ENNReal.ofReal (geomAlpha ε) ≠ ⊤ :=
    ne_of_lt (lt_trans hρ1 ENNReal.one_lt_top)
  have hρinv : ENNReal.ofReal (geomAlpha ε)
        * (ENNReal.ofReal (geomAlpha ε))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (ne_of_gt hρ0) hρtop
  refine ⟨le_of_lt hε, fun d d' hadj o => ?_⟩
  have hsens1 : (f d - f d').natAbs ≤ 1 :=
    natAbs_le_one_of_abs_le _ (hsens d d' hadj)
  have hnm : (o - f d').natAbs ≤ (o - f d).natAbs + 1 := by
    have htri := Int.natAbs_add_le (o - f d) (f d - f d')
    rw [show (o - f d) + (f d - f d') = o - f d' by ring] at htri
    omega
  have hle : (ENNReal.ofReal (geomAlpha ε)) ^ ((o - f d).natAbs + 1)
      ≤ (ENNReal.ofReal (geomAlpha ε)) ^ (o - f d').natAbs := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnm
    rw [hk, pow_add]
    calc (ENNReal.ofReal (geomAlpha ε)) ^ (o - f d').natAbs
          * (ENNReal.ofReal (geomAlpha ε)) ^ k
        ≤ (ENNReal.ofReal (geomAlpha ε)) ^ (o - f d').natAbs * 1 :=
          mul_le_mul_right (pow_le_one₀ hρ0.le hρ1.le) _
      _ = (ENNReal.ofReal (geomAlpha ε)) ^ (o - f d').natAbs := mul_one _
  have hpow : geomUnnorm (ENNReal.ofReal (geomAlpha ε)) (o - f d)
      ≤ (ENNReal.ofReal (geomAlpha ε))⁻¹
        * geomUnnorm (ENNReal.ofReal (geomAlpha ε)) (o - f d') := by
    show (ENNReal.ofReal (geomAlpha ε)) ^ (o - f d).natAbs ≤ _
    calc (ENNReal.ofReal (geomAlpha ε)) ^ (o - f d).natAbs
        = (ENNReal.ofReal (geomAlpha ε)) ^ (o - f d).natAbs
          * (ENNReal.ofReal (geomAlpha ε)
            * (ENNReal.ofReal (geomAlpha ε))⁻¹) := by rw [hρinv, mul_one]
      _ = (ENNReal.ofReal (geomAlpha ε)) ^ ((o - f d).natAbs + 1)
          * (ENNReal.ofReal (geomAlpha ε))⁻¹ := by rw [pow_succ, mul_assoc]
      _ ≤ (ENNReal.ofReal (geomAlpha ε)) ^ (o - f d').natAbs
          * (ENNReal.ofReal (geomAlpha ε))⁻¹ := mul_le_mul_left hle _
      _ = (ENNReal.ofReal (geomAlpha ε))⁻¹
          * (ENNReal.ofReal (geomAlpha ε)) ^ (o - f d').natAbs :=
          mul_comm _ _
  show geomMech f ε hε d o
      ≤ ENNReal.ofReal (Real.exp ε) * geomMech f ε hε d' o
  rw [geomMech_apply, geomMech_apply, geomExp_eq_inv, ← mul_assoc]
  exact mul_le_mul_left hpow _

/-! ## M3: exponential-mechanism utility -/

/-- Optimal utility value over a finite type. -/
noncomputable def expOPT {R : Type*} [Fintype R] [Nonempty R] (u : R → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty u

/-- Exponential-mechanism utility bound: outputs scoring much worse than
optimal have exponentially small probability. -/
theorem expMech_utility {R : Type*} [Fintype R] [Nonempty R] {D : Type*}
    (u : D → R → ℝ) (ε Δ : ℝ) (hε : 0 < ε) (hΔ : 0 < Δ) (d : D) (t : ℝ) :
    (expMech u ε Δ d).toOuterMeasure
        {r | u d r ≤ expOPT (u d)
          - (2 * Δ / ε) * (Real.log (Fintype.card R) + t)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  classical
  set N : ℝ := (Fintype.card R : ℝ) with hNdef
  set L : ℝ := Real.log N + t with hLdef
  set S : Set R :=
    {r | u d r ≤ expOPT (u d) - (2 * Δ / ε) * L} with hSdef
  have hcard_pos : 0 < Fintype.card R :=
    Fintype.card_pos_iff.mpr ‹Nonempty R›
  have hNpos : 0 < N := by
    rw [hNdef]
    exact Nat.cast_pos.mpr hcard_pos
  have hZd : 0 < expZReal (u d) ε Δ := expZReal_pos (u d) ε Δ
  obtain ⟨rstar, -, hstar⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (u d)
  have hOPT : expOPT (u d) = u d rstar := hstar
  have hwOPT_le : expScore ε Δ (expOPT (u d)) ≤ expZReal (u d) ε Δ := by
    rw [hOPT]
    unfold expZReal
    exact Finset.single_le_sum
      (fun r _ => le_of_lt (expScore_pos ε Δ (u d r)))
      (Finset.mem_univ rstar)
  have hscore_of : ∀ r : R, u d r ≤ expOPT (u d) - (2 * Δ / ε) * L →
      expScore ε Δ (u d r)
        ≤ expScore ε Δ (expOPT (u d)) * Real.exp (-L) := by
    intro r hr
    have hexp_id : ε * (expOPT (u d) - (2 * Δ / ε) * L) / (2 * Δ)
        = ε * expOPT (u d) / (2 * Δ) - L := by
      have hε0 : ε ≠ 0 := ne_of_gt hε
      have hΔ0 : (2 : ℝ) * Δ ≠ 0 :=
        mul_ne_zero (by norm_num) (ne_of_gt hΔ)
      field_simp
    have h1 : ε * u d r ≤ ε * (expOPT (u d) - (2 * Δ / ε) * L) :=
      mul_le_mul_of_nonneg_left hr (le_of_lt hε)
    have h2Δ : (0 : ℝ) < 2 * Δ := by linarith
    have h2 : ε * u d r / (2 * Δ)
        ≤ ε * (expOPT (u d) - (2 * Δ / ε) * L) / (2 * Δ) := by
      rw [div_le_iff₀ h2Δ, div_mul_cancel₀ _ (ne_of_gt h2Δ)]
      exact h1
    have hmono : ε * u d r / (2 * Δ)
        ≤ ε * expOPT (u d) / (2 * Δ) - L := by
      rw [hexp_id] at h2
      exact h2
    have h3 : ε * u d r / (2 * Δ)
        ≤ ε * expOPT (u d) / (2 * Δ) + -L := by
      linarith [hmono]
    unfold expScore
    calc Real.exp (ε * u d r / (2 * Δ))
        ≤ Real.exp (ε * expOPT (u d) / (2 * Δ) + -L) :=
          Real.exp_le_exp.mpr h3
      _ = Real.exp (ε * expOPT (u d) / (2 * Δ)) * Real.exp (-L) :=
          Real.exp_add _ _
  have hE : N * Real.exp (-L) = Real.exp (-t) := by
    have hN0 : N ≠ 0 := ne_of_gt hNpos
    have hexplog : Real.exp (Real.log N) = N := Real.exp_log hNpos
    rw [hLdef, show -(Real.log N + t) = -Real.log N + -t by ring,
      Real.exp_add, Real.exp_neg, hexplog, ← mul_assoc,
      mul_inv_cancel₀ hN0, one_mul]
  have hF0 : ∀ b ∉ Finset.univ.filter (· ∈ S),
      S.indicator ⇑(expMech u ε Δ d) b = 0 := by
    intro b hb
    refine Set.indicator_of_notMem ?_ _
    intro hmem
    exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hmem⟩)
  have hmeas : (expMech u ε Δ d).toOuterMeasure S
      = ∑ r ∈ Finset.univ.filter (· ∈ S), expMech u ε Δ d r := by
    rw [PMF.toOuterMeasure_apply, tsum_eq_sum (s := _) hF0]
    apply Finset.sum_congr rfl
    intro r hr
    exact Set.indicator_of_mem (Finset.mem_filter.mp hr).2 _
  have hsum : ∑ r ∈ Finset.univ.filter (· ∈ S), expMech u ε Δ d r
      = ENNReal.ofReal
        ((∑ r ∈ Finset.univ.filter (· ∈ S), expScore ε Δ (u d r))
          / expZReal (u d) ε Δ) := by
    simp_rw [expMech_apply, expWeight, expZ_eq_ofReal,
      ← ENNReal.ofReal_div_of_pos hZd]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ =>
      div_nonneg (le_of_lt (expScore_pos ε Δ (u d r))) (le_of_lt hZd)),
      Finset.sum_div]
  have hcard : ((Finset.univ.filter (· ∈ S)).card : ℝ) ≤ N := by
    rw [hNdef]
    exact Nat.cast_le.mpr (le_trans
      (Finset.card_le_card (Finset.filter_subset _ _))
      (le_of_eq Finset.card_univ))
  have hsum_le : (∑ r ∈ Finset.univ.filter (· ∈ S), expScore ε Δ (u d r))
      ≤ ((Finset.univ.filter (· ∈ S)).card : ℝ)
        * (expScore ε Δ (expOPT (u d)) * Real.exp (-L)) := by
    calc (∑ r ∈ Finset.univ.filter (· ∈ S), expScore ε Δ (u d r))
        ≤ ∑ r ∈ Finset.univ.filter (· ∈ S),
            (expScore ε Δ (expOPT (u d)) * Real.exp (-L)) := by
          apply Finset.sum_le_sum
          intro r hr
          have hrS : u d r ≤ expOPT (u d) - (2 * Δ / ε) * L :=
            (Finset.mem_filter.mp hr).2
          exact hscore_of r hrS
      _ = ((Finset.univ.filter (· ∈ S)).card : ℝ)
          * (expScore ε Δ (expOPT (u d)) * Real.exp (-L)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hfinal : (∑ r ∈ Finset.univ.filter (· ∈ S), expScore ε Δ (u d r))
      ≤ Real.exp (-t) * expZReal (u d) ε Δ := by
    calc (∑ r ∈ Finset.univ.filter (· ∈ S), expScore ε Δ (u d r))
        ≤ ((Finset.univ.filter (· ∈ S)).card : ℝ)
          * (expScore ε Δ (expOPT (u d)) * Real.exp (-L)) := hsum_le
      _ ≤ N * (expScore ε Δ (expOPT (u d)) * Real.exp (-L)) :=
          mul_le_mul_of_nonneg_right hcard
            (mul_nonneg (le_of_lt (expScore_pos ε Δ (expOPT (u d))))
              (Real.exp_pos _).le)
      _ = expScore ε Δ (expOPT (u d)) * (N * Real.exp (-L)) := by ring
      _ = expScore ε Δ (expOPT (u d)) * Real.exp (-t) := by rw [hE]
      _ ≤ expZReal (u d) ε Δ * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hwOPT_le (Real.exp_pos _).le
      _ = Real.exp (-t) * expZReal (u d) ε Δ := mul_comm _ _
  rw [hmeas, hsum]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ hZd]
  exact hfinal

end CSLibExt.Privacy.DiscreteMechanisms
