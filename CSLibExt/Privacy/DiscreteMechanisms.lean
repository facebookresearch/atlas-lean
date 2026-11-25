/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DifferentialPrivacy
public import CSLibExt.Crypto.Privacy.Exponential
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

The exponential mechanism reuses `Cslib.Crypto.Privacy`: the `PMF` is built
from `expMechProb`, agrees with `expMechanism` as a measure, and derives
privacy and utility from `expMechanism_differentiallyPrivate` and
`expMechanism_utility`.

Informal sources: Dwork and Roth, *The Algorithmic Foundations of
Differential Privacy* (2014), §3.2 for randomized response, Theorem 3.10
for exponential-mechanism privacy and Theorem 3.11 / Corollary 3.12 for its
utility, and the standard two-sided geometric (discrete Laplace)
distribution of Ghosh, Roughgarden, and Sundararajan (2009).
-/

@[expose] public section

namespace CSLibExt.Privacy.DiscreteMechanisms

open CSLibExt.Privacy.DifferentialPrivacy
open Cslib.Crypto.Privacy
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

/-- The exponential mechanism as a `PMF`, with masses from `expMechProb`
(Dwork and Roth, 2014, Definition 3.4). -/
noncomputable def expMech {R D : Type*} [Fintype R] [Nonempty R]
    (u : D → R → ℝ) (ε Δ : ℝ) (d : D) : PMF R :=
  PMF.ofFintype (fun r => ENNReal.ofReal (expMechProb ε Δ u d r)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun r _ => expMechProb_nonneg ε Δ u d r), sum_expMechProb,
      ENNReal.ofReal_one])

theorem expMech_apply {R D : Type*} [Fintype R] [Nonempty R] (u : D → R → ℝ)
    (ε Δ : ℝ) (d : D) (r : R) :
    expMech u ε Δ d r = expWeight ε Δ (u d r) / expZ (u d) ε Δ := by
  have hZd : 0 < expZReal (u d) ε Δ := expZReal_pos (u d) ε Δ
  show ENNReal.ofReal (expMechProb ε Δ u d r) = _
  rw [show expMechProb ε Δ u d r
      = expScore ε Δ (u d r) / expZReal (u d) ε Δ from rfl,
    ENNReal.ofReal_div_of_pos hZd, ← expZ_eq_ofReal, expWeight]

/-- The `PMF` mechanism agrees with `expMechanism` as a measure. -/
theorem expMech_toMeasure {R D : Type*} [Fintype R] [Nonempty R]
    [MeasurableSpace R] [MeasurableSingletonClass R]
    (u : D → R → ℝ) (ε Δ : ℝ) (d : D) :
    (expMech u ε Δ d).toMeasure = expMechanism ε Δ u d := by
  rw [MeasureTheory.Measure.ext_iff_singleton]
  intro r
  rw [(expMech u ε Δ d).toMeasure_apply_singleton r (measurableSet_singleton r),
    expMechanism_apply]
  have hsum : (∑ s, ({r} : Set R).indicator (expMechProb ε Δ u d) s)
      = expMechProb ε Δ u d r := by
    have h0 : ∀ s ∈ Finset.univ, s ≠ r →
        ({r} : Set R).indicator (expMechProb ε Δ u d) s = 0 := by
      intro s _ hsr
      have hmem : s ∉ ({r} : Set R) := by simpa using hsr
      exact Set.indicator_of_notMem hmem _
    rw [Finset.sum_eq_single r h0 (by simp)]
    exact Set.indicator_of_mem (Set.mem_singleton r) _
  show ENNReal.ofReal (expMechProb ε Δ u d r) = _
  rw [hsum]

/-- The exponential mechanism is `ε`-DP under sensitivity `Δ`
(Dwork and Roth, 2014, Theorem 3.10). -/
theorem isDP_expMech {R D : Type*} [Fintype R] [Nonempty R]
    (u : D → R → ℝ) (ε Δ : ℝ) (hε : 0 ≤ ε) (hΔ : 0 < Δ) (adj : D → D → Prop)
    (hsens : ∀ d d', adj d d' → ∀ r, |u d r - u d' r| ≤ Δ) :
    IsDP (expMech u ε Δ) adj ε := by
  refine ⟨hε, fun d d' hadj r => ?_⟩
  show ENNReal.ofReal (expMechProb ε Δ u d r)
      ≤ ENNReal.ofReal (Real.exp ε) * ENNReal.ofReal (expMechProb ε Δ u d' r)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal
    (expMechProb_le_exp_mul hε hΔ (hsens d d' hadj) r)

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
  have hs : ∀ s, u d s = u d' s := fun s => hconst d d' s
  have hMech : expMech u ε Δ d = expMech u ε Δ d' := by
    unfold expMech
    congr 1
    funext r
    simp only [expMechProb, expMechWeight, hs]
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
optimal have exponentially small probability
(Dwork and Roth, 2014, Corollary 3.12). -/
theorem expMech_utility {R : Type*} [Fintype R] [Nonempty R] {D : Type*}
    (u : D → R → ℝ) (ε Δ : ℝ) (hε : 0 < ε) (hΔ : 0 < Δ) (d : D) (t : ℝ) :
    (expMech u ε Δ d).toOuterMeasure
        {r | u d r ≤ expOPT (u d)
          - (2 * Δ / ε) * (Real.log (Fintype.card R) + t)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  let _ : MeasurableSpace R := ⊤
  have _ : MeasurableSingletonClass R := ⟨fun _ => trivial⟩
  have hOPT : expOPT (u d) = optUtility u d := rfl
  rw [← (expMech u ε Δ d).toMeasure_apply_eq_toOuterMeasure _, expMech_toMeasure,
    hOPT]
  exact expMechanism_utility_card hε hΔ u d t

/-- Sharp utility bound with the optimal-output fraction
(Dwork and Roth, 2014, Theorem 3.11). -/
theorem expMech_utility_opt {R : Type*} [Fintype R] [Nonempty R] {D : Type*}
    (u : D → R → ℝ) (ε Δ : ℝ) (hε : 0 < ε) (hΔ : 0 < Δ) (d : D) (t : ℝ) :
    (expMech u ε Δ d).toOuterMeasure
        {r | u d r ≤ expOPT (u d) - 2 * Δ / ε *
          (Real.log (Fintype.card R / Nat.card {r : R // u d r = expOPT (u d)})
            + t)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  let _ : MeasurableSpace R := ⊤
  have _ : MeasurableSingletonClass R := ⟨fun _ => trivial⟩
  have hOPT : expOPT (u d) = optUtility u d := rfl
  rw [← (expMech u ε Δ d).toMeasure_apply_eq_toOuterMeasure _, expMech_toMeasure,
    hOPT]
  exact expMechanism_utility hε hΔ u d t

end CSLibExt.Privacy.DiscreteMechanisms
