/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Renewal.ScoreLadder
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Tests for the discrete key renewal theorem and the score-walk ladder limit

* A two-point interarrival law `f 1 = f 2 = 1/2` (gcd `1`, mean `3/2`): the renewal
  sequence starts `1, 1/2, 3/4` and converges to `2/3`.
* A forcing applied through `tendsto_of_isRenewalSolution`.
* Boundary (lattice): the law `δ₂` has gcd `2`; its renewal sequence alternates `1, 0`
  and does not converge, so the aperiodicity hypothesis cannot be dropped.
* A skip-free-up score walk: ladder law `g = (1/4) δ₁`, Cramér root `θ = log 4`; the
  maximum has `P(M > k) = 4^{-(k+1)}`, and `tendsto_exp_mul_maxTail` returns the exact
  constant `1/4`.
* Boundary (nonnegative drift): a proper ladder law has no positive Cramér root.
* Boundary (missing exponential moment): the ladder law `g k = 1 / (2 k (k + 1))` has
  `∑ g k e^{θ k} = ∞` for every `θ > 0`, so no Cramér root exists.
-/

@[expose] public section

open Filter Topology Finset
open MathlibExt.Probability.Renewal

namespace MathlibExtTest.Probability.Renewal.ScoreLadder

/-! ### Erdős–Feller–Pollard on a two-point law -/

/-- The two-point interarrival law `f 1 = f 2 = 1/2`. -/
noncomputable def twoPoint (k : ℕ) : ℝ := if k = 1 ∨ k = 2 then 1 / 2 else 0

lemma twoPoint_hasSum : HasSum twoPoint 1 := by
  have h : HasSum twoPoint (∑ b ∈ ({1, 2} : Finset ℕ), twoPoint b) :=
      hasSum_sum_of_ne_finset_zero fun k hk => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    simp [twoPoint, hk]
  convert h using 1
  norm_num [twoPoint]

lemma twoPoint_mean : HasSum (fun k : ℕ => (k : ℝ) * twoPoint k) (3 / 2) := by
  have h : HasSum (fun k : ℕ => (k : ℝ) * twoPoint k)
      (∑ b ∈ ({1, 2} : Finset ℕ), (b : ℝ) * twoPoint b) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp [twoPoint, hk]
  convert h using 1
  norm_num [twoPoint]

lemma twoPoint_aper : Nat.setGcd {k | 0 < twoPoint k} = 1 :=
  Nat.dvd_one.1 (Nat.setGcd_dvd_of_mem (show 0 < twoPoint 1 by norm_num [twoPoint]))

lemma twoPoint_nonneg (k : ℕ) : 0 ≤ twoPoint k := by
  unfold twoPoint; split_ifs <;> norm_num

/-- The first values are `u 1 = 1/2`, `u 2 = 3/4`: the sequence genuinely oscillates. -/
example : renewalSeq twoPoint 1 = 1 / 2 ∧ renewalSeq twoPoint 2 = 3 / 4 := by
  constructor
  · rw [renewalSeq_succ]; norm_num [twoPoint]
  · have h1 : renewalSeq twoPoint 1 = 1 / 2 := by rw [renewalSeq_succ]; norm_num [twoPoint]
    rw [renewalSeq_succ]
    norm_num [Finset.sum_range_succ, twoPoint, h1]

/-- Erdős–Feller–Pollard: `u n → 1 / (3/2) = 2/3`. -/
example : Tendsto (renewalSeq twoPoint) atTop (𝓝 (2 / 3)) := by
  have h := tendsto_renewalSeq (by simp [twoPoint]) twoPoint_nonneg twoPoint_hasSum
    twoPoint_aper twoPoint_mean
  norm_num at h
  exact h

/-- Key renewal theorem with the forcing `z = δ₀ + δ₁`: the solution tends to `2 / (3/2)`. -/
example {Z : ℕ → ℝ}
    (hZ : IsRenewalSolution twoPoint (fun n => if n ≤ 1 then 1 else 0) Z) :
    Tendsto Z atTop (𝓝 (4 / 3)) := by
  have hz : HasSum (fun n : ℕ => if n ≤ 1 then (1 : ℝ) else 0) 2 := by
    have h : HasSum (fun n : ℕ => if n ≤ 1 then (1 : ℝ) else 0)
        (∑ b ∈ range 2, if b ≤ 1 then (1 : ℝ) else 0) :=
      hasSum_sum_of_ne_finset_zero fun k hk => by
        simp only [Finset.mem_range, not_lt] at hk
        simp [show ¬ k ≤ 1 by omega]
    convert h using 1
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  have h := tendsto_of_isRenewalSolution (by simp [twoPoint]) twoPoint_nonneg twoPoint_hasSum
    twoPoint_aper twoPoint_mean hz.summable hZ
  rw [hz.tsum_eq] at h
  norm_num at h
  exact h

/-! ### Boundary: the lattice law `δ₂` -/

/-- Unit mass at `2`. -/
noncomputable def deltaTwo (k : ℕ) : ℝ := if k = 2 then 1 else 0

lemma deltaTwo_setGcd : Nat.setGcd {k | 0 < deltaTwo k} = 2 := by
  have hset : {k | 0 < deltaTwo k} = {2} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, deltaTwo]
    split_ifs <;> simp_all
  rw [hset]
  refine Nat.dvd_antisymm (Nat.setGcd_dvd_of_mem rfl) (Nat.dvd_setGcd_iff.2 ?_)
  rintro m rfl
  exact dvd_rfl

lemma renewalSeq_deltaTwo (n : ℕ) : renewalSeq deltaTwo n = if Even n then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => rw [renewalSeq_succ]; simp [deltaTwo]
    | m + 2 =>
      rw [renewalSeq_succ, Finset.sum_eq_single 1]
      · rw [show m + 1 - 1 = m by omega, ih m (by omega)]
        simp [deltaTwo, Nat.even_add_one]
      · intro k _ hk
        simp [deltaTwo, show k + 1 ≠ 2 by omega]
      · intro h
        simp at h

/-- Without aperiodicity the conclusion fails: the `δ₂` renewal sequence has no limit. -/
example : ¬ ∃ c, Tendsto (renewalSeq deltaTwo) atTop (𝓝 c) := by
  rintro ⟨c, hc⟩
  have h0 : Tendsto (fun m => renewalSeq deltaTwo (2 * m)) atTop (𝓝 c) :=
    hc.comp (tendsto_atTop_mono (f := fun m : ℕ => m) (fun m => by omega) tendsto_id)
  have h1 : Tendsto (fun m => renewalSeq deltaTwo (2 * m + 1)) atTop (𝓝 c) :=
    hc.comp (tendsto_atTop_mono (f := fun m : ℕ => m) (fun m => by omega) tendsto_id)
  have e0 : ∀ m, renewalSeq deltaTwo (2 * m) = 1 := fun m => by
    simp [renewalSeq_deltaTwo]
  have e1 : ∀ m, renewalSeq deltaTwo (2 * m + 1) = 0 := fun m => by
    simp [renewalSeq_deltaTwo]
  simp only [e0, e1] at h0 h1
  exact one_ne_zero ((tendsto_nhds_unique tendsto_const_nhds h0).trans
    (tendsto_nhds_unique h1 tendsto_const_nhds))

/-! ### The skip-free-up score walk -/

/-- Ladder law of the walk with steps `+1` (probability `1/5`) and `-1` (probability `4/5`):
the first strict ascending ladder height is `1`, reached with probability `P(τ₊ < ∞) = 1/4`.
The score MGF root is `θ = log 4`. -/
noncomputable def skipFreeLadder (k : ℕ) : ℝ := if k = 1 then 1 / 4 else 0

/-- `P(M > k) = 4^{-(k+1)}` for the skip-free walk. -/
noncomputable def skipFreeMaxTail (k : ℕ) : ℝ := (1 / 4) ^ (k + 1)

lemma skipFree_exp (k : ℕ) : Real.exp (Real.log 4 * k) = 4 ^ k := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]

lemma skipFree_cramer :
    HasSum (fun k : ℕ => skipFreeLadder k * Real.exp (Real.log 4 * k)) 1 := by
  have h : (fun k : ℕ => skipFreeLadder k * Real.exp (Real.log 4 * k)) =
      fun k => if k = 1 then 1 else 0 := by
    funext k
    unfold skipFreeLadder
    split_ifs with hk
    · subst hk; rw [skipFree_exp]; norm_num
    · simp
  rw [h]
  exact hasSum_ite_eq 1 1

lemma skipFree_mean :
    HasSum (fun k : ℕ => (k : ℝ) * (skipFreeLadder k * Real.exp (Real.log 4 * k))) 1 := by
  have h : (fun k : ℕ => (k : ℝ) * (skipFreeLadder k * Real.exp (Real.log 4 * k))) =
      fun k => if k = 1 then 1 else 0 := by
    funext k
    unfold skipFreeLadder
    split_ifs with hk
    · subst hk; rw [skipFree_exp]; norm_num
    · simp
  rw [h]
  exact hasSum_ite_eq 1 1

lemma skipFree_aper : Nat.setGcd {k | 0 < skipFreeLadder k} = 1 :=
  Nat.dvd_one.1 (Nat.setGcd_dvd_of_mem (show 0 < skipFreeLadder 1 by norm_num [skipFreeLadder]))

lemma skipFree_ladderTail (k : ℕ) :
    ladderTail skipFreeLadder k = if k = 0 then 1 / 4 else 0 := by
  unfold ladderTail skipFreeLadder
  split_ifs with hk
  · subst hk
    rw [tsum_eq_single 0 fun j hj => by simp [hj]]
    simp
  · simp [hk]

lemma skipFree_ladder : IsRenewalSolution skipFreeLadder (ladderTail skipFreeLadder)
    skipFreeMaxTail := by
  intro k
  rw [skipFree_ladderTail]
  cases k with
  | zero => simp [skipFreeMaxTail, skipFreeLadder]
  | succ k =>
    rw [Finset.sum_eq_single 1]
    · simp [skipFreeMaxTail, skipFreeLadder, pow_succ]
      ring
    · intro j _ hj
      simp [skipFreeLadder, hj]
    · intro h
      simp at h

/-- The ladder-height limit on the skip-free walk returns the constant
`(1 - 1/4) / ((4 - 1) * 1) = 1/4`. -/
example : Tendsto (fun k : ℕ => Real.exp (Real.log 4 * k) * skipFreeMaxTail k) atTop
    (𝓝 (1 / 4)) := by
  have h := tendsto_exp_mul_maxTail (Real.log_pos (by norm_num)) (by simp [skipFreeLadder])
    (fun k => by unfold skipFreeLadder; split_ifs <;> norm_num) skipFree_cramer skipFree_aper
    skipFree_mean skipFree_ladder
  have hg : ∑' k, skipFreeLadder k = 1 / 4 := by
    unfold skipFreeLadder
    exact tsum_ite_eq 1 _
  rw [hg, Real.exp_log (by norm_num)] at h
  norm_num at h
  exact h

/-- Cross-check: the sequence is in fact constant `1/4`. -/
example (k : ℕ) : Real.exp (Real.log 4 * k) * skipFreeMaxTail k = 1 / 4 := by
  rw [skipFree_exp, skipFreeMaxTail, pow_succ, ← mul_assoc, ← mul_pow]
  norm_num

/-- The skip-free ladder law is defective, as forced by the Cramér root. -/
example : ∑' k, skipFreeLadder k < 1 :=
  tsum_lt_one_of_hasSum_exp_mul (Real.log_pos (by norm_num)) (by simp [skipFreeLadder])
    (fun k => by unfold skipFreeLadder; split_ifs <;> norm_num) skipFree_cramer

/-! ### Boundary cases of the score-walk theorem -/

/-- Nonnegative drift: the proper ladder law `δ₁` has no positive Cramér root. -/
example {θ : ℝ} (hθ : 0 < θ) :
    ¬ HasSum (fun k : ℕ => (if k = 1 then (1 : ℝ) else 0) * Real.exp (θ * k)) 1 :=
  not_hasSum_exp_mul_of_hasSum_one hθ (by simp) (fun k => by split_ifs <;> norm_num)
    (hasSum_ite_eq 1 1)

/-- A ladder law without exponential moments: `g k = 1 / (2 k (k + 1))`. -/
noncomputable def heavyLadder (k : ℕ) : ℝ := 1 / (2 * k * (k + 1))

/-- Missing exponential moment: for every `θ > 0` the tilted series diverges, so the Cramér
hypothesis of `tendsto_exp_mul_maxTail` cannot hold. -/
example {θ : ℝ} (hθ : 0 < θ) :
    ¬ Summable fun k : ℕ => heavyLadder k * Real.exp (θ * k) := by
  intro hs
  have h0 := hs.tendsto_atTop_zero
  have hlow : ∀ k : ℕ, 1 ≤ k → θ ^ 2 / 8 ≤ heavyLadder k * Real.exp (θ * k) := by
    intro k hk
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hexp := Real.quadratic_le_exp_of_nonneg (mul_nonneg hθ.le (by linarith : (0 : ℝ) ≤ k))
    unfold heavyLadder
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have hkk : (0 : ℝ) ≤ k * k - k := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg θ) hkk, mul_nonneg hθ.le (by linarith : (0 : ℝ) ≤ k)]
  have hpos : (0 : ℝ) < θ ^ 2 / 8 := by positivity
  have hev := (h0.eventually (gt_mem_nhds hpos))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have := hN (max N 1) (le_max_left _ _)
  linarith [hlow (max N 1) (le_max_right _ _)]

end MathlibExtTest.Probability.Renewal.ScoreLadder
