/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Ulam's perfect set problem

We refute the claim that every continuous function on `[0, 1]` agrees with an analytic
function on some nonempty perfect subset. The claim fails even for smooth functions.
The counterexample is a cosine series with
frequencies chosen so that at each point its derivatives violate every analytic growth bound.
-/

namespace MathlibExt.Analysis.ScottishBook17Point1Wanted

@[expose] public section

/-- **Perfect sets of real numbers.** A set $s \subseteq \mathbb{R}$ is perfect if it is closed,
nonempty, and has no isolated points: every $x \in s$ lies in the closure of $s \setminus \{x\}$. -/
def IsPerfectSet (s : Set ℝ) : Prop :=
  IsClosed s ∧ s.Nonempty ∧ ∀ x ∈ s, x ∈ closure (s \ {x})

/-- Ulam's Problem 17.1 from the Scottish Book: for every continuous `f` on
`[0, 1]`, do there exist a perfect set `C` in `[0, 1]` and an analytic
function `φ` with `f x = φ x` for every `x ∈ C`? -/
def ScottishBookProblem17Point1Claim : Prop :=
  ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc (0 : ℝ) 1) →
    ∃ (C : Set ℝ) (φ : ℝ → ℝ), IsPerfectSet C ∧ C ⊆ Set.Icc (0 : ℝ) 1 ∧
      AnalyticOn ℝ φ (Set.Icc (0 : ℝ) 1) ∧ ∀ x ∈ C, f x = φ x

/-- The claim of Problem 17.1 for `C ^ ∞` functions on `ℝ`, the case refuted by
Zahorski's construction. The smoothness order is `(⊤ : ℕ∞)`; a bare `⊤` would
mean analytic. -/
def ScottishBookProblem17Point1SmoothClaim : Prop :=
  ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f →
    ∃ (C : Set ℝ) (φ : ℝ → ℝ), IsPerfectSet C ∧ C ⊆ Set.Icc (0 : ℝ) 1 ∧
      AnalyticOn ℝ φ (Set.Icc (0 : ℝ) 1) ∧ ∀ x ∈ C, f x = φ x

end

open Filter Finset Set
open scoped ContDiff Topology

-- A common threshold for the orders `4 * n + 1` and `4 * n + 2`.
private noncomputable def threshold (n : ℕ) : ℝ :=
  ((4 * n + 2).factorial : ℝ) * ((n : ℝ) + 1) ^ (4 * n + 3)

-- The term at index `n` uses `frequency (n + 1)`. The previous frequency bounds
-- the entire prefix, and the geometric lower bound controls the tail.
private noncomputable def frequency : ℕ → ℝ
  | 0 => 1
  | n + 1 => 4 * (threshold n + (n : ℝ) * frequency n ^ (4 * n + 2) + 2) +
      (2 : ℝ) ^ n + frequency n

private lemma threshold_nonneg (n : ℕ) : 0 ≤ threshold n := by
  unfold threshold
  positivity

private lemma frequency_pos (n : ℕ) : 0 < frequency n := by
  induction n with
  | zero => norm_num [frequency]
  | succ n ih =>
    rw [frequency]
    have := threshold_nonneg n
    positivity

private lemma frequency_monotone : Monotone frequency := by
  apply monotone_nat_of_le_succ
  intro n
  rw [frequency]
  have := threshold_nonneg n
  have := frequency_pos n
  exact le_add_of_nonneg_left (by positivity)

private lemma one_le_frequency (n : ℕ) : 1 ≤ frequency n :=
  frequency_monotone (Nat.zero_le n)

private lemma pow_le_frequency (n : ℕ) : (2 : ℝ) ^ n ≤ frequency (n + 1) := by
  rw [frequency]
  have := threshold_nonneg n
  have := frequency_pos n
  linarith [show 0 ≤ 4 * (threshold n + (n : ℝ) * frequency n ^ (4 * n + 2) + 2) by
    positivity]

private noncomputable def amplitude (k n : ℕ) : ℝ :=
  frequency (n + 1) ^ k / frequency (n + 1) ^ (4 * n)

-- The `k`-th derivative of the `n`-th summand, expressed with a phase shift.
private noncomputable def wave (k n : ℕ) (x : ℝ) : ℝ :=
  amplitude k n * Real.cos (frequency (n + 1) * x + k * (Real.pi / 2))

private lemma hasDerivAt_wave (k n : ℕ) (x : ℝ) :
    HasDerivAt (wave k n) (wave (k + 1) n x) x := by
  have h := (((hasDerivAt_id x).const_mul (frequency (n + 1))).add_const
    ((k : ℝ) * (Real.pi / 2))).cos.const_mul (amplitude k n)
  apply h.congr_deriv
  simp only [wave, amplitude, Nat.cast_succ, add_mul, one_mul, ← add_assoc,
    Real.cos_add_pi_div_two, pow_succ, id_eq, mul_one]
  ring

private lemma amplitude_nonneg (k n : ℕ) : 0 ≤ amplitude k n := by
  unfold amplitude
  have := frequency_pos (n + 1)
  positivity

private lemma norm_wave_le (k n : ℕ) (x : ℝ) : ‖wave k n x‖ ≤ amplitude k n := by
  rw [wave, norm_mul, Real.norm_eq_abs, abs_of_nonneg (amplitude_nonneg k n)]
  exact mul_le_of_le_one_right (amplitude_nonneg k n) (Real.abs_cos_le_one _)

private lemma amplitude_le_geometric {k n : ℕ} (hkn : k < 4 * n) :
    amplitude k n ≤ ((1 / 2 : ℝ) ^ n) := by
  have hb := frequency_pos (n + 1)
  calc
    amplitude k n ≤ (frequency (n + 1))⁻¹ := by
      rw [amplitude, div_le_iff₀ (pow_pos hb _), inv_mul_eq_div, le_div_iff₀ hb, ← pow_succ]
      exact pow_le_pow_right₀ (one_le_frequency _) hkn
    _ ≤ ((2 : ℝ) ^ n)⁻¹ := inv_anti₀ (by positivity) (pow_le_frequency n)
    _ = (1 / 2 : ℝ) ^ n := by rw [one_div, inv_pow]

private lemma geometric_summable : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
  summable_geometric_of_norm_lt_one (by norm_num)

private lemma amplitude_summable (k : ℕ) : Summable (amplitude k) := by
  apply (summable_nat_add_iff (k + 1)).mp
  refine ((summable_nat_add_iff (k + 1)).mpr geometric_summable).of_nonneg_of_le
    (fun n => amplitude_nonneg k _) (fun n => amplitude_le_geometric ?_)
  omega

private lemma wave_summable (k : ℕ) (x : ℝ) : Summable (fun n => wave k n x) :=
  (amplitude_summable k).of_norm_bounded (fun n => norm_wave_le k n x)

private noncomputable def cosineSeries (k : ℕ) (x : ℝ) : ℝ := ∑' n, wave k n x

private lemma hasDerivAt_cosineSeries (k : ℕ) (x : ℝ) :
    HasDerivAt (cosineSeries k) (cosineSeries (k + 1) x) x :=
  hasDerivAt_tsum (amplitude_summable (k + 1)) (hasDerivAt_wave k)
    (norm_wave_le (k + 1)) (wave_summable k 0) x

private lemma iteratedDeriv_cosineSeries (k : ℕ) :
    iteratedDeriv k (cosineSeries 0) = cosineSeries k := by
  induction k with
  | zero => exact iteratedDeriv_zero
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun x => (hasDerivAt_cosineSeries k x).deriv

private lemma contDiff_cosineSeries : ContDiff ℝ ∞ (cosineSeries 0) := by
  refine contDiff_of_differentiable_iteratedDeriv fun k _ => ?_
  rw [iteratedDeriv_cosineSeries]
  exact fun x => (hasDerivAt_cosineSeries k x).differentiableAt

private lemma norm_prefix_le (n k : ℕ) (x : ℝ) (hk : k ≤ 4 * n + 2) :
    ‖∑ j ∈ range n, wave k j x‖ ≤ (n : ℝ) * frequency n ^ (4 * n + 2) := by
  calc
    _ ≤ ∑ j ∈ range n, ‖wave k j x‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range n, frequency n ^ (4 * n + 2) := by
      apply Finset.sum_le_sum
      intro j hj
      refine (norm_wave_le k j x).trans ?_
      have hb := one_le_frequency (j + 1)
      calc
        amplitude k j ≤ frequency (j + 1) ^ k :=
          div_le_self (by positivity) (one_le_pow₀ hb)
        _ ≤ frequency n ^ k :=
          pow_le_pow_left₀ (by positivity) (frequency_monotone (by simpa using hj)) _
        _ ≤ _ := pow_le_pow_right₀ (one_le_frequency _) hk
    _ = _ := by simp

private lemma norm_tail_le (n k : ℕ) (x : ℝ) (hk : k ≤ 4 * n + 2) :
    ‖∑' j, wave k (j + (n + 1)) x‖ ≤ 2 := by
  have hbound (j : ℕ) : ‖wave k (j + (n + 1)) x‖ ≤ (1 / 2 : ℝ) ^ j :=
    (norm_wave_le _ _ _).trans <| (amplitude_le_geometric (by omega)).trans <|
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hsum := geometric_summable.of_nonneg_of_le (fun j => norm_nonneg _) hbound
  calc
    _ ≤ ∑' j, ‖wave k (j + (n + 1)) x‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' j : ℕ, (1 / 2 : ℝ) ^ j := hsum.tsum_le_tsum hbound geometric_summable
    _ = 2 := by
      rw [tsum_geometric_of_norm_lt_one (by norm_num)]
      norm_num

private lemma wave_le_of_series_le {n k : ℕ} {x : ℝ} (hk : k ≤ 4 * n + 2)
    (hs : ‖cosineSeries k x‖ ≤ threshold n) :
    ‖wave k n x‖ ≤ threshold n + (n : ℝ) * frequency n ^ (4 * n + 2) + 2 := by
  have hsplit : cosineSeries k x =
      (∑ j ∈ range n, wave k j x) + wave k n x + ∑' j, wave k (j + (n + 1)) x := by
    rw [← sum_range_succ]
    exact ((wave_summable k x).sum_add_tsum_nat_add (n + 1)).symm
  have hw : wave k n x =
      cosineSeries k x - (∑ j ∈ range n, wave k j x) - ∑' j, wave k (j + (n + 1)) x := by
    rw [hsplit]
    abel
  calc
    ‖wave k n x‖ ≤ ‖cosineSeries k x - (∑ j ∈ range n, wave k j x)‖ +
        ‖∑' j, wave k (j + (n + 1)) x‖ := by
      conv_lhs => rw [hw]
      exact norm_sub_le _ _
    _ ≤ _ := add_le_add ((norm_sub_le _ _).trans (add_le_add hs (norm_prefix_le n k x hk)))
      (norm_tail_le n k x hk)

private lemma abs_cos_le_of_series_le {n k : ℕ} {x : ℝ}
    (hlo : 4 * n + 1 ≤ k) (hhi : k ≤ 4 * n + 2)
    (hs : ‖cosineSeries k x‖ ≤ threshold n) :
    |Real.cos (frequency (n + 1) * x + k * (Real.pi / 2))| ≤ 1 / 4 := by
  have hb := frequency_pos (n + 1)
  have hamp : frequency (n + 1) ≤ amplitude k n := by
    rw [amplitude, le_div_iff₀ (pow_pos hb _), mul_comm, ← pow_succ]
    exact pow_le_pow_right₀ (one_le_frequency _) hlo
  have hw := wave_le_of_series_le hhi hs
  rw [wave, norm_mul, Real.norm_eq_abs, abs_of_nonneg (amplitude_nonneg k n),
    Real.norm_eq_abs] at hw
  have hmul := mul_le_mul_of_nonneg_right hamp
    (abs_nonneg (Real.cos (frequency (n + 1) * x + k * (Real.pi / 2))))
  have hfreq : 4 * (threshold n + (n : ℝ) * frequency n ^ (4 * n + 2) + 2) ≤
      frequency (n + 1) := by
    rw [frequency]
    have := frequency_pos n
    exact le_add_of_nonneg_right (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity))
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  apply le_of_mul_le_mul_left _ hb
  linarith only [hmul, hw, hfreq]

-- The two consecutive phases differ by `π / 2`, so one term must be large.
private lemma cosineSeries_growth (n : ℕ) (x : ℝ) :
    threshold n < ‖cosineSeries (4 * n + 1) x‖ ∨
      threshold n < ‖cosineSeries (4 * n + 2) x‖ := by
  by_contra! h
  let t := frequency (n + 1) * x + ((4 * n + 1 : ℕ) : ℝ) * (Real.pi / 2)
  have hcos : |Real.cos t| ≤ 1 / 4 :=
    abs_cos_le_of_series_le le_rfl (by omega) h.1
  have hsin := abs_cos_le_of_series_le (by omega) le_rfl h.2
  have hphase : frequency (n + 1) * x + ((4 * n + 2 : ℕ) : ℝ) * (Real.pi / 2) =
      t + Real.pi / 2 := by
    push_cast
    dsimp [t]
    push_cast
    ring
  rw [hphase, Real.cos_add_pi_div_two, abs_neg] at hsin
  nlinarith [Real.sin_sq_add_cos_sq t,
    (sq_le_sq.mpr (hsin.trans_eq (abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)).symm)),
    (sq_le_sq.mpr (hcos.trans_eq (abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)).symm))]

private lemma analytic_deriv_bound {φ : ℝ → ℝ} {x : ℝ} (h : AnalyticAt ℝ φ x) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ, ‖iteratedDeriv k φ x‖ ≤ (k.factorial : ℝ) * B ^ (k + 1) := by
  let p := FormalMultilinearSeries.ofScalars ℝ (fun k => iteratedDeriv k φ x / k.factorial)
  have hp : HasFPowerSeriesAt φ p x := h.hasFPowerSeriesAt
  obtain ⟨r, hr, hrp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.radius_pos
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  obtain ⟨M, hM, hb⟩ := p.norm_mul_pow_le_of_lt_radius hrp
  let B := max 1 (max M (r : ℝ)⁻¹)
  have hB : 1 ≤ B := le_max_left ..
  have hMB : M ≤ B := (le_max_left ..).trans (le_max_right ..)
  have hrB : (r : ℝ)⁻¹ ≤ B := (le_max_right ..).trans (le_max_right ..)
  refine ⟨B, hB, fun k => ?_⟩
  have hb' := hb k
  dsimp [p] at hb'
  rw [FormalMultilinearSeries.ofScalars_norm, norm_div,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ k.factorial)] at hb'
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hnorm : ‖iteratedDeriv k φ x‖ ≤ M * (r : ℝ)⁻¹ ^ k * k.factorial := by
    rw [← div_le_iff₀ hfac, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hr' _)]
    exact hb'
  calc
    _ ≤ M * (r : ℝ)⁻¹ ^ k * k.factorial := hnorm
    _ ≤ B * B ^ k * k.factorial := by
      gcongr
    _ = _ := by rw [pow_succ]; ring

/-- Zahorski's stronger answer: the claim fails already for `C ^ ∞` functions.
Source: Z. Zahorski, "Sur l'ensemble des points singuliers d'une fonction d'une variable
reelle admettant les derivees de tous les ordres", Fund. Math. 34 (1947), 183-245. -/
public theorem smoothFunctionPerfectAnalytic_refuted :
    ¬ ScottishBookProblem17Point1SmoothClaim := by
  intro h
  obtain ⟨C, φ, hC, hCI, hφ, heq⟩ := h (cosineSeries 0) contDiff_cosineSeries
  have hdiffC : UniqueDiffOn ℝ C := by
    intro x hx
    rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin,
      ← mem_closure_iff_nhdsWithin_neBot]
    exact hC.2.2 x hx
  -- Work in the interior, where analyticity within the interval gives analyticity at a point.
  let S := C ∩ Ioo (0 : ℝ) 1
  have hS : S.Nonempty := by
    by_contra hn
    have hend : C ⊆ ({0, 1} : Set ℝ) := by
      intro x hx
      have hI := hCI hx
      have hnot : x ∉ Ioo (0 : ℝ) 1 := fun hm => hn ⟨x, hx, hm⟩
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hnot
      simp only [mem_insert_iff, mem_singleton_iff]
      exact hnot.imp (le_antisymm · hI.1) (le_antisymm hI.2 ·)
    obtain ⟨x, hx⟩ := hC.2.1
    have hfinite := (finite_singleton (1 : ℝ)).insert 0 |>.subset hend
    have hclosed : IsClosed (C \ {x}) := (hfinite.subset sdiff_subset).isClosed
    exact (hclosed.closure_eq ▸ hC.2.2 x hx).2 (mem_singleton x)
  have hdiffS : UniqueDiffOn ℝ S := fun y hy => (hdiffC y hy.1).inter (isOpen_Ioo.mem_nhds hy.2)
  obtain ⟨x, hx⟩ := hS
  have hφx : AnalyticAt ℝ φ x :=
    (isOpen_Ioo.analyticOn_iff_analyticOnNhd.mp (hφ.mono Ioo_subset_Icc_self)) x hx.2
  -- The agreement on S determines every derivative at x.
  have hderiv (k : ℕ) : cosineSeries k x = iteratedDeriv k φ x := by
    rw [← iteratedDeriv_cosineSeries, ← iteratedDerivWithin_eq_iteratedDeriv hdiffS
      (contDiff_cosineSeries.of_le (by simp)).contDiffAt hx,
      ← iteratedDerivWithin_eq_iteratedDeriv hdiffS hφx.contDiffAt hx]
    exact iteratedDerivWithin_congr (fun y (hy : y ∈ S) => heq y hy.1) hx
  obtain ⟨B, hB, hbound⟩ := analytic_deriv_bound hφx
  obtain ⟨n, hn⟩ := exists_nat_gt B
  have hupper (k : ℕ) (hk : k ≤ 4 * n + 2) : ‖cosineSeries k x‖ ≤ threshold n := by
    rw [hderiv]
    refine (hbound k).trans ?_
    unfold threshold
    have hn' : 1 ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hpow : B ^ (k + 1) ≤ ((n : ℝ) + 1) ^ (4 * n + 3) :=
      (pow_le_pow_left₀ (by linarith) (by linarith : B ≤ (n : ℝ) + 1) _).trans
        (pow_le_pow_right₀ hn' (by omega))
    gcongr
  exact (cosineSeries_growth n x).elim
    (fun hlarge => hlarge.not_ge (hupper _ (by omega)))
    (fun hlarge => hlarge.not_ge (hupper _ le_rfl))

/--
Problem 17.1 is false: the answer is negative. Source: S. Ulam, Problem 17.1
of the Scottish Book; Z. Zahorski gave a negative answer by constructing a
`C ^ ∞` function that agrees with every real-analytic function on at most
finitely many points, so no nonempty perfect set `C` can work for it: Z.
Zahorski, "Sur l'ensemble des points singuliers d'une fonction d'une
variable reelle admettant les derivees de tous les ordres", Fund. Math. 34
(1947), 183-245. The 2026 survey "90+ years of the Scottish Book"
(arXiv:2603.27867) confirms the negative solution.
-/
public theorem continuousFunctionPerfectAnalytic_refuted :
    ¬ ScottishBookProblem17Point1Claim :=
  fun h => smoothFunctionPerfectAnalytic_refuted fun f hf => h f hf.continuous.continuousOn

end MathlibExt.Analysis.ScottishBook17Point1Wanted
