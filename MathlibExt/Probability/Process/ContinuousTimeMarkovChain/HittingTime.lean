/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path
import Mathlib.Probability.Independence.InfinitePi
import MathlibExt.Probability.Distributions.ExponentialMoments

/-!
# Hitting times of finite continuous-time Markov chains

For the path process `ctmcPath Q i` of
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path` and a set of states `A`, the
**hitting time** of `A` is `H_A = inf {t ≥ 0 | X t ∈ A}`, valued in `ℝ≥0∞`
(`ctmcHittingTime`). This file identifies the mean `E_i H_A` and the product moment
`E_i (H_A H_B)` with the backward (first-step) equations of the chain (Norris 1997, §3.3 for
the mean).

Write `q i = -Q i i` and `Π` for the jump matrix (`ctmcJumpMatrix`). Off `A`, where `q i ≠ 0`,
the first-step equations read, in `ℝ≥0∞`,

* `E_i H_A = 1 / q i + ∑ⱼ Π i j E_j H_A`, and
* off `A ∪ B`: `E_i (H_A H_B) = (E_i H_A + E_i H_B) / q i + ∑ⱼ Π i j E_j (H_A H_B)`.

The second identity comes from `H_A H_B = (S + H_A') (S + H_B')`, where `S` is the first holding
time and `H'` are the hitting times after the first jump, together with `E S² = 2 / q²`.
Every nonnegative supersolution of these equations dominates the expectations, which are thus
the minimal solutions. Multiplying by `q i` turns the equations into the backward equations
`(Q m) i = -1` and `(Q f) i = -(m_A i + m_B i)`.

## Main definitions

* `ProbabilityTheory.ctmcHittingTime Q i A ω`: the hitting time of `A` by the chain started at
  `i` and driven by the steps `ω`.

## Main results

* `ctmcHittingTime_eq_add`, `ctmcHittingTime_eq_zero`: first-jump decomposition of the hitting
  time (deterministic).
* `IsRateMatrix.lintegral_ctmcHittingTime`, `IsRateMatrix.lintegral_ctmcHittingTime_le`: the
  mean hitting time solves the first-step equations and is their minimal nonnegative solution.
* `IsRateMatrix.lintegral_ctmcHittingTime_mul`, `IsRateMatrix.lintegral_ctmcHittingTime_mul_le`:
  the same for the product moment of two hitting times.
* `IsRateMatrix.ctmcHittingTime_backward`, `IsRateMatrix.ctmcHittingTime_mul_backward`: if the
  backward equations have a nonnegative real solution, the expectations are finite, bounded by
  it, and their real parts solve the same backward equations.

## Implementation notes

The infimum over the uncountable time set is not used for measurability. Instead, the hitting
time is the increasing limit of its truncations at the jump times, defined by recursion on the
number of jumps; this holds almost surely, by non-explosion (`ae_tendsto_ctmcJumpTime`) and
because the exponential clocks are almost surely positive. The expectations of the truncations
satisfy the first-step recursion, which passes to the limit by monotone convergence.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §2.6 and §3.3.
-/

@[expose] public section

open Finset MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace ProbabilityTheory

section Path

variable {ι : Type*} {Q : Matrix ι ι ℝ}

/-- The **hitting time** `inf {t ≥ 0 | X t ∈ A}` of a set of states `A` by the chain
`X = ctmcPath Q i ω` started at `i`, valued in `ℝ≥0∞` (it is `∞` if `A` is never visited). -/
noncomputable def ctmcHittingTime (Q : Matrix ι ι ℝ) (i : ι) (A : Set ι)
    (ω : ℕ → (ι → ι) × ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : ctmcPath Q i ω t ∈ A), (t : ℝ≥0∞)

/-- **First-jump decomposition of a hitting time**: from a state `i ∉ A`, the hitting time of
`A` is the first holding time plus the hitting time of the chain restarted after the first
jump. -/
theorem ctmcHittingTime_eq_add {A : Set ι} {i : ι} (hi : i ∉ A) (ω : ℕ → (ι → ι) × ℝ) :
    ctmcHittingTime Q i A ω =
      ctmcHoldingTime Q i ω 0 + ctmcHittingTime Q ((ω 0).1 i) A (ctmcShift 1 ω) := by
  have hX := ctmcPath_eq_ite (Q := Q) i ω
  unfold ctmcHittingTime
  by_cases hT : ctmcHoldingTime Q i ω 0 = ∞
  · rw [hT, top_add]
    refine iInf₂_eq_top.2 fun t ht => absurd ?_ hi
    rwa [hX t, ite_eq_left (by rw [hT]; exact ENNReal.coe_lt_top)] at ht
  · set S := ctmcHoldingTime Q i ω 0 with hSdef
    have hs : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) = S := ENNReal.coe_toNNReal hT
    rw [ENNReal.add_iInf₂]
    refine le_antisymm (le_iInf₂ fun u hu => ?_) (le_iInf₂ fun t ht => ?_)
    · have key : ctmcPath Q i ω (S.toNNReal + u) ∈ A := by
        rw [hX, ite_eq_right (by rw [ENNReal.coe_add, hs]; exact not_lt.2 le_self_add),
          add_tsub_cancel_left]
        exact hu
      calc _ ≤ ((S.toNNReal + u : ℝ≥0) : ℝ≥0∞) := iInf₂_le (S.toNNReal + u) key
        _ = S + u := by rw [ENNReal.coe_add, hs]
    · have hlt : ¬ (t : ℝ≥0∞) < S := fun h => hi (by rwa [hX t, ite_eq_left h] at ht)
      rw [hX t, ite_eq_right hlt] at ht
      have hle : S.toNNReal ≤ t := by rw [← ENNReal.coe_le_coe, hs]; exact not_lt.1 hlt
      calc _ ≤ S + ((t - S.toNNReal : ℝ≥0) : ℝ≥0∞) := iInf₂_le (t - S.toNNReal) ht
        _ = ((S.toNNReal + (t - S.toNNReal) : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_add, hs]
        _ = t := by rw [add_tsub_cancel_of_le hle]

/-- From a state `i ∈ A`, the hitting time of `A` is `0` as soon as the first holding time is
positive (which fails only on a null event, see `ctmcHoldingTime`). -/
theorem ctmcHittingTime_eq_zero {A : Set ι} {i : ι} (hi : i ∈ A) {ω : ℕ → (ι → ι) × ℝ}
    (hS : 0 < ctmcHoldingTime Q i ω 0) : ctmcHittingTime Q i A ω = 0 := by
  have h0 : ctmcPath Q i ω 0 ∈ A := by
    rwa [ctmcPath_eq_ite, ite_eq_left (by simpa using hS)]
  exact nonpos_iff_eq_zero.1 ((iInf₂_le 0 h0).trans_eq ENNReal.coe_zero)

/-! ### Truncation at the jump times -/

open scoped Classical in
/-- The hitting time of `A` truncated at the `n`-th jump time, by recursion on `n`. -/
private noncomputable def hitTrunc (Q : Matrix ι ι ℝ) (A : Set ι) :
    ℕ → ι → (ℕ → (ι → ι) × ℝ) → ℝ≥0∞
  | 0, _, _ => 0
  | n + 1, i, ω => if i ∈ A then 0 else
      ctmcHoldingTime Q i ω 0 + hitTrunc Q A n ((ω 0).1 i) (ctmcShift 1 ω)

private lemma hitTrunc_zero (A : Set ι) (i : ι) (ω : ℕ → (ι → ι) × ℝ) :
    hitTrunc Q A 0 i ω = 0 := rfl

private lemma hitTrunc_succ_of_mem {A : Set ι} {i : ι} (hi : i ∈ A) (n : ℕ)
    (ω : ℕ → (ι → ι) × ℝ) : hitTrunc Q A (n + 1) i ω = 0 := by
  simp [hitTrunc, hi]

private lemma hitTrunc_succ_of_notMem {A : Set ι} {i : ι} (hi : i ∉ A) (n : ℕ)
    (ω : ℕ → (ι → ι) × ℝ) : hitTrunc Q A (n + 1) i ω =
      ctmcHoldingTime Q i ω 0 + hitTrunc Q A n ((ω 0).1 i) (ctmcShift 1 ω) := by
  simp [hitTrunc, hi]

private lemma hitTrunc_of_mem {A : Set ι} {i : ι} (hi : i ∈ A) (n : ℕ)
    (ω : ℕ → (ι → ι) × ℝ) : hitTrunc Q A n i ω = 0 := by
  cases n with
  | zero => rfl
  | succ n => exact hitTrunc_succ_of_mem hi n ω

private lemma hitTrunc_le_succ (A : Set ι) (n : ℕ) :
    ∀ i ω, hitTrunc Q A n i ω ≤ hitTrunc Q A (n + 1) i ω := by
  induction n with
  | zero => intro i ω; exact zero_le
  | succ n ih =>
    intro i ω
    by_cases hi : i ∈ A
    · rw [hitTrunc_succ_of_mem hi, hitTrunc_succ_of_mem hi]
    · rw [hitTrunc_succ_of_notMem hi, hitTrunc_succ_of_notMem hi]
      gcongr
      exact ih _ _

private lemma monotone_hitTrunc (A : Set ι) (i : ι) (ω : ℕ → (ι → ι) × ℝ) :
    Monotone fun n => hitTrunc Q A n i ω :=
  monotone_nat_of_le_succ fun n => hitTrunc_le_succ A n i ω

/-- On step sequences with positive clocks, the truncation is the minimum of the hitting time
and the `n`-th jump time. -/
private lemma hitTrunc_eq_min (hdiag : ∀ k, Q k k ≤ 0) (A : Set ι) (n : ℕ) :
    ∀ (i : ι) (ω : ℕ → (ι → ι) × ℝ), (∀ m, 0 < (ω m).2) →
      hitTrunc Q A n i ω = min (ctmcHittingTime Q i A ω) (ctmcJumpTime Q i ω n) := by
  induction n with
  | zero => intro i ω _; simp [hitTrunc_zero, ctmcJumpTime]
  | succ n ih =>
    intro i ω hω
    by_cases hi : i ∈ A
    · have hS : 0 < ctmcHoldingTime Q i ω 0 := by
        unfold ctmcHoldingTime
        split_ifs with h0
        · exact ENNReal.zero_lt_top
        · have hq : 0 < -Q (ctmcJumpChain i ω 0) (ctmcJumpChain i ω 0) :=
            lt_of_le_of_ne (neg_nonneg.2 (hdiag _)) (fun h => h0 (by linarith))
          exact ENNReal.ofReal_pos.2 (div_pos (hω 0) hq)
      rw [hitTrunc_succ_of_mem hi, ctmcHittingTime_eq_zero hi hS, zero_min]
    · rw [hitTrunc_succ_of_notMem hi, ih ((ω 0).1 i) (ctmcShift 1 ω) fun m => hω (1 + m),
        ctmcHittingTime_eq_add hi, add_comm n 1, ctmcJumpTime_add]
      have h1 : ctmcJumpTime Q i ω 1 = ctmcHoldingTime Q i ω 0 := by simp [ctmcJumpTime]
      rw [h1, min_add_add_left]
      rfl

private lemma hitTrunc_mul_of_mem {A B : Set ι} {i : ι} (hi : i ∈ A ∪ B) (n : ℕ)
    (ω : ℕ → (ι → ι) × ℝ) : hitTrunc Q A n i ω * hitTrunc Q B n i ω = 0 := by
  rcases hi with hi | hi
  · rw [hitTrunc_of_mem hi, zero_mul]
  · rw [hitTrunc_of_mem hi, mul_zero]

private lemma ctmcHoldingTime_zero_eq {i : ι} (hq : Q i i ≠ 0) (ω : ℕ → (ι → ι) × ℝ) :
    ctmcHoldingTime Q i ω 0 = ENNReal.ofReal ((ω 0).2 / -Q i i) := by
  simp [ctmcHoldingTime, ctmcJumpChain, hq]

private lemma measurable_comp_first [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Finite ι]
    (i : ι)
    {G : ι → (ℕ → (ι → ι) × ℝ) → ℝ≥0∞} (hG : ∀ j, Measurable (G j)) :
    Measurable fun ω : ℕ → (ι → ι) × ℝ => G ((ω 0).1 i) (ctmcShift 1 ω) := by
  have hH : Measurable fun p : (ℕ → (ι → ι) × ℝ) × ι => G p.2 p.1 :=
    measurable_from_prod_countable_left fun j => hG j
  have hsh : Measurable (ctmcShift (ι := ι) 1) :=
    Measurable.of_eval fun j => measurable_pi_apply (1 + j)
  exact hH.comp (hsh.prodMk ((measurable_pi_apply i).comp (measurable_pi_apply 0).fst))

private lemma measurable_hitTrunc [MeasurableSpace ι] [DiscreteMeasurableSpace ι] [Finite ι]
    (A : Set ι) (n : ℕ) : ∀ i, Measurable (hitTrunc Q A n i) := by
  induction n with
  | zero => intro i; exact measurable_const
  | succ n ih =>
    intro i
    by_cases hi : i ∈ A
    · rw [show hitTrunc Q A (n + 1) i = fun _ => 0 from funext (hitTrunc_succ_of_mem hi n)]
      exact measurable_const
    · rw [show hitTrunc Q A (n + 1) i = _ from funext (hitTrunc_succ_of_notMem hi n)]
      exact (measurable_ctmcHoldingTime i 0).add (measurable_comp_first i ih)

private lemma measurable_shift_tail [MeasurableSpace ι] (n : ℕ) :
    Measurable[⨆ k ∈ Set.Ici n,
      MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance] (ctmcShift n) := by
  rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun j => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup₂ (f := fun k (_ : k ∈ Set.Ici n) =>
    MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance) (n + j)
    (Set.mem_Ici.mpr (Nat.le_add_right n j))

end Path

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}


/-! ### The law of the first step -/

private lemma sum_ofReal_ctmcJumpMatrix (hQ : IsRateMatrix Q) (i : ι) :
    ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => hQ.ctmcJumpMatrix_nonneg i j,
    hQ.sum_ctmcJumpMatrix i, ENNReal.ofReal_one]

omit [DecidableEq ι] in
private lemma neg_diag_pos (hQ : IsRateMatrix Q) {i : ι} (hq : Q i i ≠ 0) : 0 < -Q i i :=
  lt_of_le_of_ne (neg_nonneg.2 (hQ.diag_nonpos i)) (fun h => hq (by linarith))

section Step

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

omit [DiscreteMeasurableSpace ι] in
private lemma step_indep (hQ : IsRateMatrix Q) (n : ℕ) :
    Indep (⨆ k ∈ Set.Iio n, MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance)
      (⨆ k ∈ Set.Ici n, MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance)
      (ctmcInputMeasure hQ) := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => ctmcStepMeasure hQ)
    (X := fun _ x => x) (fun _ => measurable_id)
  rw [iIndepFun_iff_iIndep] at h
  refine indep_iSup_of_disjoint (fun k => (measurable_pi_apply k).comap_le) h ?_
  exact Set.disjoint_left.mpr fun k hk hk' => absurd (Set.mem_Iio.mp hk) (not_lt.mpr hk')

omit [DiscreteMeasurableSpace ι] in
/-- Under the law of the steps, the first step is independent of the shifted steps, which have
the same law. -/
private lemma map_first_shift (hQ : IsRateMatrix Q) :
    (ctmcInputMeasure hQ).map (fun ω => (ω 0, ctmcShift 1 ω)) =
      (ctmcStepMeasure hQ).prod (ctmcInputMeasure hQ) := by
  have hsh : Measurable (ctmcShift (ι := ι) 1) :=
    Measurable.of_eval fun j => measurable_pi_apply (1 + j)
  have hind : IndepFun (fun ω : ℕ → (ι → ι) × ℝ => ω 0) (ctmcShift 1) (ctmcInputMeasure hQ) := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left (step_indep hQ 1) ?_)
      (measurable_shift_tail 1).comap_le
    exact le_iSup₂ (f := fun k (_ : k ∈ Set.Iio 1) =>
      MeasurableSpace.comap (fun ω : ℕ → (ι → ι) × ℝ => ω k) inferInstance) 0
      (Set.mem_Iio.mpr Nat.zero_lt_one)
  have hmap : (ctmcInputMeasure hQ).map (ctmcShift 1) = ctmcInputMeasure hQ :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ctmcStepMeasure hQ)
      (f := fun j => 1 + j) (add_right_injective 1)
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
    hsh.aemeasurable).1 hind, hmap]
  congr 1
  exact Measure.infinitePi_map_eval _ 0

/-- **First-step integral**: the first step `(ξ, E)` is independent of the shifted steps, `ξ i`
has law row `i` of the jump matrix, and the clock `E` has law `expMeasure 1`. -/
private lemma lintegral_step (hQ : IsRateMatrix Q) (i : ι) {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ)
    {G : ι → (ℕ → (ι → ι) × ℝ) → ℝ≥0∞} (hG : ∀ j, Measurable (G j)) :
    ∫⁻ ω, ψ (ω 0).2 * G ((ω 0).1 i) (ctmcShift 1 ω) ∂ctmcInputMeasure hQ =
      (∫⁻ x, ψ x ∂expMeasure 1) *
        ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * ∫⁻ ω, G j ω ∂ctmcInputMeasure hQ := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  set μ := ctmcInputMeasure hQ
  set K : ι → ℝ≥0∞ := fun j => ∫⁻ ω, G j ω ∂μ
  have hg : Measurable fun ω : ℕ → (ι → ι) × ℝ => (ω 0, ctmcShift 1 ω) :=
    (measurable_pi_apply 0).prodMk (Measurable.of_eval fun j => measurable_pi_apply (1 + j))
  have hH : Measurable fun p : (ℕ → (ι → ι) × ℝ) × ι => G p.2 p.1 :=
    measurable_from_prod_countable_left fun j => hG j
  have hF : Measurable fun p : ((ι → ι) × ℝ) × (ℕ → (ι → ι) × ℝ) => ψ p.1.2 * G (p.1.1 i) p.2 :=
    (hψ.comp measurable_fst.snd).mul
      (hH.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst.fst)))
  have hK : Measurable fun ξ : ι → ι => K (ξ i) :=
    (Measurable.of_discrete (f := K)).comp (measurable_pi_apply i)
  have hpi : ∫⁻ ξ, K (ξ i) ∂(Measure.pi fun k => (hQ.ctmcJumpPMF k).toMeasure) =
      ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * K j := by
    rw [(measurePreserving_eval (fun k => (hQ.ctmcJumpPMF k).toMeasure) i).lintegral_comp
      Measurable.of_discrete, lintegral_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j), mul_comm]
    simp [IsRateMatrix.ctmcJumpPMF, PMF.ofFintype_apply]
  calc ∫⁻ ω, ψ (ω 0).2 * G ((ω 0).1 i) (ctmcShift 1 ω) ∂μ
      = ∫⁻ p, ψ p.1.2 * G (p.1.1 i) p.2 ∂(μ.map fun ω => (ω 0, ctmcShift 1 ω)) :=
        (lintegral_map hF hg).symm
    _ = ∫⁻ a, ∫⁻ ω, ψ a.2 * G (a.1 i) ω ∂μ ∂ctmcStepMeasure hQ := by
        rw [map_first_shift, lintegral_prod _ hF.aemeasurable]
    _ = ∫⁻ a, ψ a.2 * K (a.1 i) ∂ctmcStepMeasure hQ := by
        refine lintegral_congr fun a => ?_
        exact lintegral_const_mul _ (hG _)
    _ = ∫⁻ ξ, ∫⁻ x, ψ x * K (ξ i) ∂expMeasure 1
          ∂(Measure.pi fun k => (hQ.ctmcJumpPMF k).toMeasure) := by
        have hm : Measurable fun a : (ι → ι) × ℝ => ψ a.2 * K (a.1 i) :=
          (hψ.comp measurable_snd).mul (hK.comp measurable_fst)
        rw [ctmcStepMeasure, lintegral_prod _ hm.aemeasurable]
    _ = (∫⁻ x, ψ x ∂expMeasure 1) * ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * K j := by
        simp_rw [lintegral_mul_const _ hψ]
        rw [lintegral_const_mul _ hK, hpi]

private lemma ae_pos_expMeasure : ∀ᵐ x ∂expMeasure 1, 0 < x := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have h := cdf_expMeasure_eq one_pos 0
  rw [cdf_eq_real] at h
  simp only [le_refl, ↓reduceIte, mul_zero, neg_zero, Real.exp_zero, sub_self] at h
  rw [ae_iff, show {x : ℝ | ¬ 0 < x} = Set.Iic 0 from Set.ext fun x => by simp]
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h

private lemma lintegral_ofReal_div_expMeasure {q : ℝ} (hq : 0 < q) :
    ∫⁻ x, ENNReal.ofReal (x / q) ∂expMeasure 1 = ENNReal.ofReal (1 / q) := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hint : Integrable (fun x : ℝ => x / q) (expMeasure 1) :=
    (integrable_id_expMeasure one_pos).div_const q
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_pos_expMeasure.mono fun x hx => div_nonneg hx.le hq.le)]
  congr 1
  rw [integral_div]
  simpa using congrArg (· / q) (integral_id_expMeasure one_pos)

private lemma lintegral_ofReal_div_mul_expMeasure {q : ℝ} (hq : 0 < q) :
    ∫⁻ x, ENNReal.ofReal (x / q) * ENNReal.ofReal (x / q) ∂expMeasure 1 =
      ENNReal.ofReal (2 / q ^ 2) := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hae : (fun x => ENNReal.ofReal (x / q) * ENNReal.ofReal (x / q)) =ᵐ[expMeasure 1]
      fun x => ENNReal.ofReal (x ^ 2 / q ^ 2) := by
    filter_upwards [ae_pos_expMeasure] with x hx
    rw [← ENNReal.ofReal_mul (div_nonneg hx.le hq.le)]
    congr 1
    ring
  rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal
    ((integrable_pow_expMeasure one_pos 2).div_const _)
    (Eventually.of_forall fun x => by positivity), integral_div, integral_sq_expMeasure one_pos]
  norm_num

/-- The mean of the first holding time. -/
private lemma lintegral_holding (hQ : IsRateMatrix Q) {i : ι} (hq : Q i i ≠ 0) :
    ∫⁻ ω, ctmcHoldingTime Q i ω 0 ∂ctmcInputMeasure hQ = ENNReal.ofReal (1 / -Q i i) := by
  have h := lintegral_step hQ i (ψ := fun x => ENNReal.ofReal (x / -Q i i))
    (ENNReal.measurable_ofReal.comp (measurable_id.div_const _))
    (G := fun _ _ => 1) (fun _ => measurable_const)
  simp only [mul_one, lintegral_const, measure_univ, sum_ofReal_ctmcJumpMatrix hQ] at h
  simp_rw [ctmcHoldingTime_zero_eq hq, h, lintegral_ofReal_div_expMeasure (neg_diag_pos hQ hq)]

/-- The second moment of the first holding time. -/
private lemma lintegral_holding_sq (hQ : IsRateMatrix Q) {i : ι} (hq : Q i i ≠ 0) :
    ∫⁻ ω, ctmcHoldingTime Q i ω 0 * ctmcHoldingTime Q i ω 0 ∂ctmcInputMeasure hQ =
      ENNReal.ofReal (2 / (-Q i i) ^ 2) := by
  have h := lintegral_step hQ i
    (ψ := fun x => ENNReal.ofReal (x / -Q i i) * ENNReal.ofReal (x / -Q i i))
    ((ENNReal.measurable_ofReal.comp (measurable_id.div_const _)).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.div_const _)))
    (G := fun _ _ => 1) (fun _ => measurable_const)
  simp only [mul_one, lintegral_const, measure_univ, sum_ofReal_ctmcJumpMatrix hQ] at h
  simp_rw [ctmcHoldingTime_zero_eq hq, h,
    lintegral_ofReal_div_mul_expMeasure (neg_diag_pos hQ hq)]

/-- The first holding time times a function of the shifted steps. -/
private lemma lintegral_holding_mul (hQ : IsRateMatrix Q) {i : ι} (hq : Q i i ≠ 0)
    {G : ι → (ℕ → (ι → ι) × ℝ) → ℝ≥0∞} (hG : ∀ j, Measurable (G j)) :
    ∫⁻ ω, ctmcHoldingTime Q i ω 0 * G ((ω 0).1 i) (ctmcShift 1 ω) ∂ctmcInputMeasure hQ =
      ENNReal.ofReal (1 / -Q i i) *
        ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * ∫⁻ ω, G j ω ∂ctmcInputMeasure hQ := by
  have hψ : Measurable fun x : ℝ => ENNReal.ofReal (x / -Q i i) :=
    ENNReal.measurable_ofReal.comp (measurable_id.div_const _)
  simp_rw [ctmcHoldingTime_zero_eq hq]
  rw [lintegral_step hQ i hψ hG,
    lintegral_ofReal_div_expMeasure (neg_diag_pos hQ hq)]

/-- A function of the shifted steps. -/
private lemma lintegral_shift (hQ : IsRateMatrix Q) (i : ι)
    {G : ι → (ℕ → (ι → ι) × ℝ) → ℝ≥0∞} (hG : ∀ j, Measurable (G j)) :
    ∫⁻ ω, G ((ω 0).1 i) (ctmcShift 1 ω) ∂ctmcInputMeasure hQ =
      ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * ∫⁻ ω, G j ω ∂ctmcInputMeasure hQ := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have h := lintegral_step hQ i (ψ := fun _ => 1) measurable_const hG
  simpa using h

end Step

/-! ### From first-step equations to backward equations -/

omit [DecidableEq ι] in
/-- A state with exit rate `0` has a zero row, so `(Q m) i = 0`. -/
private lemma mulVec_eq_zero_of_diag (hQ : IsRateMatrix Q) {i : ι} (h0 : Q i i = 0)
    (m : ι → ℝ) : (Q *ᵥ m) i = 0 := by
  classical
  have hsum : ∑ j ∈ univ.erase i, Q i j = 0 := by linarith [hQ.diag_eq i]
  have hz : ∀ j ∈ univ.erase i, Q i j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j hj => hQ.nonneg_of_ne (ne_of_mem_erase hj).symm).1
      hsum
  simp only [mulVec, dotProduct]
  rw [← Finset.add_sum_erase _ _ (mem_univ i), h0, zero_mul, zero_add]
  exact Finset.sum_eq_zero fun j hj => by rw [hz j hj, zero_mul]

/-- Off the absorbing states, the first-step form `x i = c / q i + ∑ⱼ Π i j x j` of a linear
equation is equivalent to the backward form `(Q x) i = -c`. -/
private lemma eq_jump_iff {i : ι} (hq : Q i i ≠ 0) (x : ι → ℝ) (c : ℝ) :
    x i = c / -Q i i + ∑ j, ctmcJumpMatrix Q i j * x j ↔ (Q *ᵥ x) i = -c := by
  have hq' : -Q i i ≠ 0 := neg_ne_zero.2 hq
  have key : (∑ j, ctmcJumpMatrix Q i j * x j) * -Q i i = (Q *ᵥ x) i - Q i i * x i := by
    simp only [mulVec, dotProduct]
    rw [Finset.sum_mul, ← Finset.add_sum_erase _ _ (mem_univ i),
      ← Finset.add_sum_erase (s := univ) (fun j => Q i j * x j) (mem_univ i)]
    have hj : ∀ j ∈ univ.erase i, ctmcJumpMatrix Q i j * x j * -Q i i = Q i j * x j := by
      intro j hj
      simp only [ctmcJumpMatrix, hq, ↓reduceIte, (ne_of_mem_erase hj).symm]
      field_simp
    rw [Finset.sum_congr rfl hj]
    simp [ctmcJumpMatrix, hq]
  rw [div_add' _ _ _ hq', eq_div_iff hq', key]
  constructor <;> intro h <;> linarith

private lemma ofReal_jump (hQ : IsRateMatrix Q) {i : ι} (hq : Q i i ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    {x : ι → ℝ} (hx : ∀ j, 0 ≤ x j) :
    ENNReal.ofReal (c / -Q i i + ∑ j, ctmcJumpMatrix Q i j * x j) =
      ENNReal.ofReal (c / -Q i i) +
        ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * ENNReal.ofReal (x j) := by
  have hq' : 0 < -Q i i :=
    lt_of_le_of_ne (neg_nonneg.2 (hQ.diag_nonpos i)) (fun h => hq (by linarith))
  rw [ENNReal.ofReal_add (div_nonneg hc hq'.le)
      (Finset.sum_nonneg fun j _ => mul_nonneg (hQ.ctmcJumpMatrix_nonneg i j) (hx j)),
    ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hQ.ctmcJumpMatrix_nonneg i j) (hx j)]
  simp_rw [ENNReal.ofReal_mul (hQ.ctmcJumpMatrix_nonneg i _)]

private lemma toReal_jump (hQ : IsRateMatrix Q) (i : ι) {c : ℝ≥0∞}
    (hc : c ≠ ∞) {x : ι → ℝ≥0∞} (hx : ∀ j, x j ≠ ∞) :
    (c + ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * x j).toReal =
      c.toReal + ∑ j, ctmcJumpMatrix Q i j * (x j).toReal := by
  rw [ENNReal.toReal_add hc (ENNReal.sum_ne_top.2 fun j _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hx j)),
    ENNReal.toReal_sum fun j _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hx j)]
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hQ.ctmcJumpMatrix_nonneg i _)]

/-! ### Expectations of the truncations -/

section Expectation

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

omit [DiscreteMeasurableSpace ι] in
private lemma ae_clock_pos (hQ : IsRateMatrix Q) :
    ∀ᵐ ω ∂ctmcInputMeasure hQ, ∀ m, 0 < (ω m).2 := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [ae_all_iff]
  intro m
  have h2 : ∀ᵐ a ∂ctmcStepMeasure hQ, 0 < a.2 := by
    have hmap : (ctmcStepMeasure hQ).map Prod.snd = expMeasure 1 := by
      simp [ctmcStepMeasure, Measure.map_snd_prod]
    exact ae_of_ae_map measurable_snd.aemeasurable (hmap ▸ ae_pos_expMeasure)
  have hmap : (ctmcInputMeasure hQ).map (fun ω => ω m) = ctmcStepMeasure hQ :=
    Measure.infinitePi_map_eval _ m
  exact ae_of_ae_map (measurable_pi_apply m).aemeasurable (hmap ▸ h2)

omit [DiscreteMeasurableSpace ι] in
private lemma iSup_hitTrunc_ae (hQ : IsRateMatrix Q) (A : Set ι) (i : ι) :
    ∀ᵐ ω ∂ctmcInputMeasure hQ, ⨆ n, hitTrunc Q A n i ω = ctmcHittingTime Q i A ω := by
  filter_upwards [ae_clock_pos hQ, hQ.ae_tendsto_ctmcJumpTime i] with ω hω hT
  simp_rw [hitTrunc_eq_min hQ.diag_nonpos A _ i ω hω]
  rw [← inf_iSup_eq, iSup_eq_of_tendsto (ctmcJumpTime_mono i ω) hT]
  exact min_top_right _

private lemma tendsto_lintegral_hitTrunc (hQ : IsRateMatrix Q) (A : Set ι) (i : ι) :
    Tendsto (fun n => ∫⁻ ω, hitTrunc Q A n i ω ∂ctmcInputMeasure hQ) atTop
      (𝓝 (∫⁻ ω, ctmcHittingTime Q i A ω ∂ctmcInputMeasure hQ)) := by
  have hmono : Monotone fun n => ∫⁻ ω, hitTrunc Q A n i ω ∂ctmcInputMeasure hQ :=
    fun m n h => lintegral_mono fun ω => monotone_hitTrunc A i ω h
  convert tendsto_atTop_iSup hmono using 2
  rw [← lintegral_iSup (fun n => measurable_hitTrunc A n i)
    (fun m n h ω => monotone_hitTrunc A i ω h)]
  exact (lintegral_congr_ae (iSup_hitTrunc_ae hQ A i)).symm

private lemma iSup_mul_iSup_of_monotone {f g : ℕ → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g) :
    (⨆ n, f n) * (⨆ n, g n) = ⨆ n, f n * g n := by
  rw [ENNReal.iSup_mul]
  simp_rw [ENNReal.mul_iSup]
  refine le_antisymm (iSup_le fun m => iSup_le fun n => ?_)
    (iSup_le fun n => le_iSup_of_le n (le_iSup_of_le n le_rfl))
  exact le_iSup_of_le (max m n) (mul_le_mul' (hf (le_max_left _ _)) (hg (le_max_right _ _)))

private lemma tendsto_lintegral_hitTrunc_mul (hQ : IsRateMatrix Q) (A B : Set ι) (i : ι) :
    Tendsto (fun n => ∫⁻ ω, hitTrunc Q A n i ω * hitTrunc Q B n i ω ∂ctmcInputMeasure hQ)
      atTop (𝓝 (∫⁻ ω, ctmcHittingTime Q i A ω * ctmcHittingTime Q i B ω
        ∂ctmcInputMeasure hQ)) := by
  have hm : ∀ ω, Monotone fun n => hitTrunc Q A n i ω * hitTrunc Q B n i ω :=
    fun ω m n h => mul_le_mul' (monotone_hitTrunc A i ω h) (monotone_hitTrunc B i ω h)
  have hmono : Monotone fun n =>
      ∫⁻ ω, hitTrunc Q A n i ω * hitTrunc Q B n i ω ∂ctmcInputMeasure hQ :=
    fun m n h => lintegral_mono fun ω => hm ω h
  convert tendsto_atTop_iSup hmono using 2
  have hmeas : ∀ n, Measurable fun ω => hitTrunc Q A n i ω * hitTrunc Q B n i ω :=
    fun n => (measurable_hitTrunc A n i).mul (measurable_hitTrunc B n i)
  rw [← lintegral_iSup hmeas (fun m n h ω => hm ω h)]
  refine (lintegral_congr_ae ?_).symm
  filter_upwards [iSup_hitTrunc_ae hQ A i, iSup_hitTrunc_ae hQ B i] with ω hA hB
  rw [← hA, ← hB, iSup_mul_iSup_of_monotone (monotone_hitTrunc A i ω)
    (monotone_hitTrunc B i ω)]

private lemma lintegral_hitTrunc_succ (hQ : IsRateMatrix Q) {A : Set ι} {i : ι} (hi : i ∉ A)
    (hq : Q i i ≠ 0) (n : ℕ) :
    ∫⁻ ω, hitTrunc Q A (n + 1) i ω ∂ctmcInputMeasure hQ =
      ENNReal.ofReal (1 / -Q i i) + ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
        ∫⁻ ω, hitTrunc Q A n j ω ∂ctmcInputMeasure hQ := by
  simp_rw [hitTrunc_succ_of_notMem hi]
  rw [lintegral_add_left (measurable_ctmcHoldingTime i 0), lintegral_holding hQ hq,
    lintegral_shift hQ i (measurable_hitTrunc A n)]

omit [DiscreteMeasurableSpace ι] in
private lemma lintegral_hitTrunc_of_mem (hQ : IsRateMatrix Q) {A : Set ι} {i : ι} (hi : i ∈ A)
    (n : ℕ) : ∫⁻ ω, hitTrunc Q A n i ω ∂ctmcInputMeasure hQ = 0 := by
  simp_rw [hitTrunc_of_mem hi]
  exact lintegral_zero

private lemma lintegral_hitTrunc_mul_succ (hQ : IsRateMatrix Q) {A B : Set ι} {i : ι}
    (hi : i ∉ A ∪ B) (hq : Q i i ≠ 0) (n : ℕ) :
    ∫⁻ ω, hitTrunc Q A (n + 1) i ω * hitTrunc Q B (n + 1) i ω ∂ctmcInputMeasure hQ =
      ENNReal.ofReal (2 / (-Q i i) ^ 2) +
        ENNReal.ofReal (1 / -Q i i) * ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
          ∫⁻ ω, hitTrunc Q A n j ω ∂ctmcInputMeasure hQ +
        ENNReal.ofReal (1 / -Q i i) * ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
          ∫⁻ ω, hitTrunc Q B n j ω ∂ctmcInputMeasure hQ +
        ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
          ∫⁻ ω, hitTrunc Q A n j ω * hitTrunc Q B n j ω ∂ctmcInputMeasure hQ := by
  have hiA : i ∉ A := fun h => hi (Or.inl h)
  have hiB : i ∉ B := fun h => hi (Or.inr h)
  have hS : Measurable fun ω : ℕ → (ι → ι) × ℝ => ctmcHoldingTime Q i ω 0 :=
    measurable_ctmcHoldingTime i 0
  have ha : Measurable fun ω : ℕ → (ι → ι) × ℝ =>
      hitTrunc Q A n ((ω 0).1 i) (ctmcShift 1 ω) :=
    measurable_comp_first i (measurable_hitTrunc A n)
  have hb : Measurable fun ω : ℕ → (ι → ι) × ℝ =>
      hitTrunc Q B n ((ω 0).1 i) (ctmcShift 1 ω) :=
    measurable_comp_first i (measurable_hitTrunc B n)
  have hexp : ∀ ω, hitTrunc Q A (n + 1) i ω * hitTrunc Q B (n + 1) i ω =
      ctmcHoldingTime Q i ω 0 * ctmcHoldingTime Q i ω 0 +
        ctmcHoldingTime Q i ω 0 * hitTrunc Q A n ((ω 0).1 i) (ctmcShift 1 ω) +
        ctmcHoldingTime Q i ω 0 * hitTrunc Q B n ((ω 0).1 i) (ctmcShift 1 ω) +
        hitTrunc Q A n ((ω 0).1 i) (ctmcShift 1 ω) *
          hitTrunc Q B n ((ω 0).1 i) (ctmcShift 1 ω) := by
    intro ω
    rw [hitTrunc_succ_of_notMem hiA, hitTrunc_succ_of_notMem hiB]
    ring
  have hab : Measurable fun ω : ℕ → (ι → ι) × ℝ => hitTrunc Q A n ((ω 0).1 i) (ctmcShift 1 ω) *
      hitTrunc Q B n ((ω 0).1 i) (ctmcShift 1 ω) := ha.mul hb
  have hSb : Measurable fun ω : ℕ → (ι → ι) × ℝ => ctmcHoldingTime Q i ω 0 *
      hitTrunc Q B n ((ω 0).1 i) (ctmcShift 1 ω) := hS.mul hb
  have hSa : Measurable fun ω : ℕ → (ι → ι) × ℝ => ctmcHoldingTime Q i ω 0 *
      hitTrunc Q A n ((ω 0).1 i) (ctmcShift 1 ω) := hS.mul ha
  simp_rw [hexp]
  rw [lintegral_add_right _ hab, lintegral_add_right _ hSb, lintegral_add_right _ hSa,
    lintegral_holding_sq hQ hq,
    lintegral_holding_mul hQ hq (measurable_hitTrunc A n),
    lintegral_holding_mul hQ hq (measurable_hitTrunc B n)]
  congr 1
  exact lintegral_shift hQ i (G := fun j ω => hitTrunc Q A n j ω * hitTrunc Q B n j ω)
    fun j => (measurable_hitTrunc A n j).mul (measurable_hitTrunc B n j)

private lemma lintegral_hitTrunc_le (hQ : IsRateMatrix Q) {A : Set ι}
    (hq : ∀ i ∉ A, Q i i ≠ 0) {m : ι → ℝ≥0∞}
    (hm : ∀ i ∉ A, ENNReal.ofReal (1 / -Q i i) + ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * m j
      ≤ m i) (n : ℕ) : ∀ i, ∫⁻ ω, hitTrunc Q A n i ω ∂ctmcInputMeasure hQ ≤ m i := by
  induction n with
  | zero => intro i; simp [hitTrunc_zero]
  | succ n ih =>
    intro i
    by_cases hi : i ∈ A
    · rw [lintegral_hitTrunc_of_mem hQ hi]; exact zero_le
    · rw [lintegral_hitTrunc_succ hQ hi (hq i hi)]
      refine le_trans ?_ (hm i hi)
      gcongr with j
      exact ih j

end Expectation

namespace IsRateMatrix

variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

/-- **Mean hitting time, first-step equation** (compare Norris 1997, §3.3): from `i ∉ A`
with `q i = -Q i i ≠ 0`, `E_i H_A = 1 / q i + ∑ⱼ Π i j E_j H_A` in `ℝ≥0∞`. -/
theorem lintegral_ctmcHittingTime (hQ : IsRateMatrix Q) {A : Set ι} {i : ι} (hi : i ∉ A)
    (hq : Q i i ≠ 0) :
    ∫⁻ ω, ctmcHittingTime Q i A ω ∂ctmcInputMeasure hQ =
      ENNReal.ofReal (1 / -Q i i) + ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
        ∫⁻ ω, ctmcHittingTime Q j A ω ∂ctmcInputMeasure hQ := by
  have h2 : Tendsto (fun n => ∫⁻ ω, hitTrunc Q A (n + 1) i ω ∂ctmcInputMeasure hQ) atTop
      (𝓝 (ENNReal.ofReal (1 / -Q i i) + ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
        ∫⁻ ω, ctmcHittingTime Q j A ω ∂ctmcInputMeasure hQ)) := by
    simp_rw [lintegral_hitTrunc_succ hQ hi hq]
    exact tendsto_const_nhds.add (tendsto_finsetSum _ fun j _ =>
      ENNReal.Tendsto.const_mul (tendsto_lintegral_hitTrunc hQ A j)
        (Or.inr ENNReal.ofReal_ne_top))
  exact tendsto_nhds_unique ((tendsto_lintegral_hitTrunc hQ A i).comp
    (tendsto_add_atTop_nat 1)) h2

/-- From a state of `A`, the mean hitting time of `A` is `0`. -/
theorem lintegral_ctmcHittingTime_of_mem (hQ : IsRateMatrix Q) {A : Set ι} {i : ι}
    (hi : i ∈ A) : ∫⁻ ω, ctmcHittingTime Q i A ω ∂ctmcInputMeasure hQ = 0 := by
  refine tendsto_nhds_unique (tendsto_lintegral_hitTrunc hQ A i) ?_
  simp_rw [lintegral_hitTrunc_of_mem hQ hi]
  exact tendsto_const_nhds

/-- **Minimality of the mean hitting time** (compare Norris 1997, §3.3): if every state off
`A` has a positive exit rate, every `m : ι → ℝ≥0∞` with `1 / q i + ∑ⱼ Π i j m j ≤ m i` off `A`
dominates `E_i H_A`. -/
theorem lintegral_ctmcHittingTime_le (hQ : IsRateMatrix Q) {A : Set ι}
    (hq : ∀ i ∉ A, Q i i ≠ 0) {m : ι → ℝ≥0∞}
    (hm : ∀ i ∉ A, ENNReal.ofReal (1 / -Q i i) + ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * m j
      ≤ m i) (i : ι) :
    ∫⁻ ω, ctmcHittingTime Q i A ω ∂ctmcInputMeasure hQ ≤ m i :=
  le_of_tendsto' (tendsto_lintegral_hitTrunc hQ A i) fun n => lintegral_hitTrunc_le hQ hq hm n i

/-- **Product moment of two hitting times, first-step equation**: from `i ∉ A ∪ B` with
`q i ≠ 0`, `E_i (H_A H_B) = (E_i H_A + E_i H_B) / q i + ∑ⱼ Π i j E_j (H_A H_B)` in `ℝ≥0∞`. -/
theorem lintegral_ctmcHittingTime_mul (hQ : IsRateMatrix Q) {A B : Set ι} {i : ι}
    (hi : i ∉ A ∪ B) (hq : Q i i ≠ 0) :
    ∫⁻ ω, ctmcHittingTime Q i A ω * ctmcHittingTime Q i B ω ∂ctmcInputMeasure hQ =
      ENNReal.ofReal (1 / -Q i i) *
          (∫⁻ ω, ctmcHittingTime Q i A ω ∂ctmcInputMeasure hQ +
            ∫⁻ ω, ctmcHittingTime Q i B ω ∂ctmcInputMeasure hQ) +
        ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
          ∫⁻ ω, ctmcHittingTime Q j A ω * ctmcHittingTime Q j B ω ∂ctmcInputMeasure hQ := by
  have hiA : i ∉ A := fun h => hi (Or.inl h)
  have hiB : i ∉ B := fun h => hi (Or.inr h)
  have hc : Tendsto (fun n : ℕ => ∫⁻ ω, hitTrunc Q A (n + 1) i ω * hitTrunc Q B (n + 1) i ω
      ∂ctmcInputMeasure hQ) atTop (𝓝 (ENNReal.ofReal (2 / (-Q i i) ^ 2) +
        ENNReal.ofReal (1 / -Q i i) * ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
          ∫⁻ ω, ctmcHittingTime Q j A ω ∂ctmcInputMeasure hQ +
        ENNReal.ofReal (1 / -Q i i) * ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
          ∫⁻ ω, ctmcHittingTime Q j B ω ∂ctmcInputMeasure hQ +
        ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
          ∫⁻ ω, ctmcHittingTime Q j A ω * ctmcHittingTime Q j B ω ∂ctmcInputMeasure hQ)) := by
    simp_rw [lintegral_hitTrunc_mul_succ hQ hi hq]
    have hsum : ∀ (G : ℕ → ι → ℝ≥0∞) (L : ι → ℝ≥0∞),
        (∀ j, Tendsto (fun n => G n j) atTop (𝓝 (L j))) →
        Tendsto (fun n => ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * G n j) atTop
          (𝓝 (∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * L j)) :=
      fun G L hG => tendsto_finsetSum _ fun j _ =>
        ENNReal.Tendsto.const_mul (hG j) (Or.inr ENNReal.ofReal_ne_top)
    exact ((tendsto_const_nhds.add (ENNReal.Tendsto.const_mul
      (hsum _ _ fun j => tendsto_lintegral_hitTrunc hQ A j) (Or.inr ENNReal.ofReal_ne_top))).add
      (ENNReal.Tendsto.const_mul (hsum _ _ fun j => tendsto_lintegral_hitTrunc hQ B j)
        (Or.inr ENNReal.ofReal_ne_top))).add
      (hsum _ _ fun j => tendsto_lintegral_hitTrunc_mul hQ A B j)
  rw [tendsto_nhds_unique ((tendsto_lintegral_hitTrunc_mul hQ A B i).comp
    (tendsto_add_atTop_nat 1)) hc, lintegral_ctmcHittingTime hQ hiA hq,
    lintegral_ctmcHittingTime hQ hiB hq]
  have hq' := neg_diag_pos hQ hq
  have h2 : ENNReal.ofReal (2 / (-Q i i) ^ 2) =
      ENNReal.ofReal (1 / -Q i i) * ENNReal.ofReal (1 / -Q i i) +
        ENNReal.ofReal (1 / -Q i i) * ENNReal.ofReal (1 / -Q i i) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
    congr 1
    field_simp
    ring
  rw [h2]
  ring

/-- From a state of `A ∪ B`, the product moment of the hitting times of `A` and `B` is `0`. -/
theorem lintegral_ctmcHittingTime_mul_of_mem (hQ : IsRateMatrix Q) {A B : Set ι} {i : ι}
    (hi : i ∈ A ∪ B) :
    ∫⁻ ω, ctmcHittingTime Q i A ω * ctmcHittingTime Q i B ω ∂ctmcInputMeasure hQ = 0 := by
  refine tendsto_nhds_unique (tendsto_lintegral_hitTrunc_mul hQ A B i) ?_
  simp_rw [hitTrunc_mul_of_mem hi]
  simp

/-- **Minimality of the product moment**: if `mA`, `mB` are supersolutions of the mean
equations of `A` and `B` (as in `lintegral_ctmcHittingTime_le`) and `F` satisfies
`(mA i + mB i) / q i + ∑ⱼ Π i j F j ≤ F i` off `A ∪ B`, then `F` dominates `E_i (H_A H_B)`. -/
theorem lintegral_ctmcHittingTime_mul_le (hQ : IsRateMatrix Q) {A B : Set ι}
    (hqA : ∀ i ∉ A, Q i i ≠ 0) (hqB : ∀ i ∉ B, Q i i ≠ 0) {mA mB F : ι → ℝ≥0∞}
    (hmA : ∀ i ∉ A, ENNReal.ofReal (1 / -Q i i) +
      ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * mA j ≤ mA i)
    (hmB : ∀ i ∉ B, ENNReal.ofReal (1 / -Q i i) +
      ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * mB j ≤ mB i)
    (hF : ∀ i ∉ A ∪ B, ENNReal.ofReal (1 / -Q i i) * (mA i + mB i) +
      ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * F j ≤ F i) (i : ι) :
    ∫⁻ ω, ctmcHittingTime Q i A ω * ctmcHittingTime Q i B ω ∂ctmcInputMeasure hQ ≤ F i := by
  refine le_of_tendsto' (tendsto_lintegral_hitTrunc_mul hQ A B i) fun n => ?_
  induction n generalizing i with
  | zero => simp [hitTrunc_zero]
  | succ n ih =>
    by_cases hi : i ∈ A ∪ B
    · simp_rw [hitTrunc_mul_of_mem hi]
      simp
    · have hiA : i ∉ A := fun h => hi (Or.inl h)
      have hiB : i ∉ B := fun h => hi (Or.inr h)
      have hq := hqA i hiA
      have hq' := neg_diag_pos hQ hq
      rw [lintegral_hitTrunc_mul_succ hQ hi hq]
      refine le_trans ?_ (hF i hi)
      have h2 : ENNReal.ofReal (2 / (-Q i i) ^ 2) =
          ENNReal.ofReal (1 / -Q i i) * ENNReal.ofReal (1 / -Q i i) +
            ENNReal.ofReal (1 / -Q i i) * ENNReal.ofReal (1 / -Q i i) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        field_simp
        ring
      calc _ ≤ ENNReal.ofReal (2 / (-Q i i) ^ 2) +
            ENNReal.ofReal (1 / -Q i i) * ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * mA j +
            ENNReal.ofReal (1 / -Q i i) * ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * mB j +
            ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * F j := by
            have s1 : ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
                ∫⁻ ω, hitTrunc Q A n j ω ∂ctmcInputMeasure hQ ≤
                ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * mA j :=
              Finset.sum_le_sum fun j _ => by gcongr; exact lintegral_hitTrunc_le hQ hqA hmA n j
            have s2 : ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
                ∫⁻ ω, hitTrunc Q B n j ω ∂ctmcInputMeasure hQ ≤
                ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * mB j :=
              Finset.sum_le_sum fun j _ => by gcongr; exact lintegral_hitTrunc_le hQ hqB hmB n j
            have s3 : ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
                ∫⁻ ω, hitTrunc Q A n j ω * hitTrunc Q B n j ω ∂ctmcInputMeasure hQ ≤
                ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * F j :=
              Finset.sum_le_sum fun j _ => by gcongr; exact ih j
            gcongr
        _ = ENNReal.ofReal (1 / -Q i i) * (ENNReal.ofReal (1 / -Q i i) +
              ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * mA j) +
            ENNReal.ofReal (1 / -Q i i) * (ENNReal.ofReal (1 / -Q i i) +
              ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * mB j) +
            ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * F j := by
            rw [h2]; ring
        _ ≤ _ := by
            rw [mul_add (ENNReal.ofReal (1 / -Q i i)) (mA i) (mB i)]
            gcongr
            · exact hmA i hiA
            · exact hmB i hiB

/-- **Backward equations for the mean hitting time** (compare Norris 1997, §3.3): if
`m : ι → ℝ` is nonnegative and `(Q m) i = -1` for `i ∉ A`, then `E_i H_A ≤ m i` (so it is
finite), `E_i H_A = 0` on `A`, and the real vector `E_i H_A` solves the same backward
equations. With uniqueness of the solution, this identifies `E_i H_A`. -/
theorem ctmcHittingTime_backward (hQ : IsRateMatrix Q) {A : Set ι} {m : ι → ℝ}
    (hm0 : ∀ i, 0 ≤ m i) (hm : ∀ i ∉ A, (Q *ᵥ m) i = -1) :
    (∀ i, ∫⁻ ω, ctmcHittingTime Q i A ω ∂ctmcInputMeasure hQ ≤ ENNReal.ofReal (m i)) ∧
      (∀ i ∈ A, (∫⁻ ω, ctmcHittingTime Q i A ω ∂ctmcInputMeasure hQ).toReal = 0) ∧
      ∀ i ∉ A, (Q *ᵥ fun j => (∫⁻ ω, ctmcHittingTime Q j A ω ∂ctmcInputMeasure hQ).toReal) i =
        -1 := by
  have hq : ∀ i ∉ A, Q i i ≠ 0 := fun i hi h0 => by
    have := hm i hi
    rw [mulVec_eq_zero_of_diag hQ h0] at this
    norm_num at this
  have hsup : ∀ i ∉ A, ENNReal.ofReal (1 / -Q i i) +
      ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) * ENNReal.ofReal (m j) ≤ ENNReal.ofReal (m i) := by
    intro i hi
    rw [← ofReal_jump hQ (hq i hi) zero_le_one hm0, ← (eq_jump_iff (hq i hi) m 1).2 (hm i hi)]
  have hle := fun i => lintegral_ctmcHittingTime_le hQ hq hsup i
  have hfin : ∀ j, ∫⁻ ω, ctmcHittingTime Q j A ω ∂ctmcInputMeasure hQ ≠ ∞ :=
    fun j => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle j)
  refine ⟨hle, fun i hi => by rw [lintegral_ctmcHittingTime_of_mem hQ hi]; rfl, fun i hi => ?_⟩
  rw [← eq_jump_iff (hq i hi), lintegral_ctmcHittingTime hQ hi (hq i hi),
    toReal_jump hQ i ENNReal.ofReal_ne_top hfin,
    ENNReal.toReal_ofReal (div_nonneg zero_le_one (neg_diag_pos hQ (hq i hi)).le)]

/-- **Backward equations for the product moment of two hitting times**: let `mA`, `mB`, `f` be
nonnegative with `(Q mA) i = -1` off `A`, `(Q mB) i = -1` off `B` and
`(Q f) i = -(mA i + mB i)` off `A ∪ B`. Then `E_i (H_A H_B) ≤ f i` (so it is finite), it is `0`
on `A ∪ B`, and its real part `p` solves `(Q p) i = -(E_i H_A + E_i H_B)` off `A ∪ B`. -/
theorem ctmcHittingTime_mul_backward (hQ : IsRateMatrix Q) {A B : Set ι} {mA mB f : ι → ℝ}
    (hmA0 : ∀ i, 0 ≤ mA i) (hmB0 : ∀ i, 0 ≤ mB i) (hf0 : ∀ i, 0 ≤ f i)
    (hmA : ∀ i ∉ A, (Q *ᵥ mA) i = -1) (hmB : ∀ i ∉ B, (Q *ᵥ mB) i = -1)
    (hf : ∀ i ∉ A ∪ B, (Q *ᵥ f) i = -(mA i + mB i)) :
    (∀ i, ∫⁻ ω, ctmcHittingTime Q i A ω * ctmcHittingTime Q i B ω ∂ctmcInputMeasure hQ ≤
        ENNReal.ofReal (f i)) ∧
      (∀ i ∈ A ∪ B, (∫⁻ ω, ctmcHittingTime Q i A ω * ctmcHittingTime Q i B ω
        ∂ctmcInputMeasure hQ).toReal = 0) ∧
      ∀ i ∉ A ∪ B, (Q *ᵥ fun j => (∫⁻ ω, ctmcHittingTime Q j A ω * ctmcHittingTime Q j B ω
        ∂ctmcInputMeasure hQ).toReal) i =
        -((∫⁻ ω, ctmcHittingTime Q i A ω ∂ctmcInputMeasure hQ).toReal +
          (∫⁻ ω, ctmcHittingTime Q i B ω ∂ctmcInputMeasure hQ).toReal) := by
  have hqA : ∀ i ∉ A, Q i i ≠ 0 := fun i hi h0 => by
    have := hmA i hi
    rw [mulVec_eq_zero_of_diag hQ h0] at this
    norm_num at this
  have hqB : ∀ i ∉ B, Q i i ≠ 0 := fun i hi h0 => by
    have := hmB i hi
    rw [mulVec_eq_zero_of_diag hQ h0] at this
    norm_num at this
  have hsupA : ∀ i ∉ A, ENNReal.ofReal (1 / -Q i i) + ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
      ENNReal.ofReal (mA j) ≤ ENNReal.ofReal (mA i) := by
    intro i hi
    rw [← ofReal_jump hQ (hqA i hi) zero_le_one hmA0, ← (eq_jump_iff (hqA i hi) mA 1).2 (hmA i hi)]
  have hsupB : ∀ i ∉ B, ENNReal.ofReal (1 / -Q i i) + ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
      ENNReal.ofReal (mB j) ≤ ENNReal.ofReal (mB i) := by
    intro i hi
    rw [← ofReal_jump hQ (hqB i hi) zero_le_one hmB0, ← (eq_jump_iff (hqB i hi) mB 1).2 (hmB i hi)]
  have hsupF : ∀ i ∉ A ∪ B, ENNReal.ofReal (1 / -Q i i) *
      (ENNReal.ofReal (mA i) + ENNReal.ofReal (mB i)) + ∑ j, ENNReal.ofReal (ctmcJumpMatrix Q i j) *
      ENNReal.ofReal (f j) ≤ ENNReal.ofReal (f i) := by
    intro i hi
    have hq := hqA i fun h => hi (Or.inl h)
    have hq' := neg_diag_pos hQ hq
    rw [← ENNReal.ofReal_add (hmA0 i) (hmB0 i), ← ENNReal.ofReal_mul (by positivity),
      show 1 / -Q i i * (mA i + mB i) = (mA i + mB i) / -Q i i by ring,
      ← ofReal_jump hQ hq (add_nonneg (hmA0 i) (hmB0 i)) hf0,
      ← (eq_jump_iff hq f (mA i + mB i)).2 (hf i hi)]
  have hle := fun i => lintegral_ctmcHittingTime_mul_le hQ hqA hqB hsupA hsupB hsupF i
  have hfin : ∀ j, ∫⁻ ω, ctmcHittingTime Q j A ω * ctmcHittingTime Q j B ω
      ∂ctmcInputMeasure hQ ≠ ∞ := fun j => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle j)
  have hfinA : ∀ j, ∫⁻ ω, ctmcHittingTime Q j A ω ∂ctmcInputMeasure hQ ≠ ∞ := fun j =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_ctmcHittingTime_le hQ hqA hsupA j)
  have hfinB : ∀ j, ∫⁻ ω, ctmcHittingTime Q j B ω ∂ctmcInputMeasure hQ ≠ ∞ := fun j =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_ctmcHittingTime_le hQ hqB hsupB j)
  refine ⟨hle, fun i hi => by rw [lintegral_ctmcHittingTime_mul_of_mem hQ hi]; rfl,
    fun i hi => ?_⟩
  have hq := hqA i fun h => hi (Or.inl h)
  rw [← eq_jump_iff hq, lintegral_ctmcHittingTime_mul hQ hi hq,
    toReal_jump hQ i (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨hfinA i, hfinB i⟩)) hfin, ENNReal.toReal_mul,
    ENNReal.toReal_add (hfinA i) (hfinB i),
    ENNReal.toReal_ofReal (div_nonneg zero_le_one (neg_diag_pos hQ hq).le)]
  ring

end IsRateMatrix

end ProbabilityTheory
