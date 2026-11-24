/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.BlackwellApproachabilityAlmostSure
import Mathlib.Algebra.Order.Chebyshev

/-! # Asymptotic calibration of randomised forecasts

A forecaster announces each day a probability of rain from the grid `0, 1/k, …, 1`; it is
calibrated if, among the days with forecast `i / k`, it rained on a fraction close to `i / k`.
No deterministic forecaster is calibrated against every sequence of outcomes (Oakes 1985;
Dawid 1985), but a randomised one can be, against an adaptive Nature that sees the past but not
the current randomisation (Foster and Vohra 1998, Theorem 1).

## Main results

* `calibrationScore`: the calibration score of a sequence of binary forecasts.
* `exists_calibrated_forecast`: for every `ε > 0` there are a grid and a randomised forecasting
  rule whose calibration score after `t` rounds is below `ε` with probability greater than
  `1 − ε` for all large `t`, against every adaptive Nature.

## Proof outline

Calibration follows from Blackwell's approachability theorem (`blackwell_approachability`, in
`MathlibExt.GameTheory.BlackwellApproachabilityAlmostSure`), as in Foster 1999, here with a
payoff and a target set adapted to the score of Foster and Vohra.

* Payoff: the forecast `i / k` and the outcome `x ∈ {0, 1}` pay `(x − i / k) eᵢ ∈ ℝᵏ⁺¹`. After
  `t` rounds, the `i`-th coordinate of the average payoff is `Dᵢ = (N(i) − (i / k) n(i)) / t`,
  where `n(i)` counts the rounds forecast `i / k` and `N(i)` those of them with outcome `1`.
* Score: since `|N(i) − (i / k) n(i)| ≤ n(i)`, the term `(N(i) − (i / k) n(i))² / (n(i) t)` of
  the score is at most `|Dᵢ|`, so `C_t ≤ ∑ᵢ |Dᵢ| ≤ √(k + 1) ‖D‖` by Cauchy–Schwarz.
* Half-space condition: let `C` be the closed Euclidean ball of radius `1 / k` about `0`, and
  let the half-space `{y | ⟪λ, y⟫ ≤ ρ}` contain `C`, so that `ρ ≥ 0` and `ρ ≥ |λⱼ| / k` for every
  `j`. If `λₖ ≥ 0`, the forecast `1` gives `⟪λ, (x − 1) eₖ⟫ ≤ 0`; if `λ₀ ≤ 0`, the forecast `0`
  gives `⟪λ, x e₀⟫ ≤ 0`. Otherwise `λ` changes sign between two adjacent forecasts,
  `λᵢ > 0 ≥ λᵢ₊₁`, and forecasting `i / k` and `(i + 1) / k` with probabilities proportional to
  `−λᵢ₊₁` and `λᵢ` gives, for both outcomes, the expected value
  `λᵢ (−λᵢ₊₁) / (k (λᵢ − λᵢ₊₁)) ≤ −λᵢ₊₁ / k ≤ ρ`.
* Blackwell's theorem gives a strategy `σ` of the average payoff under which `dist(D, C) → 0`
  almost surely; the rule forecasts with `σ` applied to the average payoff of the history. Then
  eventually `‖D‖ < 2 / k`, so `C_t < 2 √(k + 1) / k ≤ ε` once `k > 8 / ε²`.
* Almost-sure convergence gives convergence in probability: the events
  `{C_s < ε for every s ≥ t}` increase with `t` to an event of probability `1`.

## Implementation notes

`calibrationScore` and `exists_calibrated_forecast` keep the full names, statements and
docstrings of the former wanted declarations, so their namespace is `CalibrationWanted`. The
hypothesis of the theorem on the first round is not used, as Blackwell's theorem allows an
arbitrary first round. Continuity of measures from below holds for every increasing sequence of
sets, so the events about the score need no measurability argument.

## References

* D. P. Foster and R. V. Vohra, "Asymptotic calibration", Biometrika 85(2) (1998), 379–390:
  §2 (calibration score), §3 (Rules 1–3, Definition of ε-calibration), Theorem 1 (§5).
* D. P. Foster, "A proof of calibration via Blackwell's approachability theorem", Games Econom.
  Behav. 29(1–2) (1999), 73–78.
* D. Blackwell, "An analog of the minimax theorem for vector payoffs", Pacific J. Math. 6
  (1956), 1–8: Theorem 1.
* D. Oakes, "Self-calibrating priors do not exist", J. Amer. Statist. Assoc. 80(390) (1985), 339,
  and A. P. Dawid, "Comment", J. Amer. Statist. Assoc. 80(390) (1985), 340–341.
-/

@[expose] public section

namespace MathlibExt.GameTheory.CalibrationWanted

open MeasureTheory Filter Topology Finset
open MathlibExt.GameTheory.BlackwellApproachabilityWanted (historySigma)
open MathlibExt.GameTheory.BlackwellApproachability (average)

/-- The **calibration score** of binary forecasts (Foster and Vohra 1998, §2). The forecasts
`f s ∈ {0, 1/k, …, 1}` (the index `i` standing for `i / k`, for a grid size `k ≥ 1`) are made for
the outcomes `x s` of `t ≥ 1` rounds; with `n(i)` the number of rounds forecast `i / k` and `ρ(i)`
the fraction of those rounds with outcome `1`, `C_t = ∑ᵢ (ρ(i) − i / k)² n(i) / t`. For `t = 0`
every forecaster would score `0`, and for `k = 0` the grid would not be defined. -/
noncomputable def calibrationScore {k t : ℕ} [NeZero k] [NeZero t] (f : Fin t → Fin (k + 1))
    (x : Fin t → Bool) : ℝ :=
  ∑ i : Fin (k + 1),
    ((#{s | f s = i ∧ x s = true} : ℝ) / #{s | f s = i} - (i : ℝ) / k) ^ 2 *
      #{s | f s = i} / t

/-- The vector payoff of a forecast `i / k` and an outcome `b`: `(b − i / k) eᵢ`. -/
private noncomputable def calibrationPayoff (k : ℕ) (i : Fin (k + 1)) (b : Bool) :
    EuclideanSpace ℝ (Fin (k + 1)) :=
  EuclideanSpace.single i ((if b then 1 else 0) - (i : ℝ) / k)

/-- The inner product of `λ` with an expected payoff. -/
private lemma inner_sum_calibrationPayoff (k : ℕ) (lam : EuclideanSpace ℝ (Fin (k + 1)))
    (q : Fin (k + 1) → ℝ) (b : Bool) :
    inner ℝ lam (∑ a, q a • calibrationPayoff k a b) =
      ∑ a, q a * (((if b then 1 else 0) - (a : ℝ) / k) * lam a) := by
  simp [calibrationPayoff, inner_sum, real_inner_smul_right, EuclideanSpace.inner_single_right]

/-- Every closed half-space containing the closed ball of radius `1 / k` about `0` is enforceable
for the calibration payoff: a forecast at an end of the grid, or a mixture of two adjacent
forecasts, keeps the expected payoff in it against both outcomes. -/
private lemma enforceable (k : ℕ) [NeZero k] (lam : EuclideanSpace ℝ (Fin (k + 1))) (ρ : ℝ)
    (hρ : ∀ c ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) (1 / k),
      inner ℝ lam c ≤ ρ) :
    ∃ q : Convexity.StdSimplex ℝ (Fin (k + 1)), ∀ b,
      inner ℝ lam (∑ a, q.weights a • calibrationPayoff k a b) ≤ ρ := by
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne k)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_ne (Nat.cast_nonneg k) hk.symm
  have hρ0 : 0 ≤ ρ := by
    simpa using hρ 0 (Metric.mem_closedBall_self (by positivity))
  have hb : ∀ b : Bool, (0 : ℝ) ≤ (if b then 1 else 0) ∧ (if b then (1 : ℝ) else 0) ≤ 1 := by
    intro b; cases b <;> norm_num
  by_cases hlast : 0 ≤ lam (Fin.last k)
  · -- forecast `1`
    refine ⟨.single (Fin.last k), fun b => ?_⟩
    rw [inner_sum_calibrationPayoff]
    simp only [Convexity.StdSimplex.weights_single, Finsupp.single_apply]
    rw [Finset.sum_eq_single (Fin.last k) (fun a _ ha => by simp [Ne.symm ha])
      (by simp)]
    simp only [ite_true, one_mul, Fin.val_last, div_self hk]
    have := hb b
    nlinarith
  by_cases hzero : lam 0 ≤ 0
  · -- forecast `0`
    refine ⟨.single 0, fun b => ?_⟩
    rw [inner_sum_calibrationPayoff]
    simp only [Convexity.StdSimplex.weights_single, Finsupp.single_apply]
    rw [Finset.sum_eq_single 0 (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp only [ite_true, one_mul, Fin.val_zero, Nat.cast_zero, zero_div, sub_zero]
    have := hb b
    nlinarith
  push Not at hlast hzero
  -- a sign change of `λ` between two adjacent forecasts
  obtain ⟨i, hi, hi'⟩ : ∃ i : Fin k, 0 < lam i.castSucc ∧ lam i.succ ≤ 0 := by
    by_contra h
    push Not at h
    exact (Fin.induction (motive := fun j => 0 < lam j) hzero h (Fin.last k)).not_ge hlast.le
  set u := lam i.castSucc
  set w := lam i.succ
  have hD : 0 < u - w := by linarith
  refine ⟨.duple i.castSucc i.succ (s := -w / (u - w)) (t := u / (u - w))
    (div_nonneg (by linarith) hD.le) (div_nonneg hi.le hD.le) (by field_simp; ring), fun b => ?_⟩
  rw [inner_sum_calibrationPayoff]
  simp only [Convexity.StdSimplex.weights_duple, Finsupp.add_apply, Finsupp.single_apply,
    add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single i.castSucc (fun a _ ha => by simp [Ne.symm ha]) (by simp),
    Finset.sum_eq_single i.succ (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
  simp only [ite_true, Fin.val_castSucc, Fin.val_succ]
  -- the value is `(−w / k) (u / (u − w)) ≤ −w / k = ⟪λ, −eᵢ₊₁ / k⟫ ≤ ρ`
  have hval : -w / (u - w) * (((if b then 1 else 0) - ((i : ℕ) : ℝ) / k) * u) +
      u / (u - w) * (((if b then 1 else 0) - (((i : ℕ) + 1 : ℕ) : ℝ) / k) * w) =
      -w / k * (u / (u - w)) := by
    push_cast
    field_simp
    ring
  rw [hval]
  have hc := hρ (EuclideanSpace.single i.succ (-1 / k)) (by
    rw [mem_closedBall_zero_iff, PiLp.norm_single, Real.norm_eq_abs, abs_div, abs_neg, abs_one,
      abs_of_pos hk0])
  rw [EuclideanSpace.inner_single_right] at hc
  simp only [conj_trivial] at hc
  calc -w / k * (u / (u - w)) ≤ -w / k * 1 := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (by linarith) hk0.le)
        rw [div_le_one hD]
        linarith
    _ = -1 / k * w := by ring
    _ ≤ ρ := hc

/-- For counts `n₁ ≤ n` and `p ∈ [0, 1]`, `(n₁ / n − p)² n / T ≤ |(n₁ − p n) / T|`: the
contribution of one forecast to the calibration score is at most the absolute value of the
corresponding coordinate of the average payoff. -/
private lemma sq_mul_div_le {n₁ n : ℕ} {p T : ℝ} (h : n₁ ≤ n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hT : 0 < T) : ((n₁ : ℝ) / n - p) ^ 2 * n / T ≤ |T⁻¹ * (n₁ - p * n)| := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.le_zero.1 h]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h' : (n₁ : ℝ) ≤ n := by exact_mod_cast h
  have habs : |(n₁ : ℝ) - p * n| ≤ n := by
    rw [abs_le]
    constructor <;> nlinarith [(Nat.cast_nonneg n₁ : (0 : ℝ) ≤ n₁)]
  rw [abs_mul, abs_inv, abs_of_pos hT]
  have key : ((n₁ : ℝ) / n - p) ^ 2 * n = |(n₁ : ℝ) - p * n| ^ 2 / n := by
    rw [sq_abs]
    field_simp
  rw [key, div_div, inv_mul_eq_div, div_le_div_iff₀ (by positivity) hT, sq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)

/-- The calibration score is at most the `ℓ¹` norm of the average payoff. -/
private lemma calibrationScore_le {k T : ℕ} [NeZero k] [NeZero T] (f : Fin T → Fin (k + 1))
    (x : Fin T → Bool) :
    calibrationScore f x ≤ ∑ i, |((T : ℝ)⁻¹ • ∑ s, calibrationPayoff k (f s) (x s)) i| := by
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (NeZero.pos k)
  have hT : (0 : ℝ) < T := Nat.cast_pos.2 (NeZero.pos T)
  refine Finset.sum_le_sum fun i _ => ?_
  have hcoord : ((T : ℝ)⁻¹ • ∑ s, calibrationPayoff k (f s) (x s)) i =
      (T : ℝ)⁻¹ * ((#{s | f s = i ∧ x s = true} : ℝ) - (i : ℝ) / k * #{s | f s = i}) := by
    simp only [PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply, calibrationPayoff,
      PiLp.single_apply]
    congr 1
    have hterm : ∀ s, (if i = f s then (if x s then (1 : ℝ) else 0) - ((f s : ℕ) : ℝ) / k
        else 0) = (if f s = i ∧ x s = true then 1 else 0) - (i : ℝ) / k *
          (if f s = i then 1 else 0) := by
      intro s
      by_cases h : f s = i
      · subst h
        cases x s <;> simp
      · simp [h, Ne.symm h]
    simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  rw [hcoord]
  refine sq_mul_div_le ?_ (by positivity) ?_ hT
  · exact Finset.card_le_card fun s => by simp +contextual
  · rw [div_le_one hk0]
    exact_mod_cast Nat.lt_succ_iff.1 i.isLt

/-- The average of the first `n` terms of a sequence, as a sum over `Fin n`. -/
private lemma average_eq_sum_fin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (y : ℕ → E) (n : ℕ) : average y n = (n : ℝ)⁻¹ • ∑ s : Fin n, y s := by
  rw [average, Fin.sum_univ_eq_sum_range]

/-- **Asymptotic calibration** (Foster and Vohra 1998, Theorem 1, with §3's definition of
`ε`-calibration against an adaptive adversary). For every `ε > 0` there are a grid size `k` and a
randomised forecasting rule `μ`, choosing a distribution on the forecasts `0, 1/k, …, 1` from the
history, such that against every Nature, who chooses each outcome knowing the past but not the
current randomisation, the calibration score after `t` rounds is below `ε` with probability
greater than `1 − ε` for all large `t`. This is weaker than Foster and Vohra's `ε`-calibration,
`lim_t Pr(C_t < ε) > 1 − ε`, which implies it; it does not require the limit to exist. The score
is taken after `t + 1` rounds, so that the history is never empty. -/
theorem exists_calibrated_forecast {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∃ _ : NeZero k,
    ∃ μ : ∀ t : ℕ, (Fin t → Fin (k + 1) × Bool) → Convexity.StdSimplex ℝ (Fin (k + 1)),
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : ℕ → Ω → Fin (k + 1) × Bool), (∀ n z, MeasurableSet {ω | Z n ω = z}) →
        (∀ i b, P.real {ω | Z 0 ω = (i, b)} = (μ 0 Fin.elim0).weights i *
          P.real {ω | (Z 0 ω).2 = b}) →
        (∀ n i b,
          P[{ω | Z (n + 1) ω = (i, b)}.indicator (fun _ => (1 : ℝ)) | historySigma Z n] =ᵐ[P]
            fun ω => (μ (n + 1) (fun s => Z s ω)).weights i *
              P[{ω | (Z (n + 1) ω).2 = b}.indicator (fun _ => (1 : ℝ)) | historySigma Z n] ω) →
        ∀ᶠ t in atTop, 1 - ε < P.real {ω |
          calibrationScore (fun s : Fin (t + 1) => (Z s ω).1) (fun s => (Z s ω).2) < ε} := by
  -- the grid size: `k > 8 / ε²`
  obtain ⟨k, hk⟩ := exists_nat_gt (8 / ε ^ 2)
  have hk0 : (0 : ℝ) < k := (by positivity : (0 : ℝ) < 8 / ε ^ 2).trans hk
  have : NeZero k := ⟨by exact_mod_cast hk0.ne'⟩
  -- Blackwell's theorem for the calibration payoff and the ball of radius `1 / k`
  set C := Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k + 1))) (1 / k)
  have hCne : C.Nonempty := ⟨0, Metric.mem_closedBall_self (by positivity)⟩
  obtain ⟨σ, hσ⟩ := MathlibExt.GameTheory.BlackwellApproachabilityWanted.blackwell_approachability
    (calibrationPayoff k) hCne Metric.isClosed_closedBall (convex_closedBall _ _) (enforceable k)
  refine ⟨k, inferInstance, fun t h => σ ((t : ℝ)⁻¹ • ∑ s, calibrationPayoff k (h s).1 (h s).2), ?_⟩
  intro Ω _ P _ Z hZ _ hlaw
  set y : Ω → ℕ → EuclideanSpace ℝ (Fin (k + 1)) := fun ω j =>
    calibrationPayoff k (Z j ω).1 (Z j ω).2
  have hconv := hσ P Z hZ fun n a b => by
    simpa only [average_eq_sum_fin] using hlaw n a b
  -- almost surely, the score is eventually below `ε`
  have hev : ∀ᵐ ω ∂P, ∀ᶠ t in atTop,
      calibrationScore (fun s : Fin (t + 1) => (Z s ω).1) (fun s => (Z s ω).2) < ε := by
    filter_upwards [hconv] with ω hω
    have h1 : ∀ᶠ n in atTop, Metric.infDist (average (y ω) n) C < 1 / k :=
      hω.eventually (gt_mem_nhds (by positivity))
    filter_upwards [(tendsto_add_atTop_nat 1).eventually h1] with t ht
    obtain ⟨c, hc, hdist⟩ := (Metric.infDist_lt_iff hCne).1 ht
    have hcn : ‖c‖ ≤ 1 / k := mem_closedBall_zero_iff.1 hc
    have hnorm : ‖average (y ω) (t + 1)‖ < 2 / k := by
      have := norm_le_norm_add_norm_sub' (average (y ω) (t + 1)) c
      rw [dist_eq_norm] at hdist
      have h2 : (2 : ℝ) / k = 1 / k + 1 / k := by ring
      linarith
    have hscore := calibrationScore_le (fun s : Fin (t + 1) => (Z s ω).1) (fun s => (Z s ω).2)
    rw [← average_eq_sum_fin (y ω)] at hscore
    set S := ∑ i, |average (y ω) (t + 1) i|
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hS : S ^ 2 < ε ^ 2 := by
      have h8 : 8 / k < ε ^ 2 := by
        rw [div_lt_iff₀ hk0]
        rw [div_lt_iff₀ (by positivity)] at hk
        linarith
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne k)
      have hCS : S ^ 2 ≤ (k + 1) * ‖average (y ω) (t + 1)‖ ^ 2 := by
        have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun i => |average (y ω) (t + 1) i|)
        simp only [sq_abs, Finset.card_univ, Fintype.card_fin] at h
        rw [EuclideanSpace.real_norm_sq_eq]
        exact_mod_cast h
      calc S ^ 2 ≤ (k + 1) * ‖average (y ω) (t + 1)‖ ^ 2 := hCS
        _ < (k + 1) * (2 / k) ^ 2 := by
            gcongr
        _ ≤ 8 / k := by
            rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) hk0]
            nlinarith
        _ < ε ^ 2 := h8
    exact hscore.trans_lt (lt_of_pow_lt_pow_left₀ 2 hε.le hS)
  -- almost-sure convergence gives convergence in probability
  set A : ℕ → Set Ω := fun t => {ω |
    calibrationScore (fun s : Fin (t + 1) => (Z s ω).1) (fun s => (Z s ω).2) < ε}
  set B : ℕ → Set Ω := fun t => ⋂ s ≥ t, A s
  have hB : Monotone B := fun t t' htt' =>
    Set.iInter₂_mono' fun s hs => ⟨s, htt'.trans hs, le_rfl⟩
  have hBA : ∀ t, B t ⊆ A t := fun t => Set.iInter₂_subset t le_rfl
  have hU : P (⋃ t, B t) = 1 := by
    have hmem : ∀ᵐ ω ∂P, ω ∈ ⋃ t, B t := by
      filter_upwards [hev] with ω hω
      obtain ⟨t, ht⟩ := eventually_atTop.1 hω
      exact Set.mem_iUnion.2 ⟨t, Set.mem_iInter₂.2 ht⟩
    rw [measure_congr (ae_eq_univ.2 (ae_iff.1 hmem)), measure_univ]
  have hlim : Tendsto (fun t => P.real (B t)) atTop (𝓝 1) := by
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp
      (hU ▸ tendsto_measure_iUnion_atTop (μ := P) hB)
    simpa [Function.comp_def, measureReal_def] using this
  filter_upwards [hlim.eventually (lt_mem_nhds (by linarith : 1 - ε < 1))] with t ht
  exact ht.trans_le (measureReal_mono (hBA t))

end MathlibExt.GameTheory.CalibrationWanted
