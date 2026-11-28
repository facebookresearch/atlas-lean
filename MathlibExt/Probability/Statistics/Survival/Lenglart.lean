/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DoobLpInequality
public import MathlibExt.Probability.Statistics.Survival.CoxCountingProcessConditions
public import MathlibExt.Probability.Statistics.Survival.CoxAsymptotics

/-!
# Lenglart's inequality and the Andersen–Gill hypotheses from counting-process conditions

Andersen and Gill (1982) derive consistency and asymptotic normality of the Cox estimator from
two limit statements, which `CoxAsymptotics` (T145) takes as hypotheses: the score CLT
`Uₙ(β₀) / √n ⟶ N(0, v)` (`hscore`) and the uniform convergence in probability of `Iₙ(b) / n` near
`β₀` to a function `i` continuous at `β₀` (`hinfo`, `hi`). `CoxCountingProcessConditions` (T159)
reduces both, on a discrete time grid, to one hypothesis `hcomp`: the information compensator
`(1/n) ∑ₖ Δα V(b) S⁽⁰⁾(β₀)` converges uniformly in probability to `i`. This file completes the
derivation and proves Lenglart's inequality in its general form.

## Main results

**Lenglart's inequality** (discrete time).

* `measure_le_sup_le` (**Lenglart's domination inequality**): if a nonnegative adapted process
  `X` is dominated by a predictable nondecreasing process `A` with `A 0 = 0`, in the sense
  `E X_τ ≤ E A_τ` for every stopping time `τ ≤ K`, then for `ε, η > 0`,
  `P(max_{k ≤ K} X_k ≥ ε) ≤ E[A_K ∧ η] / ε + P(A_K ≥ η)`.
* `measure_le_sup_le_of_submartingale`: the same when `A - X` is a submartingale and `X 0 = 0`
  (optional stopping supplies the domination).
* `martingale_sq_sub_predictableQuadraticVariation`: `M² - ⟨M⟩` is a martingale.
* `measure_le_sup_abs_le_of_martingale` (maximal form for martingales):
  `P(max_{k ≤ K} |M_k| ≥ ε) ≤ η / ε² + P(⟨M⟩_K ≥ η)` for a square-integrable martingale with
  `M 0 = 0`. `CoxCountingProcessConditions.measure_le_abs_sum_le` is the terminal-time form
  (`|M_K|` in place of the running maximum).

**The law of large numbers step and the Andersen–Gill theorems.**

* `IsAndersenGillRegular`: the discrete form of Andersen–Gill's Condition B and the finiteness of
  the cumulative baseline hazard. For deterministic `s n j k b`:
  `max_{k < K n} sup_{b ∈ [β₀ - r, β₀ + r]} |S⁽ʲ⁾(b, k) / n - s n j k b| → 0` in probability for
  `j = 0, 1, 2`, `s n 0 k b ≥ κ > 0`, `∑ₖ Δα ≤ Λ`, and the deterministic compensator
  `∑ₖ Δα v(b) s⁽⁰⁾(β₀)`, with `v = s⁽²⁾ / s⁽⁰⁾ - (s⁽¹⁾ / s⁽⁰⁾)²` (`limVar`), converges to `i`
  uniformly on the interval.
* `tendsto_measure_exists_infoCompensator`: these conditions imply T159's `hcomp`.
* `continuousAt_of_isAndersenGillRegular`: the limit `i` is Lipschitz on the interval, hence
  continuous at `β₀` (T145's `hi` is derived, not assumed).
* `andersenGill_hypotheses_of_isAndersenGillRegular`: T145's `hscore`, `hinfo` and `hi` from
  `IsCoxCountingProcess` and `IsAndersenGillRegular`.
* `tendstoInMeasure_coxMPLE_of_isAndersenGillRegular` (consistency),
  `tendstoInDistribution_coxMPLE_gaussian_of_isAndersenGillRegular` (asymptotic normality,
  `√n (βhat - β₀) ⟶ N(0, v⁻¹)`), `tendsto_coverage_cox_waldInterval_of_isAndersenGillRegular`
  (Wald coverage): T145's Theorems 3.2 and 3.3 with every limit hypothesis replaced by the
  counting-process conditions.

## Proof

Lenglart: stop at `ρ`, the first `k ≤ K` with `X_k ≥ ε` or `A_{k+1} ≥ η` (a stopping time
because `A` is predictable). Before `ρ` the process `A` stays below `η`, so `A_ρ ≤ A_K ∧ η`; on
`{max X ≥ ε, A_K < η}` one has `X_ρ ≥ ε`. Markov's inequality and domination at `ρ` finish.

Law of large numbers: `(x₀, x₁, x₂, y) ↦ (x₂ / x₀ - (x₁ / x₀)²) y` is uniformly continuous on a
compact box with `x₀ ≥ κ / 2`. The normalized sums `S⁽ʲ⁾ / n` lie in that box (bounded
covariates), so uniform closeness of `S⁽ʲ⁾ / n` to `s` gives closeness of each step
`V(b) S⁽⁰⁾(β₀) / n` to `v(b) s⁽⁰⁾(β₀)`, and summing against `Δα` costs a factor `Λ`. Continuity of
`i`: `b ↦ V(b)` is `6 B³`-Lipschitz (T159), so the random compensators are uniformly Lipschitz,
and so is their limit in probability.

## What is weakened or deferred

* The model is T159's discrete-time grid model with its restrictions (no ties, at most one event
  per subject, bounded time-fixed scalar covariates); see `CoxCountingProcessConditions`.
* The deterministic compensator limit (`tendsto_det`) is a hypothesis: on a grid that changes
  with `n`, it is the convergence of the Riemann sums `∑ₖ Δα v s⁽⁰⁾` to
  `∫ v(b, t) s⁽⁰⁾(β₀, t) λ₀(t) dt`, which is real analysis about the chosen grid, not probability.
  The deterministic `s` may depend on `n`; the time-indexed form `s j b (τₙₖ)` of Andersen–Gill
  is a special case.
* Lenglart's inequality is proved in discrete time with predictable `A`, not in continuous time.
* No fixture exhibits `IsCoxCountingProcess` and `IsAndersenGillRegular` jointly with `v > 0`
  (the tests check each condition group separately).

## References

* E. Lenglart, *Relation de domination entre deux processus*, Ann. Inst. H. Poincaré 13 (1977),
  171–179.
* P. K. Andersen and R. D. Gill, *Cox's regression model for counting processes: a large sample
  study*, Ann. Statist. 10 (1982), 1100–1120, Condition B and Theorems 3.2, 3.3.
* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Section II.4.1 and Theorem VII.2.2.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.Lenglart

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open MathlibExt.Probability.Statistics.CoxPartialLikelihood
open MathlibExt.Probability.Statistics.CoxCountingProcessConditions

/-! ### Lenglart's inequality -/

section Lenglart

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℕ m0}

/-- **Lenglart's domination inequality** (discrete time, predictable dominating process). Let `X` be
adapted and almost surely nonnegative and `A` predictable (`A (k + 1)` is `F k`-measurable), almost
surely nondecreasing, with `A 0 = 0` almost surely. If `X` is dominated by `A` up to `K`,
`E X_τ ≤ E A_τ` for every stopping time `τ ≤ K`, then for `ε, η > 0`
`P(max_{k ≤ K} X_k ≥ ε) ≤ E[A_K ∧ η] / ε + P(A_K ≥ η)`. -/
theorem measure_le_sup_le {X A : ℕ → Ω → ℝ} (K : ℕ)
    (hX : Adapted F X) (hA : ∀ k, Measurable[F k] (A (k + 1)))
    (hXnn : ∀ᵐ ω ∂P, ∀ k, 0 ≤ X k ω) (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hAmono : ∀ᵐ ω ∂P, Monotone fun k => A k ω)
    (hXint : ∀ k, Integrable (X k) P) (hAint : ∀ k, Integrable (A k) P)
    (hdom : ∀ τ : Ω → WithTop ℕ, IsStoppingTime F τ → (∀ ω, τ ω ≤ K) →
      ∫ ω, stoppedValue X τ ω ∂P ≤ ∫ ω, stoppedValue A τ ω ∂P)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    P {ω | ε ≤ (range (K + 1)).sup' nonempty_range_add_one fun k => X k ω} ≤
      ENNReal.ofReal ((∫ ω, min (A K ω) η ∂P) / ε) + P {ω | η ≤ A K ω} := by
  set u : ℕ → Ω → ℝ × ℝ := fun k ω => (X k ω, A (k + 1) ω) with hu
  set s : Set (ℝ × ℝ) := {p | ε ≤ p.1 ∨ η ≤ p.2} with hs
  have hsm : MeasurableSet s :=
    ((isClosed_le continuous_const continuous_fst).union
      (isClosed_le continuous_const continuous_snd)).measurableSet
  have huad : Adapted F u := fun k => (hX k).prodMk (hA k)
  set ρ : Ω → ℕ := hittingBtwn u s 0 K with hρ
  have hρst : IsStoppingTime F (fun ω => (ρ ω : WithTop ℕ)) :=
    huad.isStoppingTime_hittingBtwn hsm
  have hρK : ∀ ω, ρ ω ≤ K := fun ω => hittingBtwn_le ω
  have hρK' : ∀ ω, (ρ ω : WithTop ℕ) ≤ K := fun ω => by exact_mod_cast hρK ω
  have hsv : ∀ Y : ℕ → Ω → ℝ, stoppedValue Y (fun ω => (ρ ω : WithTop ℕ)) =
      fun ω => Y (ρ ω) ω := fun Y => rfl
  -- the dominating process at `ρ` stays below `min (A K) η`
  have hAρ : ∀ᵐ ω ∂P, A (ρ ω) ω ≤ min (A K ω) η := by
    filter_upwards [hA0, hAmono] with ω h0 hmono
    refine le_min (hmono (hρK ω)) ?_
    by_cases h : ρ ω = 0
    · rw [h, h0]
      exact hη.le
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero h
      have hns : u j ω ∉ s :=
        notMem_of_lt_hittingBtwn (show j < ρ ω by omega) (Nat.zero_le j)
      simp only [hu, hs, Set.mem_ofPred_eq, not_or, not_le] at hns
      rw [hj]
      exact hns.2.le
  -- on `{max X ≥ ε, A K < η}` the process at `ρ` is at least `ε`
  have hXρ : ∀ᵐ ω ∂P, ε ≤ (range (K + 1)).sup' nonempty_range_add_one (fun k => X k ω) →
      A K ω < η → ε ≤ X (ρ ω) ω := by
    filter_upwards [hAmono] with ω hmono hsup hAK
    obtain ⟨j, hj, hjX⟩ := exists_mem_eq_sup' nonempty_range_add_one (fun k => X k ω)
    rw [hjX] at hsup
    have hjK : j ≤ K := by simp only [mem_range] at hj; omega
    have hjs : u j ω ∈ s := Or.inl hsup
    have hle : ρ ω ≤ j := hittingBtwn_le_of_mem (Nat.zero_le j) hjK hjs
    rcases hle.lt_or_eq with hlt | heq
    · have hmem : u (ρ ω) ω ∈ s := hittingBtwn_mem_set ⟨j, ⟨Nat.zero_le j, hjK⟩, hjs⟩
      simp only [hu, hs, Set.mem_ofPred_eq] at hmem
      rcases hmem with h1 | h2
      · exact h1
      · exact absurd (lt_of_le_of_lt (hmono (show ρ ω + 1 ≤ K by omega)) hAK) (not_lt.2 h2)
    · rw [heq]
      exact hsup
  have hXρint : Integrable (fun ω => X (ρ ω) ω) P := by
    have := integrable_stoppedValue ℕ hρst hXint hρK'
    rwa [hsv] at this
  have hAρint : Integrable (fun ω => A (ρ ω) ω) P := by
    have := integrable_stoppedValue ℕ hρst hAint hρK'
    rwa [hsv] at this
  have hminint : Integrable (fun ω => min (A K ω) η) P :=
    (hAint K).inf (integrable_const η)
  have hmarkov : P {ω | ε ≤ X (ρ ω) ω} ≤ ENNReal.ofReal ((∫ ω, min (A K ω) η ∂P) / ε) := by
    have hm := mul_meas_ge_le_integral_of_nonneg
      (by filter_upwards [hXnn] with ω h using h (ρ ω)) hXρint ε
    have hd := hdom _ hρst hρK'
    rw [hsv, hsv] at hd
    have h2 : ∫ ω, A (ρ ω) ω ∂P ≤ ∫ ω, min (A K ω) η ∂P := integral_mono_ae hAρint hminint hAρ
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hε, mul_comm]
    linarith
  calc P {ω | ε ≤ (range (K + 1)).sup' nonempty_range_add_one fun k => X k ω}
      ≤ P ({ω | ε ≤ X (ρ ω) ω} ∪ {ω | η ≤ A K ω}) := by
        refine measure_mono_ae ?_
        filter_upwards [hXρ] with ω hω hmem
        by_cases hAK : η ≤ A K ω
        · exact Or.inr hAK
        · exact Or.inl (hω hmem (not_le.1 hAK))
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add hmarkov le_rfl)

/-- **Lenglart's inequality for a Doob compensator.** If `A - X` is a submartingale, `X` is
adapted and almost surely nonnegative with `X 0 = 0` almost surely, and `A` is predictable and
almost surely nondecreasing with `A 0 = 0` almost surely,
then `P(max_{k ≤ K} X_k ≥ ε) ≤ E[A_K ∧ η] / ε + P(A_K ≥ η)`. The domination hypothesis of
`measure_le_sup_le` follows from the optional stopping theorem. -/
theorem measure_le_sup_le_of_submartingale {X A : ℕ → Ω → ℝ} (K : ℕ)
    (hX : Adapted F X) (hA : ∀ k, Measurable[F k] (A (k + 1)))
    (hXnn : ∀ᵐ ω ∂P, ∀ k, 0 ≤ X k ω) (hX0 : ∀ᵐ ω ∂P, X 0 ω = 0) (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hAmono : ∀ᵐ ω ∂P, Monotone fun k => A k ω)
    (hXint : ∀ k, Integrable (X k) P) (hAint : ∀ k, Integrable (A k) P)
    (hsub : Submartingale (fun k ω => A k ω - X k ω) F P)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    P {ω | ε ≤ (range (K + 1)).sup' nonempty_range_add_one fun k => X k ω} ≤
      ENNReal.ofReal ((∫ ω, min (A K ω) η ∂P) / ε) + P {ω | η ≤ A K ω} := by
  refine measure_le_sup_le K hX hA hXnn hA0 hAmono hXint hAint (fun τ hτ hτK => ?_) hε hη
  have h := hsub.expected_stoppedValue_mono (isStoppingTime_const F 0) hτ
    (fun ω => by simp) hτK
  have h0 : ∀ᵐ ω ∂P, stoppedValue (fun k ω => A k ω - X k ω) (fun _ => ((0 : ℕ) : WithTop ℕ)) ω
      = 0 := by
    filter_upwards [hX0, hA0] with ω h1 h2
    change A 0 ω - X 0 ω = 0
    simp [h1, h2]
  have hsplit : stoppedValue (fun k ω => A k ω - X k ω) τ =
      fun ω => stoppedValue A τ ω - stoppedValue X τ ω := rfl
  have key : 0 ≤ ∫ ω, stoppedValue (fun k ω => A k ω - X k ω) τ ω ∂P :=
    (integral_eq_zero_of_ae h0).symm.le.trans h
  rw [hsplit, integral_sub (integrable_stoppedValue ℕ hτ hAint hτK)
    (integrable_stoppedValue ℕ hτ hXint hτK)] at key
  linarith

/-- For a square-integrable martingale `M`, `M² - ⟨M⟩` is a martingale, where `⟨M⟩` is the
predictable quadratic variation `∑_{j < k} E[(M_{j+1} - M_j)² | F_j]`. -/
theorem martingale_sq_sub_predictableQuadraticVariation {M : ℕ → Ω → ℝ}
    (hM : Martingale M F P) (hL2 : ∀ k, MemLp (M k) 2 P) :
    Martingale (fun k ω => M k ω ^ 2 - predictableQuadraticVariation P F M k ω) F P := by
  set c : ℕ → Ω → ℝ := fun k => P[fun ω => (M (k + 1) ω - M k ω) ^ 2 | F k] with hc
  have hAdef : ∀ k, predictableQuadraticVariation P F M k = fun ω => ∑ j ∈ range k, c j ω :=
    fun k => rfl
  have hAm : ∀ k, StronglyMeasurable[F k] (predictableQuadraticVariation P F M k) := by
    intro k
    rw [hAdef]
    exact Finset.stronglyMeasurable_fun_sum _ fun j hj =>
      stronglyMeasurable_condExp.mono (F.mono (by simp at hj; omega))
  have hAint : ∀ k, Integrable (predictableQuadraticVariation P F M k) P := fun k => by
    rw [hAdef]
    exact integrable_finsetSum _ fun j _ => integrable_condExp
  refine martingale_of_condExp_sub_eq_zero_nat (fun k => ?_)
    (fun k => (hL2 k).integrable_sq.sub (hAint k)) (fun k => ?_)
  · exact ((hM.stronglyMeasurable k).pow 2).sub (hAm k)
  · have hΔ : (fun ω => M (k + 1) ω ^ 2 - predictableQuadraticVariation P F M (k + 1) ω) -
        (fun ω => M k ω ^ 2 - predictableQuadraticVariation P F M k ω) =
        ((fun ω => 2 * M k ω) * fun ω => M (k + 1) ω - M k ω) +
          ((fun ω => (M (k + 1) ω - M k ω) ^ 2) - c k) := by
      funext ω
      simp only [hAdef, sum_range_succ, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
      ring
    have hd2 : MemLp (fun ω => M (k + 1) ω - M k ω) 2 P := (hL2 (k + 1)).sub (hL2 k)
    have hprod : Integrable ((fun ω => 2 * M k ω) * fun ω => M (k + 1) ω - M k ω) P :=
      ((hL2 k).const_mul 2).integrable_mul hd2
    have hsq : Integrable (fun ω => (M (k + 1) ω - M k ω) ^ 2) P := hd2.integrable_sq
    rw [hΔ]
    have h1 : P[(fun ω => 2 * M k ω) * (fun ω => M (k + 1) ω - M k ω) | F k] =ᵐ[P] 0 := by
      have hsm : StronglyMeasurable[F k] (fun ω => 2 * M k ω) :=
        (hM.stronglyMeasurable k).const_mul 2
      have hmul := condExp_mul_of_stronglyMeasurable_left (m := F k) (μ := P) hsm hprod
        (hd2.integrable one_le_two)
      have hdiff : P[fun ω => M (k + 1) ω - M k ω | F k] =ᵐ[P] 0 := by
        have hs := condExp_sub (m := F k) (μ := P) (hM.integrable (k + 1)) (hM.integrable k)
        have hk : P[M k | F k] = M k :=
          condExp_of_stronglyMeasurable (F.le k) (hM.stronglyMeasurable k) (hM.integrable k)
        filter_upwards [hs, hM.condExp_ae_eq (Nat.le_succ k)] with ω hω h2
        change P[M (k + 1) - M k | F k] ω = 0
        rw [hω, Pi.sub_apply, h2, hk, sub_self]
      filter_upwards [hmul, hdiff] with ω hω h2
      rw [hω, Pi.mul_apply, h2]
      simp
    have h2 : P[(fun ω => (M (k + 1) ω - M k ω) ^ 2) - c k | F k] =ᵐ[P] 0 := by
      have hs := condExp_sub (m := F k) (μ := P) hsq
        (show Integrable (c k) P from integrable_condExp)
      have hcc : P[c k | F k] = c k :=
        condExp_of_stronglyMeasurable (F.le k) stronglyMeasurable_condExp integrable_condExp
      filter_upwards [hs] with ω hω
      rw [hω, hcc, Pi.sub_apply, sub_self]
      rfl
    filter_upwards [condExp_add (m := F k) (μ := P) hprod
      (hsq.sub (show Integrable (c k) P from integrable_condExp)), h1, h2]
      with ω hω h1' h2'
    rw [hω, Pi.add_apply, h1', h2']
    simp

/-- **Lenglart's inequality for a martingale and its predictable quadratic variation**
(maximal form). For a square-integrable martingale `M` with `M 0 = 0` almost surely and
`ε, η > 0`,
`P(max_{k ≤ K} |M_k| ≥ ε) ≤ η / ε² + P(⟨M⟩_K ≥ η)`. -/
theorem measure_le_sup_abs_le_of_martingale {M : ℕ → Ω → ℝ} (K : ℕ)
    (hM : Martingale M F P) (hL2 : ∀ k, MemLp (M k) 2 P) (hM0 : ∀ᵐ ω ∂P, M 0 ω = 0)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    P {ω | ε ≤ (range (K + 1)).sup' nonempty_range_add_one fun k => |M k ω|} ≤
      ENNReal.ofReal (η / ε ^ 2) + P {ω | η ≤ predictableQuadraticVariation P F M K ω} := by
  set A := predictableQuadraticVariation P F M with hA
  set c : ℕ → Ω → ℝ := fun k => P[fun ω => (M (k + 1) ω - M k ω) ^ 2 | F k] with hc
  have hAdef : ∀ k, A k = fun ω => ∑ j ∈ range k, c j ω := fun k => rfl
  have hcnn : ∀ᵐ ω ∂P, ∀ j, 0 ≤ c j ω :=
    ae_all_iff.2 fun j => condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
  have hAint : ∀ k, Integrable (A k) P := fun k => by
    rw [hAdef]
    exact integrable_finsetSum _ fun j _ => integrable_condExp
  have hAmeas : ∀ k, Measurable[F k] (A (k + 1)) := fun k => by
    rw [hAdef]
    exact Finset.measurable_fun_sum _ fun j hj =>
      stronglyMeasurable_condExp.measurable.mono (F.mono (by simp at hj; omega)) le_rfl
  have hAmono : ∀ᵐ ω ∂P, Monotone fun k => A k ω := by
    filter_upwards [hcnn] with ω hω
    refine monotone_nat_of_le_succ fun k => ?_
    simp only [hAdef, sum_range_succ]
    linarith [hω k]
  have hmart := martingale_sq_sub_predictableQuadraticVariation hM hL2
  have hsub : Submartingale (fun k ω => A k ω - M k ω ^ 2) F P := by
    have := hmart.neg.submartingale
    convert this using 1
    funext k ω
    simp [hA]
  have hε2 : 0 < ε ^ 2 := by positivity
  have hmain := measure_le_sup_le_of_submartingale (X := fun k ω => M k ω ^ 2) (A := A) K
    (fun k => ((hM.stronglyMeasurable k).measurable.pow_const 2))
    hAmeas (Eventually.of_forall fun ω k => sq_nonneg _)
    (by filter_upwards [hM0] with ω h using by simp [h])
    (Eventually.of_forall fun ω => by simp [hAdef])
    hAmono (fun k => (hL2 k).integrable_sq) hAint hsub hε2 hη
  have hmin : ∫ ω, min (A K ω) η ∂P ≤ η := by
    calc ∫ ω, min (A K ω) η ∂P ≤ ∫ _ω, η ∂P :=
          integral_mono ((hAint K).inf (integrable_const η)) (integrable_const η)
            fun ω => min_le_right _ _
      _ = η := by simp
  calc P {ω | ε ≤ (range (K + 1)).sup' nonempty_range_add_one fun k => |M k ω|}
      ≤ P {ω | ε ^ 2 ≤ (range (K + 1)).sup' nonempty_range_add_one fun k => M k ω ^ 2} := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq] at hω ⊢
        obtain ⟨j, hj, hjM⟩ := exists_mem_eq_sup' nonempty_range_add_one (fun k => |M k ω|)
        rw [hjM] at hω
        calc ε ^ 2 ≤ |M j ω| ^ 2 := pow_le_pow_left₀ hε.le hω 2
          _ = M j ω ^ 2 := sq_abs _
          _ ≤ _ := le_sup' (fun k => M k ω ^ 2) hj
    _ ≤ ENNReal.ofReal ((∫ ω, min (A K ω) η ∂P) / ε ^ 2) + P {ω | η ≤ A K ω} := hmain
    _ ≤ ENNReal.ofReal (η / ε ^ 2) + P {ω | η ≤ A K ω} := by
        gcongr

end Lenglart

/-! ### Deterministic helpers for the law of large numbers step -/

/-- The weighted variance written through normalized sums,
`v = s⁽²⁾ / s⁽⁰⁾ - (s⁽¹⁾ / s⁽⁰⁾)²`. -/
noncomputable def limVar (s0 s1 s2 : ℝ) : ℝ := s2 / s0 - (s1 / s0) ^ 2

/-- The deterministic information compensator `∑_{k < K} Δα_k v(s(0, k, b), s(1, k, b),
s(2, k, b)) s(0, k, β₀)` for any real array `s` and real increments `Δα` (in applications, `s j k b`
is the deterministic limit of `S⁽ʲ⁾(b, k) / n`); the quotients in `v` are `0` when `s(0, k, b) = 0`.
-/
noncomputable def detInfoCompensator (s : ℕ → ℕ → ℝ → ℝ) (dα : ℕ → ℝ) (β₀ b : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ range K, dα k * limVar (s 0 k b) (s 1 k b) (s 2 k b) * s 0 k β₀

/-- `V(b) = v(S⁽⁰⁾ / c, S⁽¹⁾ / c, S⁽²⁾ / c)` for any normalization `c ≠ 0`. -/
theorem wVar_eq_limVar {n : ℕ} (Y z : Fin n → ℝ) (b : ℝ) {c : ℝ} (hc : c ≠ 0) :
    wVar Y z b = limVar (wSum Y z 0 b / c) (wSum Y z 1 b / c) (wSum Y z 2 b / c) := by
  simp only [wVar, wMean, limVar, div_div_div_cancel_right₀ hc]

/-- Uniform continuity of `(x₀, x₁, x₂, y) ↦ v(x₀, x₁, x₂) y` on the box `κ ≤ x₀ ≤ R`,
`|x₁|, |x₂|, |y| ≤ R`, for `κ > 0`. -/
theorem exists_pos_abs_limVar_mul_sub_lt {κ R ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x₀ x₁ x₂ y x₀' x₁' x₂' y' : ℝ,
      κ ≤ x₀ → x₀ ≤ R → |x₁| ≤ R → |x₂| ≤ R → |y| ≤ R →
      κ ≤ x₀' → x₀' ≤ R → |x₁'| ≤ R → |x₂'| ≤ R → |y'| ≤ R →
      |x₀ - x₀'| < δ → |x₁ - x₁'| < δ → |x₂ - x₂'| < δ → |y - y'| < δ →
      |limVar x₀ x₁ x₂ * y - limVar x₀' x₁' x₂' * y'| < ε := by
  set C : Set (ℝ × ℝ × ℝ × ℝ) :=
    Set.Icc κ R ×ˢ Set.Icc (-R) R ×ˢ Set.Icc (-R) R ×ˢ Set.Icc (-R) R with hC
  have hCc : IsCompact C :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  set g : ℝ × ℝ × ℝ × ℝ → ℝ := fun p => limVar p.1 p.2.1 p.2.2.1 * p.2.2.2 with hg
  have hgc : ContinuousOn g C := by
    intro p hp
    have hp0 : p.1 ≠ 0 := (lt_of_lt_of_le hκ hp.1.1).ne'
    have hx₀ : ContinuousAt (fun p : ℝ × ℝ × ℝ × ℝ => p.1) p := continuous_fst.continuousAt
    have hx₁ : ContinuousAt (fun p : ℝ × ℝ × ℝ × ℝ => p.2.1) p :=
      (continuous_fst.comp continuous_snd).continuousAt
    have hx₂ : ContinuousAt (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1) p :=
      (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt
    have hy : ContinuousAt (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2) p :=
      (continuous_snd.comp (continuous_snd.comp continuous_snd)).continuousAt
    exact (((hx₂.div hx₀ hp0).sub ((hx₁.div hx₀ hp0).pow 2)).mul hy).continuousWithinAt
  obtain ⟨δ, hδ, hδg⟩ :=
    Metric.uniformContinuousOn_iff.1 (hCc.uniformContinuousOn_of_continuous hgc) ε hε
  refine ⟨δ, hδ, fun x₀ x₁ x₂ y x₀' x₁' x₂' y' h₀ h₀R h₁ h₂ hy h₀' h₀R' h₁' h₂' hy'
    d₀ d₁ d₂ dy => ?_⟩
  have hmem : (x₀, x₁, x₂, y) ∈ C :=
    ⟨⟨h₀, h₀R⟩, abs_le.1 h₁, abs_le.1 h₂, abs_le.1 hy⟩
  have hmem' : (x₀', x₁', x₂', y') ∈ C :=
    ⟨⟨h₀', h₀R'⟩, abs_le.1 h₁', abs_le.1 h₂', abs_le.1 hy'⟩
  have hd : dist (x₀, x₁, x₂, y) (x₀', x₁', x₂', y') < δ := by
    simp only [Prod.dist_eq, Real.dist_eq]
    exact max_lt d₀ (max_lt d₁ (max_lt d₂ dy))
  have := hδg _ hmem _ hmem' hd
  rwa [Real.dist_eq] at this

/-- `|S⁽ʲ⁾(b) / n| ≤ Bʲ exp (|b| B)` for at-risk indicators and `|z| ≤ B`. -/
theorem abs_wSum_atRiskInd_div_le {n : ℕ} (t : Fin n → ℕ) {z : Fin n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ l, |z l| ≤ B) (k j : ℕ) (b : ℝ) :
    |wSum (atRiskInd t k) z j b / n| ≤ B ^ j * exp (|b| * B) := by
  have hY := atRiskInd_nonneg t k
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, div_zero, abs_zero]
    positivity
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_div, abs_of_pos hn', div_le_iff₀ hn']
    calc |wSum (atRiskInd t k) z j b| ≤ B ^ j * wSum (atRiskInd t k) z 0 b := abs_wSum_le hY hz j b
      _ ≤ B ^ j * (n * exp (|b| * B)) :=
          mul_le_mul_of_nonneg_left (wSum_zero_le (atRiskInd_le_one t k) hz b) (pow_nonneg hB j)
      _ = B ^ j * exp (|b| * B) * n := by ring

/-- Points of `[β₀ - r, β₀ + r]` satisfy `|b| ≤ |β₀| + r`. -/
theorem abs_le_of_mem_Icc {β₀ r b : ℝ} (hb : b ∈ Set.Icc (β₀ - r) (β₀ + r)) :
    |b| ≤ |β₀| + r := by
  have h1 : |b - β₀| ≤ r := abs_le.2 ⟨by linarith [hb.1], by linarith [hb.2]⟩
  calc |b| = |β₀ + (b - β₀)| := by ring_nf
    _ ≤ |β₀| + |b - β₀| := abs_add_le _ _
    _ ≤ |β₀| + r := by linarith

/-- An in-probability uniform limit on `S` of random functions that are `L`-Lipschitz on `S` is
`L`-Lipschitz on `S`. -/
theorem abs_sub_le_of_tendsto_measure {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {f : ℕ → Ω → ℝ → ℝ} {i : ℝ → ℝ} {S : Set ℝ} {L : ℝ}
    (hf : ∀ n ω, ∀ b ∈ S, ∀ b' ∈ S, |f n ω b - f n ω b'| ≤ L * |b - b'|)
    (hconv : ∀ η > 0, Tendsto (fun n => P {ω | ∃ b ∈ S, η ≤ |f n ω b - i b|}) atTop (𝓝 0))
    {b b' : ℝ} (hb : b ∈ S) (hb' : b' ∈ S) : |i b - i b'| ≤ L * |b - b'| := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := ((hconv (ε / 2) (half_pos hε)).eventually
    (gt_mem_nhds zero_lt_one)).exists
  have hne : {ω | ∃ b ∈ S, ε / 2 ≤ |f n ω b - i b|} ≠ Set.univ := by
    intro heq
    rw [heq, measure_univ] at hn
    exact lt_irrefl _ hn
  obtain ⟨ω, hω⟩ := Set.ne_univ_iff_exists_notMem _ |>.1 hne
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_le] at hω
  have h1 := hω b hb
  have h2 := hω b' hb'
  have h3 := hf n ω b hb b' hb'
  calc |i b - i b'| = |(i b - f n ω b) + (f n ω b - f n ω b') + (f n ω b' - i b')| := by ring_nf
    _ ≤ |i b - f n ω b| + |f n ω b - f n ω b'| + |f n ω b' - i b'| := abs_add_three _ _ _
    _ < ε / 2 + L * |b - b'| + ε / 2 := by
        rw [abs_sub_comm (i b)]
        linarith
    _ = L * |b - b'| + ε := by ring

/-- A function that is `L`-Lipschitz towards `β₀` on `[β₀ - r, β₀ + r]` with `r > 0` is
continuous at `β₀`. -/
theorem continuousAt_of_abs_sub_le {i : ℝ → ℝ} {β₀ r L : ℝ} (hr : 0 < r)
    (hL : ∀ b ∈ Set.Icc (β₀ - r) (β₀ + r), |i b - i β₀| ≤ L * |b - β₀|) :
    ContinuousAt i β₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hL1 : 0 < |L| + 1 := by positivity
  refine ⟨min r (ε / (|L| + 1)), lt_min hr (div_pos hε hL1), fun {x} hx => ?_⟩
  rw [Real.dist_eq] at hx ⊢
  have hxr : |x - β₀| < r := lt_of_lt_of_le hx (min_le_left _ _)
  have hxe : |x - β₀| < ε / (|L| + 1) := lt_of_lt_of_le hx (min_le_right _ _)
  have hmem : x ∈ Set.Icc (β₀ - r) (β₀ + r) :=
    ⟨by linarith [(abs_lt.1 hxr).1], by linarith [(abs_lt.1 hxr).2]⟩
  calc |i x - i β₀| ≤ L * |x - β₀| := hL x hmem
    _ ≤ |L| * |x - β₀| := mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
    _ ≤ |L| * (ε / (|L| + 1)) := mul_le_mul_of_nonneg_left hxe.le (abs_nonneg _)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hL1]
        nlinarith [abs_nonneg L]

section Model

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
  {F : ℕ → Filtration ℕ m0} {t : (n : ℕ) → Ω → Fin n → ℕ}
  {d : (n : ℕ) → Ω → Fin n → Bool} {z : (n : ℕ) → Ω → Fin n → ℝ} {dα : ℕ → ℕ → ℝ} {β₀ B : ℝ}

/-- The normalized information compensator is Lipschitz in `b` with the deterministic constant
`6 B³ Λ exp (|β₀| B)` when `∑ₖ Δα ≤ Λ`. -/
theorem abs_infoCompensator_div_sub_le (h : IsCoxCountingProcess P F t d z dα β₀ B) (n K : ℕ)
    {Λ : ℝ} (hΛ : ∑ k ∈ range K, dα n k ≤ Λ) (ω : Ω) (b b' : ℝ) :
    |infoCompensator (t n ω) (z n ω) (dα n) β₀ b K / n -
        infoCompensator (t n ω) (z n ω) (dα n) β₀ b' K / n| ≤
      6 * B ^ 3 * (Λ * exp (|β₀| * B)) * |b - b'| := by
  have hB := h.bound_nonneg
  set E := exp (|β₀| * B)
  have heq : infoCompensator (t n ω) (z n ω) (dα n) β₀ b K / n -
      infoCompensator (t n ω) (z n ω) (dα n) β₀ b' K / n =
      ∑ k ∈ range K, dα n k * (wVar (atRiskInd (t n ω) k) (z n ω) b -
        wVar (atRiskInd (t n ω) k) (z n ω) b') *
          (wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ / n) := by
    unfold infoCompensator
    rw [sum_div, sum_div, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [heq]
  have hterm : ∀ k ∈ range K, |dα n k * (wVar (atRiskInd (t n ω) k) (z n ω) b -
      wVar (atRiskInd (t n ω) k) (z n ω) b') * (wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ / n)| ≤
      dα n k * (6 * B ^ 3 * |b - b'| * E) := by
    intro k _
    have hα := h.hazard_nonneg n k
    have hV := abs_wVar_sub_le (atRiskInd_nonneg (t n ω) k) (h.covariate_bound n ω) hB b b'
    have hS := abs_wSum_atRiskInd_div_le (t n ω) hB (h.covariate_bound n ω) k 0 β₀
    rw [pow_zero, one_mul] at hS
    rw [abs_mul, abs_mul, abs_of_nonneg hα, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hα
    exact mul_le_mul hV hS (abs_nonneg _) (by positivity)
  calc |∑ k ∈ range K, dα n k * (wVar (atRiskInd (t n ω) k) (z n ω) b -
        wVar (atRiskInd (t n ω) k) (z n ω) b') * (wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ / n)|
      ≤ ∑ k ∈ range K, dα n k * (6 * B ^ 3 * |b - b'| * E) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ = (∑ k ∈ range K, dα n k) * (6 * B ^ 3 * |b - b'| * E) := by rw [sum_mul]
    _ ≤ Λ * (6 * B ^ 3 * |b - b'| * E) :=
        mul_le_mul_of_nonneg_right hΛ (by positivity)
    _ = 6 * B ^ 3 * (Λ * E) * |b - b'| := by ring

end Model

/-! ### The law of large numbers step -/

section LLN

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
  {F : ℕ → Filtration ℕ m0} {t : (n : ℕ) → Ω → Fin n → ℕ}
  {d : (n : ℕ) → Ω → Fin n → Bool} {z : (n : ℕ) → Ω → Fin n → ℝ} {dα : ℕ → ℕ → ℝ} {β₀ B : ℝ}

/-- **Andersen–Gill regularity on the grid** (discrete form of Condition B plus a finite
cumulative hazard). For deterministic `s n j k b` (the limit of `S⁽ʲ⁾(b, k) / n`), a radius
`r ≥ 0`, `κ > 0` and `Λ`:

* `S⁽ʲ⁾(b, k) / n` is uniformly close to `s n j k b` over `k < K n` and `b ∈ [β₀ - r, β₀ + r]`,
  in `P`-measure (in probability when `P` is a probability measure), for `j = 0, 1, 2`;
* `s n 0 k b ≥ κ` (the risk set does not empty out);
* the cumulative baseline hazard over the grid is at most `Λ`;
* the deterministic compensator `detInfoCompensator` converges to `i` uniformly on the
  interval. -/
structure IsAndersenGillRegular (P : Measure Ω) (t : (n : ℕ) → Ω → Fin n → ℕ)
    (z : (n : ℕ) → Ω → Fin n → ℝ) (dα : ℕ → ℕ → ℝ) (K : ℕ → ℕ) (β₀ r : ℝ)
    (s : ℕ → ℕ → ℕ → ℝ → ℝ) (κ Λ : ℝ) (i : ℝ → ℝ) : Prop where
  radius_nonneg : 0 ≤ r
  lower_pos : 0 < κ
  tendsto_wSum : ∀ j ≤ 2, ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ k < K n,
    ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |wSum (atRiskInd (t n ω) k) (z n ω) j b / n - s n j k b|}) atTop (𝓝 0)
  lower_le : ∀ n, ∀ k < K n, ∀ b ∈ Set.Icc (β₀ - r) (β₀ + r), κ ≤ s n 0 k b
  sum_hazard_le : ∀ n, ∑ k ∈ range (K n), dα n k ≤ Λ
  tendsto_det : ∀ ε > 0, ∀ᶠ n in atTop, ∀ b ∈ Set.Icc (β₀ - r) (β₀ + r),
    |detInfoCompensator (s n) (dα n) β₀ b (K n) - i b| < ε

/-- **The law of large numbers step.** Andersen–Gill regularity implies T159's hypothesis
`hcomp`: the normalized information compensator converges to `i` uniformly in `P`-measure on
`[β₀ - r, β₀ + r]` (in probability when `P` is a probability measure). -/
theorem tendsto_measure_exists_infoCompensator (h : IsCoxCountingProcess P F t d z dα β₀ B)
    {K : ℕ → ℕ} {r : ℝ} {s : ℕ → ℕ → ℕ → ℝ → ℝ} {κ Λ : ℝ} {i : ℝ → ℝ}
    (hAG : IsAndersenGillRegular P t z dα K β₀ r s κ Λ i) :
    ∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |infoCompensator (t n ω) (z n ω) (dα n) β₀ b (K n) / n - i b|}) atTop (𝓝 0) := by
  intro η hη
  have hB := h.bound_nonneg
  have hr := hAG.radius_nonneg
  have hκ := hAG.lower_pos
  set I := Set.Icc (β₀ - r) (β₀ + r) with hI
  have hβI : β₀ ∈ I := ⟨by linarith, by linarith⟩
  set E : ℝ := exp ((|β₀| + r) * B) with hE
  have hEpos : 0 < E := exp_pos _
  set R : ℝ := E * (1 + B + B ^ 2) + 1 with hR
  have hBR : ∀ j ≤ 2, B ^ j * E ≤ R - 1 := by
    intro j hj
    interval_cases j <;> simp only [hR] <;> nlinarith [sq_nonneg B]
  have hexpI : ∀ b ∈ I, exp (|b| * B) ≤ E := fun b hb =>
    exp_le_exp.2 (mul_le_mul_of_nonneg_right (abs_le_of_mem_Icc hb) hB)
  have hrand : ∀ n ω k j, j ≤ 2 → ∀ b ∈ I,
      |wSum (atRiskInd (t n ω) k) (z n ω) j b / n| ≤ R - 1 := by
    intro n ω k j hj b hb
    calc |wSum (atRiskInd (t n ω) k) (z n ω) j b / n| ≤ B ^ j * exp (|b| * B) :=
          abs_wSum_atRiskInd_div_le (t n ω) hB (h.covariate_bound n ω) k j b
      _ ≤ B ^ j * E := mul_le_mul_of_nonneg_left (hexpI b hb) (pow_nonneg hB j)
      _ ≤ R - 1 := hBR j hj
  set ε' : ℝ := η / (2 * (|Λ| + 1)) with hε'
  have hε'pos : 0 < ε' := div_pos hη (by positivity)
  obtain ⟨δ, hδ, hcont⟩ := exists_pos_abs_limVar_mul_sub_lt (κ := κ / 2) (R := R)
    (half_pos hκ) hε'pos
  set δ' : ℝ := min (min δ (κ / 2)) 1 with hδ'
  have hδ'pos : 0 < δ' := lt_min (lt_min hδ (half_pos hκ)) one_pos
  have hδ'δ : δ' ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ'κ : δ' ≤ κ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  set bad : ℕ → ℕ → Set Ω := fun j n => {ω | ∃ k < K n, ∃ b ∈ I,
    δ' ≤ |wSum (atRiskInd (t n ω) k) (z n ω) j b / n - s n j k b|} with hbad
  have hlim : Tendsto (fun n => P (bad 0 n) + P (bad 1 n) + P (bad 2 n)) atTop (𝓝 0) := by
    have := ((hAG.tendsto_wSum 0 (by norm_num) δ' hδ'pos).add
      (hAG.tendsto_wSum 1 (by norm_num) δ' hδ'pos)).add
        (hAG.tendsto_wSum 2 (by norm_num) δ' hδ'pos)
    simpa only [add_zero] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hAG.tendsto_det (η / 2) (half_pos hη)] with n hn
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) le_rfl))
  intro ω hω
  obtain ⟨b, hb, hbη⟩ := hω
  by_contra hgood
  simp only [Set.mem_union, not_or] at hgood
  obtain ⟨⟨g0, g1⟩, g2⟩ := hgood
  have hgood : ∀ j ≤ 2, ∀ k < K n, ∀ b' ∈ I,
      |wSum (atRiskInd (t n ω) k) (z n ω) j b' / n - s n j k b'| < δ' := by
    intro j hj k hk b' hb'
    have hnot : ∀ j' (_ : ω ∉ bad j' n), |wSum (atRiskInd (t n ω) k) (z n ω) j' b' / n -
        s n j' k b'| < δ' := fun j' hj' => by
      simp only [hbad, Set.mem_ofPred_eq, not_exists, not_and, not_le] at hj'
      exact hj' k hk b' hb'
    interval_cases j
    · exact hnot 0 g0
    · exact hnot 1 g1
    · exact hnot 2 g2
  -- per-step comparison with the deterministic compensator
  have hstep : ∀ k ∈ range (K n),
      |dα n k * wVar (atRiskInd (t n ω) k) (z n ω) b *
          (wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ / n) -
        dα n k * limVar (s n 0 k b) (s n 1 k b) (s n 2 k b) * s n 0 k β₀| ≤ dα n k * ε' := by
    intro k hk
    have hk' : k < K n := mem_range.1 hk
    have hα := h.hazard_nonneg n k
    set Y := atRiskInd (t n ω) k
    have e0 := hgood 0 (by norm_num) k hk' b hb
    have e1 := hgood 1 (by norm_num) k hk' b hb
    have e2 := hgood 2 (by norm_num) k hk' b hb
    have ey := hgood 0 (by norm_num) k hk' β₀ hβI
    have r0 := hrand n ω k 0 (by norm_num) b hb
    have r1 := hrand n ω k 1 (by norm_num) b hb
    have r2 := hrand n ω k 2 (by norm_num) b hb
    have ry := hrand n ω k 0 (by norm_num) β₀ hβI
    have hs0 := hAG.lower_le n k hk' b hb
    have hx₀ : κ / 2 ≤ wSum Y (z n ω) 0 b / n := by
      linarith [(abs_lt.1 e0).1, (abs_lt.1 e0).2]
    have hn0 : (n : ℝ) ≠ 0 := by
      intro h0
      rw [h0, div_zero] at hx₀
      linarith
    have habs : ∀ {a c : ℝ}, |a| ≤ R - 1 → |a - c| < δ' → |c| ≤ R := by
      intro a c ha hac
      have : |c| ≤ |a| + |a - c| := by
        calc |c| = |a - (a - c)| := by ring_nf
          _ ≤ |a| + |a - c| := abs_sub _ _
      linarith
    have key := hcont (wSum Y (z n ω) 0 b / n) (wSum Y (z n ω) 1 b / n) (wSum Y (z n ω) 2 b / n)
      (wSum Y (z n ω) 0 β₀ / n) (s n 0 k b) (s n 1 k b) (s n 2 k b) (s n 0 k β₀)
      hx₀ (by linarith [le_abs_self (wSum Y (z n ω) 0 b / n)]) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith [le_abs_self (s n 0 k b), habs r0 e0])
      (habs r1 e1) (habs r2 e2) (habs ry ey)
      (lt_of_lt_of_le e0 hδ'δ) (lt_of_lt_of_le e1 hδ'δ) (lt_of_lt_of_le e2 hδ'δ)
      (lt_of_lt_of_le ey hδ'δ)
    rw [← wVar_eq_limVar Y (z n ω) b hn0] at key
    rw [mul_assoc, mul_assoc, ← mul_sub, abs_mul, abs_of_nonneg hα]
    exact mul_le_mul_of_nonneg_left key.le hα
  have hsum : |infoCompensator (t n ω) (z n ω) (dα n) β₀ b (K n) / n -
      detInfoCompensator (s n) (dα n) β₀ b (K n)| ≤ ε' * |Λ| := by
    have heq : infoCompensator (t n ω) (z n ω) (dα n) β₀ b (K n) / n -
        detInfoCompensator (s n) (dα n) β₀ b (K n) =
        ∑ k ∈ range (K n), (dα n k * wVar (atRiskInd (t n ω) k) (z n ω) b *
          (wSum (atRiskInd (t n ω) k) (z n ω) 0 β₀ / n) -
        dα n k * limVar (s n 0 k b) (s n 1 k b) (s n 2 k b) * s n 0 k β₀) := by
      unfold infoCompensator detInfoCompensator
      rw [sum_div, ← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [heq]
    calc _ ≤ ∑ k ∈ range (K n), dα n k * ε' :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum hstep)
      _ = (∑ k ∈ range (K n), dα n k) * ε' := by rw [sum_mul]
      _ ≤ Λ * ε' := mul_le_mul_of_nonneg_right (hAG.sum_hazard_le n) hε'pos.le
      _ ≤ |Λ| * ε' := mul_le_mul_of_nonneg_right (le_abs_self Λ) hε'pos.le
      _ = ε' * |Λ| := mul_comm _ _
  have hε'Λ : ε' * |Λ| < η / 2 := by
    rw [hε', div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith [abs_nonneg Λ]
  have htri := abs_sub_le (infoCompensator (t n ω) (z n ω) (dα n) β₀ b (K n) / n)
    (detInfoCompensator (s n) (dα n) β₀ b (K n)) (i b)
  have := hn b hb
  linarith

/-- For a positive radius `r > 0`, the limit `i` of the compensator is Lipschitz on the interval
`[β₀ - r, β₀ + r]`, hence continuous at `β₀`. -/
theorem continuousAt_of_isAndersenGillRegular [IsProbabilityMeasure P]
    (h : IsCoxCountingProcess P F t d z dα β₀ B)
    {K : ℕ → ℕ} {r : ℝ} {s : ℕ → ℕ → ℕ → ℝ → ℝ} {κ Λ : ℝ} {i : ℝ → ℝ}
    (hAG : IsAndersenGillRegular P t z dα K β₀ r s κ Λ i) (hr : 0 < r) :
    ContinuousAt i β₀ := by
  refine continuousAt_of_abs_sub_le (L := 6 * B ^ 3 * (Λ * exp (|β₀| * B))) hr fun b hb => ?_
  exact abs_sub_le_of_tendsto_measure
    (f := fun n ω b => infoCompensator (t n ω) (z n ω) (dα n) β₀ b (K n) / n)
    (fun n ω b _ b' _ => abs_infoCompensator_div_sub_le h n (K n) (hAG.sum_hazard_le n) ω b b')
    (tendsto_measure_exists_infoCompensator h hAG) hb ⟨by linarith, by linarith⟩

end LLN

/-! ### The Andersen–Gill theorems from counting-process conditions -/

section AndersenGill

open MathlibExt.Probability.Statistics.CoxAsymptotics

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {F : ℕ → Filtration ℕ m0} {t : (n : ℕ) → Ω → Fin n → ℕ}
  {d : (n : ℕ) → Ω → Fin n → Bool} {z : (n : ℕ) → Ω → Fin n → ℝ} {dα : ℕ → ℕ → ℝ} {β₀ B : ℝ}
  {K : ℕ → ℕ} {r : ℝ} {s : ℕ → ℕ → ℕ → ℝ → ℝ} {κ Λ : ℝ} {i : ℝ → ℝ} {v : NNReal}

/-- **T145's limit hypotheses from counting-process conditions.** Under `IsCoxCountingProcess`, with
every observed event time `1 ≤ tᵢ ≤ K n` (grid step `k` covers time `k + 1`), Andersen–Gill
regularity on `[β₀ - r, β₀ + r]` with `r > 0` and `i β₀ = v` gives, for any `Z ~ N(0, v)`: the score
CLT (`hscore`), the uniform information limit (`hinfo`) and continuity of `i` at `β₀` (`hi`). -/
theorem andersenGill_hypotheses_of_isAndersenGillRegular
    (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (hsupp : ∀ n ω i, d n ω i = true → 1 ≤ t n ω i ∧ t n ω i ≤ K n)
    (hAG : IsAndersenGillRegular P t z dα K β₀ r s κ Λ i) (hr : 0 < r) (hiv : i β₀ = v)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 v) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => coxScore (fun l => (t n ω l : ℝ)) (d n ω) (z n ω) β₀ / √(n : ℝ))
      atTop Z (fun _ => P) P' ∧
    (∀ η > 0, Tendsto (fun n : ℕ => P {ω | ∃ b ∈ Set.Icc (β₀ - r) (β₀ + r),
      η ≤ |coxInformation (fun l => (t n ω l : ℝ)) (d n ω) (z n ω) b / n - i b|}) atTop (𝓝 0)) ∧
    ContinuousAt i β₀ :=
  ⟨(andersenGill_hypotheses_of_tendsto_infoCompensator h K hsupp hAG.radius_nonneg hiv
      (tendsto_measure_exists_infoCompensator h hAG) hZ).1,
    (andersenGill_hypotheses_of_tendsto_infoCompensator h K hsupp hAG.radius_nonneg hiv
      (tendsto_measure_exists_infoCompensator h hAG) hZ).2,
    continuousAt_of_isAndersenGillRegular h hAG hr⟩

/-- **Consistency of the Cox estimator from counting-process conditions** (Andersen–Gill
Theorem 3.2, grid model, scalar covariate). -/
theorem tendstoInMeasure_coxMPLE_of_isAndersenGillRegular
    (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (hsupp : ∀ n ω i, d n ω i = true → 1 ≤ t n ω i ∧ t n ω i ≤ K n)
    (hAG : IsAndersenGillRegular P t z dα K β₀ r s κ Λ i) (hr : 0 < r) (hiv : i β₀ = v)
    (hv : v ≠ 0) {βhat : ℕ → Ω → ℝ}
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (fun l => (t n ω l : ℝ)) (d n ω) (z n ω))
        Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (fun l => (t n ω l : ℝ)) (d n ω) (z n ω)) Set.univ
        (βhat n ω)) :
    TendstoInMeasure P βhat atTop (fun _ => β₀) := by
  obtain ⟨hscore, hinfo, hi⟩ := andersenGill_hypotheses_of_isAndersenGillRegular h hsupp hAG hr hiv
    (HasLaw.id (μ := gaussianReal 0 v))
  exact tendstoInMeasure_coxMPLE (T := fun n ω l => (t n ω l : ℝ)) hv hβhat hscore hi hiv hinfo hr

/-- **Asymptotic normality of the Cox estimator from counting-process conditions**
(Andersen–Gill Theorem 3.3, grid model, scalar covariate): `√n (βhat n - β₀) ⟶ Z / v` and
`Z / v ~ N(0, v⁻¹)`. -/
theorem tendstoInDistribution_coxMPLE_gaussian_of_isAndersenGillRegular
    (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (hsupp : ∀ n ω i, d n ω i = true → 1 ≤ t n ω i ∧ t n ω i ≤ K n)
    (hAG : IsAndersenGillRegular P t z dα K β₀ r s κ Λ i) (hr : 0 < r) (hiv : i β₀ = v)
    (hv : v ≠ 0) {βhat : ℕ → Ω → ℝ}
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (fun l => (t n ω l : ℝ)) (d n ω) (z n ω))
        Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (fun l => (t n ω l : ℝ)) (d n ω) (z n ω)) Set.univ
        (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 v) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - β₀)) atTop
      (fun ω => Z ω / (v : ℝ)) (fun _ ↦ P) P' ∧
    HasLaw (fun ω => Z ω / (v : ℝ)) (gaussianReal 0 v⁻¹) P' := by
  obtain ⟨hscore, hinfo, hi⟩ :=
    andersenGill_hypotheses_of_isAndersenGillRegular h hsupp hAG hr hiv hZ
  exact tendstoInDistribution_coxMPLE_gaussian (T := fun n ω l => (t n ω l : ℝ)) hv hβhat
    hβhat_meas hscore hZ hi hiv hinfo hr

/-- **Coverage of the Cox Wald interval from counting-process conditions**: the interval
`βhat n ± c / √(Iₙ(βhat n))` covers `β₀` with probability tending to the standard-normal mass of
`[-c, c]`. -/
theorem tendsto_coverage_cox_waldInterval_of_isAndersenGillRegular
    (h : IsCoxCountingProcess P F t d z dα β₀ B)
    (hsupp : ∀ n ω i, d n ω i = true → 1 ≤ t n ω i ∧ t n ω i ≤ K n)
    (hAG : IsAndersenGillRegular P t z dα K β₀ r s κ Λ i) (hr : 0 < r) (hiv : i β₀ = v)
    (hv : v ≠ 0) {βhat : ℕ → Ω → ℝ}
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (fun l => (t n ω l : ℝ)) (d n ω) (z n ω))
        Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (fun l => (t n ω l : ℝ)) (d n ω) (z n ω)) Set.univ
        (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P)
    (hsd_meas : ∀ n : ℕ, AEMeasurable (fun ω ↦
      √(n / coxInformation (fun l => (t n ω l : ℝ)) (d n ω) (z n ω) (βhat n ω))) P) (c : ℝ) :
    Tendsto (fun n : ℕ ↦ P.real {ω | β₀ ∈ ProcessInference.waldInterval (βhat n ω)
        (1 / √(coxInformation (fun l => (t n ω l : ℝ)) (d n ω) (z n ω) (βhat n ω))) c}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Icc (-c) c))) := by
  obtain ⟨hscore, hinfo, hi⟩ := andersenGill_hypotheses_of_isAndersenGillRegular h hsupp hAG hr hiv
    (HasLaw.id (μ := gaussianReal 0 v))
  exact tendsto_coverage_cox_waldInterval_coxMPLE (T := fun n ω l => (t n ω l : ℝ)) hv hβhat
    hβhat_meas hscore HasLaw.id hi hiv hinfo hr hsd_meas c

end AndersenGill

end MathlibExt.Probability.Statistics.Lenglart
