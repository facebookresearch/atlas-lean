/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CramerRateFunction
public import MathlibExt.Probability.LDPProduct

/-!
# The Cramér upper bound in `ℝᵈ`

Let `X₀, X₁, …` be measurable i.i.d. random vectors in `ℝᵈ` on a probability space with
`E[exp ⟪t, X₀⟫] < ∞` for every `t`, and let `μₙ` be the law of the empirical mean
`(1/n) ∑_{i<n} Xᵢ`. This file proves that the Cramér rate function
`Λ*(x) = sup_t (⟪t, x⟫ - Λ(t))`, `Λ(t) = log E[exp ⟪t, X₀⟫]`, is a good rate function, and the
large deviation upper bound `limsup (1/n) log μₙ(F) ≤ -inf_F Λ*` for every closed `F`.

## Proof idea

* Goodness: testing `Λ*` against the `2 d` coordinate directions `± eᵢ` gives
  `|xᵢ| ≤ max_± Λ(± eᵢ) + a` on `{Λ* ≤ a}`, so sub-level sets lie in coordinate boxes.
* Upper bound: for `q < Λ*(x)` there is a direction `t` with `q < ⟪t, x⟫ - Λ(t)`; the open
  half-space `{y | q < ⟪t, y⟫ - Λ(t)}` contains `x` and has `μₙ`-mass at most `exp (-n q)` by
  the fixed-direction Chernoff bound (`cramer_upper_bound`). Finitely many such half-spaces
  cover a compact set. The Chernoff bound in the coordinate directions gives exponential
  tightness, which passes from compact to closed sets.

## Source

S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
Section 1 and Exercise 2 there (https://math.nyu.edu/~varadhan/LDP/1-2.pdf): Chebyshev's
inequality in half-spaces and covering. See also A. Dembo and O. Zeitouni, *Large Deviations
Techniques and Applications*, 2nd ed., Section 2.2.

## Main results

* `isGoodRateFunction_cramerRateFunction`: `Λ*` is a good rate function.
* `exists_isCompact_empiricalMeanMeasureVec_compl_le`: exponential tightness of `μₙ`.
* `limsup_log_empiricalMeanMeasureVec_le`: the large deviation upper bound for closed sets.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped InnerProductSpace ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.CramerUpperBound
open MathlibExt.Probability.CramerRateFunction

namespace MathlibExt.Probability.CramerLDPUpperBound

open MathlibExt.Probability.VaradhanIntegralLemma (inv_mul_log_le_coe_iff)
open MathlibExt.Probability.LDPProduct (eventually_mul_ofReal_exp_le)

/-- **Coordinate boxes are bounded.** The box `{x | ∀ i, |x i| ≤ B}` in `ℝᵈ` is bounded. -/
theorem isBounded_box {d : ℕ} (B : ℝ) :
    Bornology.IsBounded {x : EuclideanSpace ℝ (Fin d) | ∀ i, |x i| ≤ B} := by
  refine isBounded_iff_forall_norm_le.2 ⟨Real.sqrt (d * B ^ 2), fun x hx => ?_⟩
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, B ^ 2 := Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact hx i) 2
    _ = d * B ^ 2 := by simp

/-- **Coordinate boxes are compact.** The box `{x | ∀ i, |x i| ≤ B}` in `ℝᵈ` is compact. -/
theorem isCompact_box {d : ℕ} (B : ℝ) :
    IsCompact {x : EuclideanSpace ℝ (Fin d) | ∀ i, |x i| ≤ B} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ (isBounded_box B)
  have : {x : EuclideanSpace ℝ (Fin d) | ∀ i, |x i| ≤ B} = ⋂ i, {x | |x i| ≤ B} := by
    ext x; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

/-- **Inner product with a coordinate vector.** `⟪eᵢ, x⟫ = x i` in `ℝᵈ`. -/
theorem inner_single_one {d : ℕ} (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪EuclideanSpace.single i (1 : ℝ), x⟫_ℝ = x i := by
  simp [EuclideanSpace.inner_single_left]

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {d : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}

/-- **The laws of the empirical means are probability measures.** -/
theorem isProbabilityMeasure_empiricalMeanMeasureVec (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) : IsProbabilityMeasure (empiricalMeanMeasureVec X μ n) := by
  unfold empiricalMeanMeasureVec
  infer_instance

/-- **Fixed-direction Chernoff bound for every sample size.** If `a ≤ ⟪ξ, x⟫ - Λ(ξ)` on a measurable
set `F`, then `μₙ(F) ≤ exp (-n a)` for every `n`. -/
theorem empiricalMeanMeasureVec_le (hXmeas : ∀ i, Measurable (X i)) (hXindep : iIndepFun X μ)
    (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {F : Set (EuclideanSpace ℝ (Fin d))}
    (hF : MeasurableSet F) {ξ : EuclideanSpace ℝ (Fin d)} {a : ℝ}
    (hInt : Integrable (fun ω => Real.exp ⟪ξ, X 0 ω⟫_ℝ) μ)
    (ha : ∀ x ∈ F, a ≤ ⟪ξ, x⟫_ℝ - logMGFVec (X 0) μ ξ) (n : ℕ) :
    empiricalMeanMeasureVec X μ n F ≤ ENNReal.ofReal (Real.exp (-(n * a))) := by
  have := isProbabilityMeasure_empiricalMeanMeasureVec (μ := μ) X n
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ F)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := cramer_upper_bound hXmeas hXindep hXident hF hInt ha n
  rwa [neg_mul] at h

/-- **A bound for the log moment generating function in the coordinate directions.** -/
noncomputable def coordBound (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) : ℝ :=
  ∑ i, (|logMGFVec X μ (EuclideanSpace.single i (1 : ℝ))| +
    |logMGFVec X μ (-EuclideanSpace.single i (1 : ℝ))|)

/-- **The coordinate bound dominates the log moment generating function in the coordinate
directions.** -/
theorem logMGFVec_single_le_coordBound (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω)
    (i : Fin d) :
    logMGFVec X μ (EuclideanSpace.single i (1 : ℝ)) ≤ coordBound X μ ∧
      logMGFVec X μ (-EuclideanSpace.single i (1 : ℝ)) ≤ coordBound X μ := by
  have h := Finset.single_le_sum (f := fun i : Fin d =>
    |logMGFVec X μ (EuclideanSpace.single i (1 : ℝ))| +
      |logMGFVec X μ (-EuclideanSpace.single i (1 : ℝ))|)
    (fun j _ => by positivity) (Finset.mem_univ i)
  refine ⟨?_, ?_⟩
  · exact (le_abs_self _).trans (le_trans (le_add_of_nonneg_right (abs_nonneg _)) h)
  · exact (le_abs_self _).trans (le_trans (le_add_of_nonneg_left (abs_nonneg _)) h)

/-- **Compact sub-level sets of the Cramér rate function.** If `E[exp ⟪t, X⟫] < ∞` for every
`t`, then every finite sub-level set of `Λ*` is contained in a coordinate box, and the Cramér
rate function is a good rate function. -/
theorem isGoodRateFunction_cramerRateFunction (X₀ : Ω → EuclideanSpace ℝ (Fin d))
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X₀ ω⟫_ℝ) μ) :
    IsGoodRateFunction (cramerRateFunction X₀ μ) := by
  refine ⟨⟨lowerSemicontinuous_cramerRateFunction X₀ μ⟩, fun a => ?_⟩
  set B := coordBound X₀ μ + max a 0 with hB_def
  refine (isCompact_box (d := d) B).of_isClosed_subset
    ((lowerSemicontinuous_cramerRateFunction X₀ μ).isClosed_preimage _) fun x hx => ?_
  have hx' : cramerRateFunction X₀ μ x ≤ ENNReal.ofReal a := hx
  have key : ∀ t : EuclideanSpace ℝ (Fin d), ⟪t, x⟫_ℝ - logMGFVec X₀ μ t ≤ max a 0 := by
    intro t
    have h := (le_cramerRateFunction_of_integrable X₀ x t (hInt t)).trans hx'
    rcases (ENNReal.ofReal_le_ofReal_iff'.1 h) with h | h
    · exact h.trans (le_max_left _ _)
    · exact h.trans (le_max_right _ _)
  intro i
  have h1 := key (EuclideanSpace.single i (1 : ℝ))
  have h2 := key (-EuclideanSpace.single i (1 : ℝ))
  rw [inner_single_one] at h1
  rw [inner_neg_left, inner_single_one] at h2
  have hb := logMGFVec_single_le_coordBound X₀ μ i
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]

/-- **Exponential tightness of the empirical means.** Under finite exponential moments, for
every `ℓ` there is a compact coordinate box `K` with `μₙ(Kᶜ) ≤ 2 d exp (-n ℓ)` for every `n`;
this uses the Chernoff bound in the `2 d` coordinate directions. -/
theorem exists_isCompact_empiricalMeanMeasureVec_compl_le (hXmeas : ∀ i, Measurable (X i))
    (hXindep : iIndepFun X μ) (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X 0 ω⟫_ℝ) μ)
    (ℓ : ℝ) :
    ∃ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K ∧ ∀ n : ℕ,
      empiricalMeanMeasureVec X μ n Kᶜ ≤ 2 * d * ENNReal.ofReal (Real.exp (-(n * ℓ))) := by
  set B := |ℓ| + coordBound (X 0) μ with hB_def
  refine ⟨{x | ∀ i, |x i| ≤ B}, isCompact_box B, fun n => ?_⟩
  have hsub : {x : EuclideanSpace ℝ (Fin d) | ∀ i, |x i| ≤ B}ᶜ ⊆
      ⋃ i, ({x | B < x i} ∪ {x | x i < -B}) := by
    intro x hx
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hx
    obtain ⟨i, hi⟩ := hx
    refine mem_iUnion.2 ⟨i, ?_⟩
    rcases lt_abs.1 hi with h | h
    · exact Or.inl h
    · exact Or.inr (by simp only [mem_ofPred_eq]; linarith)
  have hexp : ∀ c : ℝ, c ≤ coordBound (X 0) μ →
      ENNReal.ofReal (Real.exp (-(n * (B - c)))) ≤ ENNReal.ofReal (Real.exp (-(n * ℓ))) := by
    intro c hc
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have : ℓ ≤ B - c := by rw [hB_def]; linarith [le_abs_self ℓ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  calc empiricalMeanMeasureVec X μ n {x | ∀ i, |x i| ≤ B}ᶜ
      ≤ empiricalMeanMeasureVec X μ n (⋃ i, ({x | B < x i} ∪ {x | x i < -B})) :=
        measure_mono hsub
    _ ≤ ∑ i, empiricalMeanMeasureVec X μ n ({x | B < x i} ∪ {x | x i < -B}) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin d, 2 * ENNReal.ofReal (Real.exp (-(n * ℓ))) := by
        refine Finset.sum_le_sum fun i _ => (measure_union_le _ _).trans ?_
        rw [two_mul]
        have hb := logMGFVec_single_le_coordBound (X 0) μ i
        refine add_le_add ?_ ?_
        · refine (empiricalMeanMeasureVec_le hXmeas hXindep hXident
            (measurableSet_lt measurable_const (by fun_prop))
            (ξ := EuclideanSpace.single i (1 : ℝ)) (hInt _)
            (a := B - logMGFVec (X 0) μ (EuclideanSpace.single i (1 : ℝ))) ?_ n).trans
            (hexp _ hb.1)
          intro x hx
          rw [inner_single_one]
          have : B < x i := hx
          linarith
        · refine (empiricalMeanMeasureVec_le hXmeas hXindep hXident
            (measurableSet_lt (by fun_prop) measurable_const)
            (ξ := -EuclideanSpace.single i (1 : ℝ)) (hInt _)
            (a := B - logMGFVec (X 0) μ (-EuclideanSpace.single i (1 : ℝ))) ?_ n).trans
            (hexp _ hb.2)
          intro x hx
          rw [inner_neg_left, inner_single_one]
          have : x i < -B := hx
          linarith
    _ = 2 * d * ENNReal.ofReal (Real.exp (-(n * ℓ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Local Chernoff bound near a point.** Under finite exponential moments, if `q < Λ*(x)`,
then some open neighbourhood `U` of `x` (an open half-space) has `μₙ(U) ≤ exp (-n q)` for
every `n`. -/
theorem exists_isOpen_empiricalMeanMeasureVec_le (hXmeas : ∀ i, Measurable (X i))
    (hXindep : iIndepFun X μ) (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X 0 ω⟫_ℝ) μ)
    {x : EuclideanSpace ℝ (Fin d)} {q : ℝ} (hq : (q : EReal) < cramerRateFunction (X 0) μ x) :
    ∃ U : Set (EuclideanSpace ℝ (Fin d)), IsOpen U ∧ x ∈ U ∧ ∀ n : ℕ,
      empiricalMeanMeasureVec X μ n U ≤ ENNReal.ofReal (Real.exp (-(n * q))) := by
  by_cases hq0 : q < 0
  · refine ⟨univ, isOpen_univ, mem_univ _, fun n => ?_⟩
    have := isProbabilityMeasure_empiricalMeanMeasureVec (μ := μ) X n
    rw [measure_univ]
    refine ENNReal.one_le_ofReal.2 (Real.one_le_exp ?_)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  push Not at hq0
  have hcoe : ((ENNReal.ofReal q : ℝ≥0∞) : EReal) = q := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left hq0]
  rw [← hcoe, EReal.coe_ennreal_lt_coe_ennreal_iff,
    cramerRateFunction_eq_iSup_of_integrable (X 0) hInt, lt_iSup_iff] at hq
  obtain ⟨t, ht⟩ := hq
  have ht' : q < ⟪t, x⟫_ℝ - logMGFVec (X 0) μ t := (ENNReal.ofReal_lt_ofReal_iff'.1 ht).1
  refine ⟨{y | q < ⟪t, y⟫_ℝ - logMGFVec (X 0) μ t},
    isOpen_lt continuous_const (by fun_prop), ht', fun n => ?_⟩
  exact empiricalMeanMeasureVec_le hXmeas hXindep hXident
    (measurableSet_lt measurable_const (by fun_prop)) (hInt t) (fun y hy => le_of_lt hy) n

/-- **Chernoff bound on a compact set.** Under finite exponential moments, if `D` is compact
and `q < Λ*` on `D`, then `μₙ(D) ≤ M exp (-n q)` for every `n`, for some finite constant `M`
(covering `D` by finitely many open half-spaces). -/
theorem exists_empiricalMeanMeasureVec_le_of_isCompact (hXmeas : ∀ i, Measurable (X i))
    (hXindep : iIndepFun X μ) (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X 0 ω⟫_ℝ) μ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : IsCompact D) {q : ℝ}
    (hq : ∀ x ∈ D, (q : EReal) < cramerRateFunction (X 0) μ x) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n : ℕ,
      empiricalMeanMeasureVec X μ n D ≤ M * ENNReal.ofReal (Real.exp (-(n * q))) := by
  refine hD.induction_on (p := fun s => ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n : ℕ,
      empiricalMeanMeasureVec X μ n s ≤ M * ENNReal.ofReal (Real.exp (-(n * q)))) ?_ ?_ ?_ ?_
  · exact ⟨0, ENNReal.zero_ne_top, fun n => by simp⟩
  · rintro s t hst ⟨M, hM, h⟩
    exact ⟨M, hM, fun n => (measure_mono hst).trans (h n)⟩
  · rintro s t ⟨M₁, hM₁, h₁⟩ ⟨M₂, hM₂, h₂⟩
    refine ⟨M₁ + M₂, ENNReal.add_ne_top.2 ⟨hM₁, hM₂⟩, fun n => ?_⟩
    exact (measure_union_le _ _).trans ((add_le_add (h₁ n) (h₂ n)).trans_eq (add_mul _ _ _).symm)
  · intro x hx
    obtain ⟨U, hU, hxU, hev⟩ :=
      exists_isOpen_empiricalMeanMeasureVec_le hXmeas hXindep hXident hInt (hq x hx)
    exact ⟨U, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU), 1, ENNReal.one_ne_top,
      fun n => by rw [one_mul]; exact hev n⟩

/-- **Cramér upper bound for closed sets.** Let `X₀, X₁, …` be measurable i.i.d. random
vectors in `ℝᵈ` on a probability space with `E[exp ⟪t, X₀⟫] < ∞` for every `t`. Then for every
closed `F`, `limsup (1/n) log μₙ(F) ≤ -inf_F Λ*`, where `μₙ` is the law of the empirical mean.

Source: S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University,
Spring 2010, Section 1 and Exercise 2 there (https://math.nyu.edu/~varadhan/LDP/1-2.pdf):
Chebyshev's inequality in half-spaces and a covering argument; see also A. Dembo and
O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Section 2.2. -/
theorem limsup_log_empiricalMeanMeasureVec_le (hXmeas : ∀ i, Measurable (X i))
    (hXindep : iIndepFun X μ) (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d), Integrable (fun ω => Real.exp ⟪t, X 0 ω⟫_ℝ) μ)
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : IsClosed F) :
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ *
        ENNReal.log (empiricalMeanMeasureVec X μ n F)) atTop ≤
      -(⨅ x ∈ F, (cramerRateFunction (X 0) μ x : EReal)) := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  rw [EReal.neg_lt_comm] at hc
  obtain ⟨q, hcq, hqm⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  obtain ⟨q', hcq', hq'q⟩ := EReal.lt_iff_exists_real_btwn.1 hcq
  rw [EReal.coe_lt_coe_iff] at hq'q
  have hq'c : ((-q' : ℝ) : EReal) ≤ c := by
    rw [EReal.coe_neg]
    exact (EReal.neg_lt_comm.1 hcq').le
  refine le_trans ?_ hq'c
  obtain ⟨K, hK, hKμ⟩ :=
    exists_isCompact_empiricalMeanMeasureVec_compl_le hXmeas hXindep hXident hInt q
  obtain ⟨M, hM, hMb⟩ := exists_empiricalMeanMeasureVec_le_of_isCompact hXmeas hXindep
    hXident hInt (hK.inter_left hF) (q := q) fun x hx =>
      hqm.trans_le (iInf₂_le (f := fun x (_ : x ∈ F) =>
        ((cramerRateFunction (X 0) μ x : ℝ≥0∞) : EReal)) x hx.1)
  have hfin : M + 2 * d ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hM, ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top d)⟩
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_mul_ofReal_exp_le hfin hq'q, eventually_gt_atTop 0]
    with n hfinn hn0
  rw [inv_mul_log_le_coe_iff hn0, mul_neg]
  calc empiricalMeanMeasureVec X μ n F
      ≤ empiricalMeanMeasureVec X μ n (F ∩ K) + empiricalMeanMeasureVec X μ n Kᶜ := by
        refine (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
        by_cases hxK : x ∈ K
        · exact Or.inl ⟨hx, hxK⟩
        · exact Or.inr hxK
    _ ≤ M * ENNReal.ofReal (Real.exp (-(n * q))) +
          2 * d * ENNReal.ofReal (Real.exp (-(n * q))) := add_le_add (hMb n) (hKμ n)
    _ = (M + 2 * d) * ENNReal.ofReal (Real.exp (-(n * q))) := (add_mul _ _ _).symm
    _ ≤ ENNReal.ofReal (Real.exp (-(n * q'))) := hfinn

end MathlibExt.Probability.CramerLDPUpperBound
