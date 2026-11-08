/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Fixed-direction Chernoff bounds for empirical means

For measurable i.i.d. random vectors `X₀, X₁, …` in `ℝᵈ` on a probability space,
fix a direction `ξ ∈ ℝᵈ` such that `exp ⟪ξ, X₀⟫` is integrable. The laws `μₙ`
of the empirical means `Aₙ = (1/n) ∑_{i<n} Xᵢ` satisfy, for every measurable set
`F` and every real `a` that lower-bounds `⟪ξ, ·⟫ - Λ(ξ)` on `F`
(where `Λ(ξ) = log E[exp ⟪ξ, X₀⟫]`),

`μₙ(F) ≤ exp(-n * a)`.

This is a fixed-direction Chernoff bound for the empirical mean. Its proof applies
Markov's inequality to `exp ⟪ξ, Sₙ⟫` and uses independence to factor the exponential
moment of the sum. For fixed `ξ`, the asymptotic rate is
`inf_{x ∈ F} (⟪ξ, x⟫ - Λ(ξ))`. Optimizing these bounds gives
`sup_ξ inf_{x ∈ F} (⟪ξ, x⟫ - Λ(ξ))`. Obtaining the Cramér upper bound with
`inf_{x ∈ F} Λ*(x)`, where `Λ*(x) = sup_ξ (⟪ξ, x⟫ - Λ(ξ))`, requires further
arguments and hypotheses. For `Λ(ξ) = ξ²/2` and `F = {-1, 1}`, these two optimized
rates are respectively `0` and `1/2`.

Here optimization is over directions in the exponential-integrability domain.

The exponential-integrability assumption is required for these bounds. The
real-valued `logMGFVec` below uses the totalized Bochner integral and `Real.log`;
outside exponential integrability it has value `0`, rather than an infinite MGF.

Source: `v1/Atlas/TheoryOfProbability/code/CramerTheorem.lean`, `cramer_theorem`
(Lecture 13). In v1 the full Cramér theorem (both bounds, with the limiting
large deviation principle and convexity of the rate function) is left unproved.
Here we prove the fixed-direction Chernoff estimate used in that argument. The
Legendre-rate large-deviation upper bound and the lower bound by change of
measure or tilting remain unproved here. The definitions `empiricalMeanMeasureVec`
and `logMGFVec` are ported verbatim from v1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped InnerProductSpace ENNReal

namespace MathlibExt.Probability.CramerUpperBound

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Law of the empirical mean** `Aₙ = (1/n) ∑_{i<n} Xᵢ` for an `ℝᵈ`-valued sample.

Pushforward of `μ` under the map `ω ↦ (1/n) ∑_{i<n} Xᵢ(ω)`. Ported verbatim
from v1. -/
noncomputable def empiricalMeanMeasureVec {d : ℕ} (X : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) (n : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  μ.map (fun ω => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω))

/-- **Real-valued log-MGF expression** `Λ(t) = log E[exp ⟪t, X⟫]`.

For a random vector `X : Ω → ℝᵈ`, this returns the logarithm of the moment
generating function evaluated at the dual variable `t ∈ ℝᵈ`, using the Euclidean
inner product. Under a probability measure it represents the cumulant generating
function at directions where the exponential is integrable. For a nonintegrable
exponential, the Bochner integral is `0` and `Real.log 0 = 0`, so this definition
returns `0`. The bounds below explicitly require exponential integrability.
Ported from v1. -/
noncomputable def logMGFVec {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) (t : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.log (∫ ω, Real.exp ⟪t, X ω⟫_ℝ ∂μ)

/-- **Chernoff bound for the empirical mean of real-valued i.i.d. variables**,
in event form: if on the event `E` the empirical mean
`(1/n) ∑_{i<n} Xᵢ` satisfies the threshold inequality
`a ≤ t * (empirical mean) - log (mgf of X₁ at t)`, then
`μ(E) ≤ exp(-n * a)`.

Assume a probability measure, measurable independent identically distributed
coordinates, and integrability of `exp (t * X₀)`.

This is the one-dimensional core of the Cramér upper bound. The proof splits
on the sign of `t`: for `t > 0` it applies Mathlib's upper-tail Chernoff bound
to the sum `Sₙ`, and for `t < 0` the lower-tail Chernoff bound; in both cases
the exponential moment of the sum factors as `(mgf of X₁ at t)^n` by
independence and identical distribution. -/
theorem measure_empiricalMean_le_of_threshold {X : ℕ → Ω → ℝ}
    [IsProbabilityMeasure μ]
    (hXmeas : ∀ i, Measurable (X i)) (hXindep : iIndepFun X μ)
    (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {t a : ℝ} (hInt : Integrable (fun ω => Real.exp (t * X 0 ω)) μ)
    {n : ℕ} (hn : 0 < n) {E : Set Ω}
    (hEthr : ∀ ω ∈ E, a ≤ t * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω)
      - Real.log (mgf (X 0) μ t)) :
    (μ E).toReal ≤ Real.exp (-(n : ℝ) * a) := by
  set M : ℝ := mgf (X 0) μ t with hM
  set L : ℝ := Real.log M with hL
  have hMpos : 0 < M := mgf_pos hInt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR' : (n : ℝ) ≠ 0 := ne_of_gt hnR
  -- Integrability of each exponential factor.
  have hIntY : ∀ i, Integrable (fun ω => Real.exp (t * X i ω)) μ := by
    intro i
    have hcomp := (hXident i).comp
      (show Measurable (fun x : ℝ => Real.exp (t * x)) from by fun_prop)
    exact hcomp.integrable_iff.mpr hInt
  -- Independence of the exponentiated variables.
  have hXindep' : iIndepFun (fun i ω => Real.exp (t * X i ω)) μ :=
    hXindep.comp (fun _ => fun x => Real.exp (t * x)) (fun _ => (measurable_const_mul t).exp)
  -- Integrability of the product of the exponential factors.
  have hIntProd : ∀ m, Integrable (fun ω => ∏ i ∈ Finset.range m, Real.exp (t * X i ω)) μ := by
    intro m
    induction m with
    | zero =>
      show Integrable (fun _ => (1 : ℝ)) μ
      exact integrable_const (1 : ℝ)
    | succ m ih =>
      have ih' : Integrable (∏ j ∈ Finset.range m, fun ω => Real.exp (t * X j ω)) μ := by
        have hfun : (∏ j ∈ Finset.range m, fun ω => Real.exp (t * X j ω))
            = fun ω => ∏ i ∈ Finset.range m, Real.exp (t * X i ω) := by
          funext ω
          simp only [Finset.prod_apply]
        rw [hfun]
        exact ih
      have hprod : (fun ω => ∏ i ∈ Finset.range (m + 1), Real.exp (t * X i ω))
          = (∏ j ∈ Finset.range m, fun ω => Real.exp (t * X j ω))
            * (fun ω => Real.exp (t * X m ω)) := by
        funext ω
        simp [Finset.prod_range_succ, Finset.prod_apply]
      rw [hprod]
      exact (hXindep'.indepFun_finsetProd_of_notMem
        (fun i => ((measurable_const_mul t).exp.comp (hXmeas i)))
        (fun h => Nat.lt_irrefl m (Finset.mem_range.mp h))).integrable_mul ih' (hIntY m)
  -- Integrability of the exponential of the sum.
  have hIntSum : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range n, X i ω)) μ := by
    have heq : (fun ω => Real.exp (t * ∑ i ∈ Finset.range n, X i ω))
        = (fun ω => ∏ i ∈ Finset.range n, Real.exp (t * X i ω)) := by
      funext ω
      rw [Finset.mul_sum, Real.exp_sum]
    rw [heq]
    exact hIntProd n
  -- The mgf of the sum is the n-th power of the mgf of one summand.
  have hmgfS : mgf (fun ω => ∑ i ∈ Finset.range n, X i ω) μ t = M ^ n := by
    have h := mgf_sum_of_identDistrib (μ := μ) (s := Finset.range n) (j := 0)
      (fun i => hXmeas i) hXindep
      (fun i _ j _ => (hXident i).trans (hXident j).symm)
      (Finset.mem_range.mpr hn) t
    rw [Finset.card_range] at h
    rw [← h]
    congr 1
    funext ω
    rw [Finset.sum_apply]
  -- The case `t = 0`: the threshold forces `a ≤ 0`, and the bound is trivial.
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    rcases E.eq_empty_or_nonempty with hEempty | hEne
    · rw [hEempty, MeasureTheory.measure_empty, ENNReal.toReal_zero]
      exact Real.exp_nonneg _
    · obtain ⟨ω₀, hω₀⟩ := hEne
      have hL0 : L = 0 := by simp [hL, hM]
      have ha0 : a ≤ 0 := by
        have h0 := hEthr ω₀ hω₀
        rw [hL0] at h0
        linarith
      calc (μ E).toReal ≤ 1 := by
            have : (μ E).toReal ≤ (μ Set.univ).toReal :=
              ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
            rwa [measure_univ, ENNReal.toReal_one] at this
        _ ≤ Real.exp (-(n : ℝ) * a) :=
            Real.one_le_exp (by nlinarith [ha0, hnR])
  -- The case `t ≠ 0`: Chernoff on the sum, with threshold `n * (a + L) / t`.
  have hthr : ∀ ω ∈ E, (a + L) ≤ t * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω) := by
    intro ω hω
    have h := hEthr ω hω
    linarith
  set S : Ω → ℝ := fun ω => ∑ i ∈ Finset.range n, X i ω with hS
  set ε : ℝ := (n : ℝ) * (a + L) / t with hε
  have hε_mul : t * ε = (n : ℝ) * (a + L) := by
    rw [hε, mul_div_cancel₀ _ ht]
  have hkey : (μ E).toReal ≤ Real.exp (-t * ε) * M ^ n := by
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · have hsub : E ⊆ {ω | S ω ≤ ε} := by
        intro ω hω
        have h1 : (a + L) ≤ t * ((n : ℝ)⁻¹ * S ω) := hthr ω hω
        have h2 : (n : ℝ) * (a + L) ≤ S ω * t := by
          have h3 : (n : ℝ) * (t * ((n : ℝ)⁻¹ * S ω)) = t * S ω := by
            have hnn : (n : ℝ) * ((n : ℝ)⁻¹ * S ω) = S ω := by
              rw [← mul_assoc, mul_inv_cancel₀ hnR', one_mul]
            calc (n : ℝ) * (t * ((n : ℝ)⁻¹ * S ω))
                = t * ((n : ℝ) * ((n : ℝ)⁻¹ * S ω)) := by ring
              _ = t * S ω := by rw [hnn]
          have h4 : (n : ℝ) * (a + L) ≤ (n : ℝ) * (t * ((n : ℝ)⁻¹ * S ω)) :=
            mul_le_mul_of_nonneg_left h1 hnR.le
          rw [h3] at h4
          rw [mul_comm (S ω) t]
          exact h4
        show S ω ≤ (n : ℝ) * (a + L) / t
        rw [le_div_iff_of_neg htneg]
        exact h2
      calc (μ E).toReal ≤ μ.real {ω | S ω ≤ ε} :=
            measureReal_mono hsub
        _ ≤ Real.exp (-t * ε) * mgf S μ t :=
            measure_le_le_exp_mul_mgf ε htneg.le hIntSum
        _ = Real.exp (-t * ε) * M ^ n := by rw [hmgfS]
    · have hsub : E ⊆ {ω | ε ≤ S ω} := by
        intro ω hω
        have h1 : (a + L) ≤ t * ((n : ℝ)⁻¹ * S ω) := hthr ω hω
        have h2 : (n : ℝ) * (a + L) ≤ S ω * t := by
          have h3 : (n : ℝ) * (t * ((n : ℝ)⁻¹ * S ω)) = t * S ω := by
            have hnn : (n : ℝ) * ((n : ℝ)⁻¹ * S ω) = S ω := by
              rw [← mul_assoc, mul_inv_cancel₀ hnR', one_mul]
            calc (n : ℝ) * (t * ((n : ℝ)⁻¹ * S ω))
                = t * ((n : ℝ) * ((n : ℝ)⁻¹ * S ω)) := by ring
              _ = t * S ω := by rw [hnn]
          have h4 : (n : ℝ) * (a + L) ≤ (n : ℝ) * (t * ((n : ℝ)⁻¹ * S ω)) :=
            mul_le_mul_of_nonneg_left h1 hnR.le
          rw [h3] at h4
          rw [mul_comm (S ω) t]
          exact h4
        show (n : ℝ) * (a + L) / t ≤ S ω
        rw [div_le_iff₀ htpos]
        exact h2
      calc (μ E).toReal ≤ μ.real {ω | ε ≤ S ω} :=
            measureReal_mono hsub
        _ ≤ Real.exp (-t * ε) * mgf S μ t :=
            measure_ge_le_exp_mul_mgf ε htpos.le hIntSum
        _ = Real.exp (-t * ε) * M ^ n := by rw [hmgfS]
  -- Simplify `exp(-t * ε) * M^n = exp(-n * a)` using `M = exp L`.
  have hMexp : M = Real.exp L := (Real.exp_log hMpos).symm
  have hfinal : Real.exp (-t * ε) * M ^ n = Real.exp (-(n : ℝ) * a) := by
    rw [neg_mul, hε_mul, hMexp, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rwa [hfinal] at hkey

/-- **Fixed-direction Chernoff bound.** For i.i.d. random vectors in `ℝᵈ`,
the law `μₙ` of the empirical mean satisfies `μₙ(F) ≤ exp(-n * a)` whenever
`a` lower-bounds `⟪ξ, ·⟫ - Λ(ξ)` on measurable `F`. Assume a probability measure,
measurable coordinates and integrability of `exp ⟪ξ, X₀⟫` at this direction. -/
theorem cramer_upper_bound {d : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    [IsProbabilityMeasure μ]
    (hXmeas : ∀ i, Measurable (X i)) (hXindep : iIndepFun X μ)
    (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : MeasurableSet F)
    {ξ : EuclideanSpace ℝ (Fin d)} {a : ℝ}
    (hInt : Integrable (fun ω => Real.exp ⟪ξ, X 0 ω⟫_ℝ) μ)
    (ha : ∀ x ∈ F, a ≤ ⟪ξ, x⟫_ℝ - logMGFVec (X 0) μ ξ) (n : ℕ) :
    ((empiricalMeanMeasureVec X μ n) F).toReal ≤ Real.exp (-(n : ℝ) * a) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hA0 : (fun ω => ((0 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range 0, X i ω)
        = fun _ => (0 : EuclideanSpace ℝ (Fin d)) := by
      funext ω
      simp
    have htop : (empiricalMeanMeasureVec X μ 0) Set.univ = 1 := by
      unfold empiricalMeanMeasureVec
      rw [hA0, Measure.map_apply measurable_const MeasurableSet.univ,
        Set.preimage_univ, measure_univ]
    have h1 : ((empiricalMeanMeasureVec X μ 0) F).toReal ≤ 1 := by
      calc ((empiricalMeanMeasureVec X μ 0) F).toReal
          ≤ ((empiricalMeanMeasureVec X μ 0) Set.univ).toReal :=
            ENNReal.toReal_mono (by rw [htop]; exact ENNReal.one_ne_top)
              (measure_mono (Set.subset_univ _))
        _ = 1 := by rw [htop, ENNReal.toReal_one]
    simpa using h1
  -- Reduce to the one-dimensional bound applied to `Yᵢ = ⟪ξ, Xᵢ⟫`.
  set Y : ℕ → Ω → ℝ := fun i ω => ⟪ξ, X i ω⟫_ℝ with hY
  have hinnerMeas : Measurable (fun x : EuclideanSpace ℝ (Fin d) => ⟪ξ, x⟫_ℝ) := by
    simpa [innerSL_apply_apply] using (innerSL ℝ ξ).continuous.measurable
  have hYmeas : ∀ i, Measurable (Y i) := fun i => hinnerMeas.comp (hXmeas i)
  have hYindep : iIndepFun Y μ :=
    hXindep.comp (fun _ => fun x => ⟪ξ, x⟫_ℝ) (fun _ => hinnerMeas)
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i =>
    (hXident i).comp hinnerMeas
  have hIntY : Integrable (fun ω => Real.exp (1 * Y 0 ω)) μ := by
    simpa [hY] using hInt
  have hIntPos : (0 : ℝ) < ∫ ω, Real.exp ⟪ξ, X 0 ω⟫_ℝ ∂μ := by
    have hpos : (0 : ℝ) < mgf (Y 0) μ 1 := mgf_pos hIntY
    simpa [mgf, hY, one_mul] using hpos
  have hmgfY : mgf (Y 0) μ 1 = Real.exp (logMGFVec (X 0) μ ξ) := by
    rw [logMGFVec, Real.exp_log hIntPos]
    simp [mgf, hY, one_mul]
  have hlogY : Real.log (mgf (Y 0) μ 1) = logMGFVec (X 0) μ ξ := by
    rw [hmgfY, Real.log_exp]
  -- The event whose measure is `μₙ(F)`.
  set A : Ω → EuclideanSpace ℝ (Fin d) :=
    fun ω => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω) with hA
  set E : Set Ω := A ⁻¹' F with hE
  have hμn : (empiricalMeanMeasureVec X μ n) F = μ E := by
    rw [empiricalMeanMeasureVec, Measure.map_apply (by fun_prop : Measurable A) hF]
  rw [hμn]
  apply measure_empiricalMean_le_of_threshold (t := 1) hYmeas hYindep hYident hIntY hn
  intro ω hω
  have hωF : A ω ∈ F := hω
  have hξA : ⟪ξ, A ω⟫_ℝ = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, Y i ω := by
    rw [hA]
    simp [inner_smul_right, inner_sum, hY]
  have h1 : a ≤ ⟪ξ, A ω⟫_ℝ - logMGFVec (X 0) μ ξ := ha _ hωF
  rw [hξA, ← hlogY] at h1
  simpa using h1

/-- **Fixed-direction Chernoff bound, rate form.** For a fixed `ξ` and
`s = inf_{x ∈ F} (⟪ξ, x⟫ - Λ(ξ))`, the `n`-th root of `μₙ(F)` has limsup at most
`exp(-s)`. Assume measurable i.i.d. coordinates under a probability measure,
measurable `F`, exponential integrability at `ξ`, and a bounded-below rate image
on `F`, with its real-valued `sInf` used for `s`.
Optimizing over admissible `ξ` gives the supremum of these fixed-direction rates;
the Legendre-rate Cramér upper bound requires further arguments. -/
theorem cramer_upper_bound_rate {d : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    [IsProbabilityMeasure μ]
    (hXmeas : ∀ i, Measurable (X i)) (hXindep : iIndepFun X μ)
    (hXident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : MeasurableSet F)
    {ξ : EuclideanSpace ℝ (Fin d)}
    (hInt : Integrable (fun ω => Real.exp ⟪ξ, X 0 ω⟫_ℝ) μ)
    (hBdd : BddBelow ((fun x => ⟪ξ, x⟫_ℝ - logMGFVec (X 0) μ ξ) '' F)) :
    limsup (fun n : ℕ => ((empiricalMeanMeasureVec X μ n) F).toReal ^ (1 / (n : ℝ)))
        atTop ≤
      Real.exp (-sInf ((fun x => ⟪ξ, x⟫_ℝ - logMGFVec (X 0) μ ξ) '' F)) := by
  set s : ℝ := sInf ((fun x => ⟪ξ, x⟫_ℝ - logMGFVec (X 0) μ ξ) '' F) with hs
  have hs_le : ∀ x ∈ F, s ≤ ⟪ξ, x⟫_ℝ - logMGFVec (X 0) μ ξ := fun x hx =>
    csInf_le hBdd ⟨x, hx, rfl⟩
  have hEv : ∀ᶠ n in atTop,
      ((empiricalMeanMeasureVec X μ n) F).toReal ^ (1 / (n : ℝ)) ≤ Real.exp (-s) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : 0 < n := hn
    have hbound := cramer_upper_bound hXmeas hXindep hXident hF hInt hs_le n
    have hbase : (0 : ℝ) ≤ ((empiricalMeanMeasureVec X μ n) F).toReal :=
      ENNReal.toReal_nonneg
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn'
    calc ((empiricalMeanMeasureVec X μ n) F).toReal ^ (1 / (n : ℝ))
        ≤ (Real.exp (-(n : ℝ) * s)) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow hbase hbound (by positivity)
      _ = Real.exp (-s) := by
          rw [← Real.exp_mul]
          congr 1
          field_simp
  have hco : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => ((empiricalMeanMeasureVec X μ n) F).toReal ^ (1 / (n : ℝ))) := by
    refine ⟨0, fun b hb => ?_⟩
    rw [Filter.eventually_map] at hb
    obtain ⟨n, hn1, _hn2⟩ := (hb.and (eventually_ge_atTop 1)).exists
    have hnn : (0 : ℝ) ≤ ((empiricalMeanMeasureVec X μ n) F).toReal ^ (1 / (n : ℝ)) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    linarith [hn1, hnn]
  exact limsup_le_of_le hco hEv

end MathlibExt.Probability.CramerUpperBound
