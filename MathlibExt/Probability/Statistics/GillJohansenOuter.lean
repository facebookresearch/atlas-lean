/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ContinuousProductIntegral

/-!
# The Gill–Johansen product-integral limit with outer probability

`MathlibExt.Probability.Statistics.ContinuousProductIntegral` (T78) proves Hadamard
differentiability of the product integral and derives the continuous-time Kaplan–Meier limit law
in Mathlib's Borel framework (`MeasureTheory.TendstoInDistribution`). On the nonseparable space
`ℓ^∞([0, τ])` that framework is too restrictive: its measurability hypotheses fail on the canonical
space of the observations for every failure-time law with a non-atomic part (see the module
docstrings of T78 and of `MathlibExt.Probability.Statistics.FunctionalDelta`). This file sets up
the **outer-probability (Hoffmann-Jørgensen) framework** of van der Vaart–Wellner and proves the
functional delta theorem and the Gill–Johansen product-integral limit in it, with **no
measurability hypothesis on the processes**.

## The outer-probability / `ℓ^∞` framework

Throughout, `(Ω, μ)` is a probability space and the processes `Xₙ : Ω → E` are arbitrary maps
into a metric space `E` (no measurability). `E` carries its Borel σ-algebra, which is used only
for the limit law.

* **Outer probability.** For an arbitrary set `s ⊆ Ω`, Mathlib's `μ s` is already the outer
  measure `inf {μ t | s ⊆ t, t measurable}`; so `μ (X n ⁻¹' F)` below is the outer probability
  `P*(Xₙ ∈ F)` of van der Vaart–Wellner, §1.2.
* **Outer integral** `outerLIntegral μ f = inf {∫⁻ g dμ | g measurable, f ≤ g a.e.}` for
  `f : Ω → ℝ≥0∞` (van der Vaart–Wellner, §1.2, for nonnegative `f`). Van der Vaart–Wellner ask
  `f ≤ g` everywhere; this gives the same value, since `g + ∞ · 𝟙_N` with `N` a measurable null
  set containing `{f > g}` is an everywhere majorant with the same integral
  (`outerLIntegral_eq_iInf_le`). It equals the Lebesgue
  integral for a.e.-measurable `f` (`outerLIntegral_eq_lintegral`) and is in general strictly
  larger than Mathlib's (lower) `lintegral`.
* **Weak convergence** `TendstoInDistributionOuter X μ L` (Hoffmann-Jørgensen; van der
  Vaart–Wellner, Definition 1.3.3): the limit is a Borel probability measure `L` on `E`, and
  `E* f(Xₙ) → ∫ f dL` for every bounded continuous `f : E → ℝ≥0`. Van der Vaart–Wellner test with
  real-valued `f`; the two are equivalent because adding a constant `c` to `f` adds `c` to the
  outer expectation under a probability measure. The limit is not required to be separable or
  tight; no separability of `E` is assumed.

`ℓ^∞([0, τ])` is Mathlib's `lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞` with the sup norm, as in T78.

## Main statements

* `TendstoInDistributionOuter.limsup_measure_le` and
  `TendstoInDistributionOuter.of_forall_isClosed_limsup_le`: the **portmanteau theorem for outer
  weak convergence** (closed-set form, van der Vaart–Wellner, Theorem 1.3.4 (i) ⇔ (iii)).
* `TendstoInDistribution.tendstoInDistributionOuter`: Borel weak convergence of measurable
  processes implies outer weak convergence to the same law (the framework extends Mathlib's).
* `TendstoInDistributionOuter.extended_comp`: the **extended continuous mapping theorem**
  (van der Vaart–Wellner, Theorem 1.11.1 (i); van der Vaart, Theorem 18.11 (i)) for outer weak
  convergence, with the domain condition in outer probability: `P*(Uₙ ∉ Dₙ) → 0`.
* `TendstoInDistributionOuter.functional_delta`: the **functional delta theorem** (van der Vaart,
  Theorem 20.8; van der Vaart–Wellner, Theorem 3.9.4) for outer weak convergence, with no
  measurability hypotheses and with `P*(Xₙ ∉ D) → 0` in place of `Xₙ ∈ D` almost surely.
* `IsDuhamelProductIntegral.tendstoInDistributionOuter`: the **Gill–Johansen product-integral
  limit**: if `rₙ (Aₙ - A) ⇝ L` (outer) with `L` concentrated on the closure of the continuity
  class, then `rₙ (P(Aₙ) - P(A)) ⇝ L ∘ (Ψ A A)⁻¹`, the law of the Duhamel integral
  `Ψ A A Z = ∫_{(0, ·]} P(A)(0, s) dZ(s) P(A)(s, ·]` of the limit `Z ∼ L`.
* `tendstoInDistributionOuter_kmSurvival_lInfty`: the **continuous-time Kaplan–Meier limit law in
  `ℓ^∞([0, τ])` with outer probability**: from an outer Nelson–Aalen CLT
  `√n (Λ̂ₙ - Λ) ⇝ L`, `√n (Ŝₙ - S) ⇝ L ∘ (-Ψ(-Λ, -Λ))⁻¹`.

## What is proved and what is still assumed

Compared with T78's `tendstoInDistribution_kmSurvival_lInfty`, the Kaplan–Meier theorem here
* has **no measurability hypotheses** (T78's `hCLT` measurability fields and `hmeas` are gone),
  so it does not exclude failure-time laws with a non-atomic part;
* asks only `P*(-Λ̂ₙ ∉ D) → 0` (`hdom`) instead of `-Λ̂ₙ ∈ D` almost surely for every `n`; for a
  total-variation ball `D` of radius larger than `Λ(τ)` this is the usual consistency of the
  Nelson–Aalen estimator, whereas the almost-sure version fails for continuous failure times.

Still assumed, exactly:
* the **product integral** and its Duhamel operator, through T78's hypothesis bundle
  `IsStieltjesProductIntegral τ P Ψ D S C` (the Lebesgue–Stieltjes construction of T77 is not
  connected to it; that bridge, building `Ψ A B` as a continuous linear map on `ℓ^∞`, is a
  separate deferred task);
* the **outer Nelson–Aalen functional CLT** `√n (Λ̂ₙ - Λ) ⇝ L` (`hCLT`), with the limit law `L`
  carried by `{h | -h ∈ closure S}` (`hL`); the martingale CLT that proves it is a separate task;
* the domain condition `hdom` in outer probability (a consistency statement for `Λ̂ₙ`).

The derivative is T44's one-sided directional Hadamard derivative `HasHadamardDerivWithinAt`
(implied by the usual one). Sequences are indexed by `ℕ` with `atTop` and live on one
probability space `(Ω, μ)`, as in T78.

## Source receipt (reuse search, 2026-11-13)

Mathlib v4.35.0 has no outer integral, no outer (Hoffmann-Jørgensen) weak convergence, and no
extended continuous mapping theorem. Reused: Mathlib's outer-measure evaluation `μ s` of arbitrary
sets, `HasOuterApproxClosed` (closed-set approximation by bounded continuous functions),
`ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto`, the ENNReal `limsup` lemmas;
T44's `HasHadamardDerivWithinAt` (`MathlibExt.Probability.Statistics.FunctionalDelta`); T78's
`IsDuhamelProductIntegral`, `IsStieltjesProductIntegral`, their Hadamard derivatives
`IsDuhamelProductIntegral.hasHadamardDerivWithinAt` and
`IsStieltjesProductIntegral.hasHadamardDerivWithinAt_neg`, and the identification of the
Kaplan–Meier estimate as a pure-jump product integral (`IsStieltjesProductIntegral.pureJump`);
`CensoredData.kmSurvival` / `CensoredData.nelsonAalen`. Proved here: the outer integral and its
properties, both portmanteau directions for outer weak convergence (the converse by a Riemann-sum
bound, since the outer integral has no layer-cake formula), the outer extended continuous mapping
theorem, the outer functional delta theorem, and the Gill–Johansen and Kaplan–Meier corollaries.
The proofs of the extended continuous mapping and delta theorems follow T44's Borel proofs with
outer probabilities in place of laws.

## References

* A. W. van der Vaart and J. A. Wellner, *Weak Convergence and Empirical Processes* (1996),
  §1.2, Definition 1.3.3, Theorem 1.3.4, Theorem 1.11.1, Theorem 3.9.4.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), Theorem 18.11, Theorem 20.8, §20.3.
* R. D. Gill and S. Johansen, *A survey of product-integration with a view toward application in
  survival analysis*, Ann. Statist. 18 (1990), 1501–1555.
* J. Hoffmann-Jørgensen, *Stochastic Processes on Polish Spaces* (1991; manuscript 1984).
-/

@[expose] public section

open Filter Topology MeasureTheory Finset
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MathlibExt.Probability.Statistics.GillJohansenOuter

open MathlibExt.Probability.Statistics.FunctionalDelta
open MathlibExt.Probability.Statistics.ContinuousProductIntegral

section OuterIntegral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The **outer integral** of an arbitrary (possibly non-measurable) `f : Ω → ℝ≥0∞`:
`E* f = inf {∫⁻ g dμ | g measurable, f ≤ g μ-a.e.}` (van der Vaart–Wellner, §1.2). -/
noncomputable def outerLIntegral (μ : Measure Ω) (f : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : f ≤ᵐ[μ] g), ∫⁻ ω, g ω ∂μ

/-- The outer integral is at most the integral of any measurable a.e. majorant. -/
theorem outerLIntegral_le_lintegral {f g : Ω → ℝ≥0∞} (hg : Measurable g) (hfg : f ≤ᵐ[μ] g) :
    outerLIntegral μ f ≤ ∫⁻ ω, g ω ∂μ :=
  iInf_le_of_le g (iInf_le_of_le hg (iInf_le _ hfg))

/-- The (lower) Lebesgue integral is at most the outer integral. -/
theorem lintegral_le_outerLIntegral (f : Ω → ℝ≥0∞) :
    ∫⁻ ω, f ω ∂μ ≤ outerLIntegral μ f :=
  le_iInf fun _ ↦ le_iInf fun _ ↦ le_iInf fun hfg ↦ lintegral_mono_ae hfg

/-- For a.e.-measurable functions the outer integral is the Lebesgue integral. -/
theorem outerLIntegral_eq_lintegral {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ) :
    outerLIntegral μ f = ∫⁻ ω, f ω ∂μ :=
  le_antisymm ((outerLIntegral_le_lintegral hf.measurable_mk hf.ae_eq_mk.le).trans_eq
    (lintegral_congr_ae hf.ae_eq_mk.symm)) (lintegral_le_outerLIntegral f)

/-- The outer integral with **everywhere** majorants (van der Vaart–Wellner's form) has the same
value: an a.e. majorant `g` becomes an everywhere majorant `g'` by setting it to `∞` on a
measurable null set containing `{f > g}`, without changing the integral. -/
theorem outerLIntegral_eq_iInf_le (f : Ω → ℝ≥0∞) :
    outerLIntegral μ f = ⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : f ≤ g), ∫⁻ ω, g ω ∂μ := by
  classical
  refine le_antisymm (le_iInf fun g ↦ le_iInf fun hg ↦ le_iInf fun hfg ↦
    outerLIntegral_le_lintegral hg (Eventually.of_forall hfg)) ?_
  refine le_iInf fun g ↦ le_iInf fun hg ↦ le_iInf fun hfg ↦ ?_
  set N := toMeasurable μ {ω | ¬ f ω ≤ g ω}
  have hN : μ N = 0 := by rw [measure_toMeasurable]; exact hfg
  let g' : Ω → ℝ≥0∞ := N.piecewise (fun _ ↦ ∞) g
  have hg' : Measurable g' := measurable_const.piecewise (measurableSet_toMeasurable _ _) hg
  have hfg' : f ≤ g' := fun ω ↦ by
    by_cases hω : ω ∈ N
    · simp [g', Set.piecewise_eq_of_mem _ _ _ hω]
    · rw [show g' ω = g ω from Set.piecewise_eq_of_notMem _ _ _ hω]
      by_contra h
      exact hω (subset_toMeasurable _ _ h)
  have hae : g' =ᵐ[μ] g := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with ω hω
    exact Set.piecewise_eq_of_notMem _ _ _ hω
  calc (⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : f ≤ g), ∫⁻ ω, g ω ∂μ) ≤ ∫⁻ ω, g' ω ∂μ :=
        iInf_le_of_le g' (iInf_le_of_le hg' (iInf_le _ hfg'))
    _ = ∫⁻ ω, g ω ∂μ := lintegral_congr_ae hae

/-- The outer integral is monotone. -/
theorem outerLIntegral_mono {f₁ f₂ : Ω → ℝ≥0∞} (h : f₁ ≤ f₂) :
    outerLIntegral μ f₁ ≤ outerLIntegral μ f₂ :=
  le_iInf fun _ ↦ le_iInf fun hg ↦ le_iInf fun hfg ↦
    outerLIntegral_le_lintegral hg ((show f₁ ≤ᵐ[μ] f₂ from Eventually.of_forall h).trans hfg)

/-- **Outer Markov bound**: if `f ≥ 1` on `s`, the outer probability of `s` is at most the outer
integral of `f`. -/
theorem measure_le_outerLIntegral {s : Set Ω} {f : Ω → ℝ≥0∞} (hf : ∀ ω ∈ s, 1 ≤ f ω) :
    μ s ≤ outerLIntegral μ f := by
  refine le_iInf fun g ↦ le_iInf fun hg ↦ le_iInf fun hfg ↦ ?_
  calc μ s ≤ μ {ω | 1 ≤ g ω} := by
        refine measure_mono_ae ?_
        filter_upwards [hfg] with ω hω hωs
        exact (hf ω hωs).trans hω
    _ ≤ ∫⁻ ω, g ω ∂μ := by simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hg.aemeasurable 1

/-- **Superadditivity bound**: if `M ≤ f₁ + f₂` pointwise, then `M ≤ E* f₁ + E* f₂` (a consequence
of the subadditivity of the outer integral). -/
theorem le_outerLIntegral_add [IsProbabilityMeasure μ] {f₁ f₂ : Ω → ℝ≥0∞} {M : ℝ≥0∞}
    (h : ∀ ω, M ≤ f₁ ω + f₂ ω) : M ≤ outerLIntegral μ f₁ + outerLIntegral μ f₂ := by
  simp only [outerLIntegral, ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun g₁ ↦ le_iInf fun hg₁ ↦ le_iInf fun h₁ ↦ le_iInf fun g₂ ↦ le_iInf fun hg₂ ↦
    le_iInf fun h₂ ↦ ?_
  rw [← lintegral_add_left hg₂]
  calc M = ∫⁻ _, M ∂μ := by simp
    _ ≤ ∫⁻ ω, g₂ ω + g₁ ω ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [h₂, h₁] with ω hω₁ hω₂
        exact (h ω).trans (add_le_add hω₁ hω₂)

/-- **Riemann-sum bound for the outer integral**: if
`f ≤ c + ∑_{i < k} c · 𝟙_{s i}` pointwise, then `E* f ≤ c + ∑_{i < k} c · P*(s i)`. -/
theorem outerLIntegral_le_const_add_sum [IsProbabilityMeasure μ] {f : Ω → ℝ≥0∞} {c : ℝ≥0∞}
    {k : ℕ} {s : ℕ → Set Ω}
    (h : ∀ ω, f ω ≤ c + ∑ i ∈ range k, (s i).indicator (fun _ ↦ c) ω) :
    outerLIntegral μ f ≤ c + ∑ i ∈ range k, c * μ (s i) := by
  set g : Ω → ℝ≥0∞ := fun ω ↦ c + ∑ i ∈ range k, (toMeasurable μ (s i)).indicator (fun _ ↦ c) ω
  have hgm : Measurable g := measurable_const.add <| Finset.measurable_sum _ fun i _ ↦
    measurable_const.indicator (measurableSet_toMeasurable _ _)
  have hfg : f ≤ g := fun ω ↦ (h ω).trans <| add_le_add le_rfl <| Finset.sum_le_sum fun i _ ↦
    Set.indicator_le_indicator_of_subset (subset_toMeasurable _ _) (fun _ ↦ zero_le) ω
  refine (outerLIntegral_le_lintegral hgm (Eventually.of_forall hfg)).trans_eq ?_
  simp only [g]
  rw [lintegral_add_left measurable_const,
    lintegral_finsetSum _ fun i _ ↦ measurable_const.indicator (measurableSet_toMeasurable _ _)]
  simp only [lintegral_indicator_const (measurableSet_toMeasurable _ _), measure_toMeasurable,
    lintegral_const, measure_univ, mul_one]

end OuterIntegral

section Riemann

/-- Pointwise Riemann-sum bounds behind the converse portmanteau theorem: for `0 ≤ y ≤ M`,
`k ≥ 1` and `c = M / k`, with `n(y) = #{i < k | (i + 1) c ≤ y}`,
`n(y) c ≤ y ≤ c + n(y) c`. -/
theorem riemann_sum_bounds {M y : ℝ≥0} {k : ℕ} (hk : 0 < k) (hM : 0 < M) (hy : y ≤ M) :
    y ≤ M / k + ∑ i ∈ range k, (if ((i : ℝ≥0) + 1) * (M / k) ≤ y then M / k else 0) ∧
      ∑ i ∈ range k, (if ((i : ℝ≥0) + 1) * (M / k) ≤ y then M / k else 0) ≤ y := by
  set c : ℝ≥0 := M / k with hc_def
  have hk' : (k : ℝ≥0) ≠ 0 := by exact_mod_cast hk.ne'
  have hc : 0 < c := div_pos hM (by exact_mod_cast hk)
  set j := ⌊y / c⌋₊ with hj_def
  have hiff : ∀ i : ℕ, ((i : ℝ≥0) + 1) * c ≤ y ↔ i < j := by
    intro i
    rw [← le_div_iff₀ hc, hj_def, Nat.lt_iff_add_one_le, Nat.le_floor_iff zero_le]
    push_cast
    rfl
  have hsum : ∑ i ∈ range k, (if ((i : ℝ≥0) + 1) * c ≤ y then c else 0) = (min k j : ℕ) * c := by
    simp_rw [hiff]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 2
    have : (range k).filter (· < j) = range (min k j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    rw [this, Finset.card_range]
  rw [hsum]
  have hjy : (j : ℝ≥0) * c ≤ y := by
    have := Nat.floor_le (a := y / c) zero_le
    calc (j : ℝ≥0) * c ≤ y / c * c := mul_le_mul_of_nonneg_right this zero_le
      _ = y := div_mul_cancel₀ y hc.ne'
  refine ⟨?_, ?_⟩
  · rcases le_or_gt k j with hkj | hkj
    · rw [min_eq_left hkj]
      calc y ≤ M := hy
        _ = (k : ℝ≥0) * c := by rw [hc_def, mul_div_cancel₀ _ hk']
        _ ≤ c + (k : ℝ≥0) * c := le_add_self
    · rw [min_eq_right hkj.le]
      have hlt : y / c < (j : ℝ≥0) + 1 := Nat.lt_floor_add_one _
      rw [div_lt_iff₀ hc] at hlt
      calc y ≤ ((j : ℝ≥0) + 1) * c := hlt.le
        _ = c + (j : ℝ≥0) * c := by ring
  · calc ((min k j : ℕ) : ℝ≥0) * c ≤ (j : ℝ≥0) * c :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right k j) zero_le
      _ ≤ y := hjy

/-- `limsup` along `atTop` of a sum of two `ℝ≥0∞`-valued sequences is at most the sum of the
`limsup`s (`atTop` on `ℕ` is not a `CountableInterFilter`, so `ENNReal.limsup_add_le` does not
apply). -/
theorem limsup_add_le_nat (u v : ℕ → ℝ≥0∞) :
    limsup (fun n ↦ u n + v n) atTop ≤ limsup u atTop + limsup v atTop := by
  simp only [limsup_eq_iInf_iSup_of_nat]
  rw [ENNReal.iInf_add_iInf fun i j ↦ ⟨max i j, add_le_add
    (iSup₂_mono' (f := fun n (_ : n ≥ max i j) ↦ u n) (g := fun n (_ : n ≥ i) ↦ u n)
      fun n hn ↦ ⟨n, (le_max_left i j).trans hn, le_rfl⟩)
    (iSup₂_mono' (f := fun n (_ : n ≥ max i j) ↦ v n) (g := fun n (_ : n ≥ j) ↦ v n)
      fun n hn ↦ ⟨n, (le_max_right i j).trans hn, le_rfl⟩)⟩]
  exact iInf_mono fun N ↦ iSup₂_le fun n hn ↦ add_le_add
    (le_iSup₂ (f := fun i (_ : i ≥ N) ↦ u i) n hn) (le_iSup₂ (f := fun i (_ : i ≥ N) ↦ v i) n hn)

/-- `limsup` of a finite sum of `ℝ≥0∞`-valued sequences is at most the sum of the `limsup`s. -/
theorem limsup_finset_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℕ → ℝ≥0∞) :
    limsup (fun n ↦ ∑ i ∈ s, u i n) atTop ≤ ∑ i ∈ s, limsup (u i) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (limsup_add_le_nat (u a) fun n ↦ ∑ i ∈ s, u i n).trans (add_le_add le_rfl ih)

end Riemann

section Weak

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]

/-- **Weak convergence in the outer-probability (Hoffmann-Jørgensen) sense**
(van der Vaart–Wellner, Definition 1.3.3): the arbitrary maps `X n : Ω → E` converge weakly to the
Borel probability measure `L` on `E` if `E* f(X n) → ∫ f dL` for every bounded continuous
`f : E → ℝ≥0`. No measurability of `X n` is required. -/
def TendstoInDistributionOuter (X : ℕ → Ω → E) (μ : Measure Ω) (L : ProbabilityMeasure E) :
    Prop :=
  ∀ f : E →ᵇ ℝ≥0, Tendsto (fun n ↦ outerLIntegral μ fun ω ↦ (f (X n ω) : ℝ≥0∞)) atTop
    (𝓝 (∫⁻ x, f x ∂(L : Measure E)))

variable [OpensMeasurableSpace E]

/-- **Borel weak convergence implies outer weak convergence**: if the `X n` are a.e. measurable
and `X n ⇒ G` in Mathlib's sense, then `X n ⇝ L` in the outer sense, where `L` is the law of
`G`. -/
theorem _root_.MeasureTheory.TendstoInDistribution.tendstoInDistributionOuter
    [IsProbabilityMeasure μ] {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {X : ℕ → Ω → E} {G : Ω' → E}
    (h : TendstoInDistribution X atTop G (fun _ ↦ μ) μ') {L : ProbabilityMeasure E}
    (hL : (L : Measure E) = μ'.map G) : TendstoInDistributionOuter X μ L := by
  intro f
  have key := ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 h.tendsto f
  simp only [ProbabilityMeasure.coe_mk] at key
  rw [hL]
  refine key.congr fun n ↦ ?_
  have hfm : Measurable fun x : E ↦ (f x : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp f.continuous.measurable
  rw [outerLIntegral_eq_lintegral (μ := μ) (f := fun ω ↦ (f (X n ω) : ℝ≥0∞))
    (hfm.comp_aemeasurable (h.forall_aemeasurable n)),
    lintegral_map' hfm.aemeasurable (h.forall_aemeasurable n)]

/-- **Portmanteau, outer form, (i) ⇒ (iii)** (van der Vaart–Wellner, Theorem 1.3.4): if
`X n ⇝ L` in the outer sense, then `limsup P*(X n ∈ F) ≤ L F` for every closed `F`. -/
theorem TendstoInDistributionOuter.limsup_measure_le [HasOuterApproxClosed E] {X : ℕ → Ω → E}
    {L : ProbabilityMeasure E} (h : TendstoInDistributionOuter X μ L) {F : Set E}
    (hF : IsClosed F) :
    limsup (fun n ↦ μ (X n ⁻¹' F)) atTop ≤ (L : Measure E) F := by
  have hk : ∀ k, limsup (fun n ↦ μ (X n ⁻¹' F)) atTop ≤ ∫⁻ x, hF.apprSeq k x ∂(L : Measure E) := by
    intro k
    refine (limsup_le_limsup (Eventually.of_forall fun n ↦ ?_)).trans
      (h (hF.apprSeq k)).limsup_eq.le
    refine measure_le_outerLIntegral fun ω hω ↦ ?_
    simp [HasOuterApproxClosed.apprSeq_apply_eq_one hF k hω]
  exact ge_of_tendsto (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (L : Measure E))
    (Eventually.of_forall hk)

/-- The `limsup` half of the converse portmanteau theorem: closed-set `limsup` bounds for outer
probabilities give `limsup E* f(X n) ≤ ∫ f dL` for bounded continuous `f ≥ 0`. The proof bounds
`f` above by the Riemann sum `c + ∑_{i < k} c 𝟙{f ≥ (i + 1) c}` over the closed level sets. -/
theorem limsup_outerLIntegral_le [IsProbabilityMeasure μ] {X : ℕ → Ω → E}
    {L : ProbabilityMeasure E}
    (h : ∀ F : Set E, IsClosed F → limsup (fun n ↦ μ (X n ⁻¹' F)) atTop ≤ (L : Measure E) F)
    (f : E →ᵇ ℝ≥0) :
    limsup (fun n ↦ outerLIntegral μ fun ω ↦ (f (X n ω) : ℝ≥0∞)) atTop ≤
      ∫⁻ x, f x ∂(L : Measure E) := by
  set M : ℝ≥0 := nndist f 0 + 1 with hM_def
  have hM : 0 < M := by positivity
  have hfM : ∀ x, f x ≤ M := fun x ↦
    (BoundedContinuousFunction.NNReal.upper_bound f x).trans (le_add_of_nonneg_right zero_le_one)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨k, hk⟩ := exists_nat_gt (M / ε)
  have hk0 : 0 < k := by
    have : (0 : ℝ≥0) < k := lt_of_le_of_lt zero_le hk
    exact_mod_cast this
  set c : ℝ≥0 := M / k with hc_def
  have hcε : c ≤ ε := by
    rw [hc_def, div_le_iff₀ (by exact_mod_cast hk0)]
    rw [div_lt_iff₀ hε] at hk
    rw [mul_comm]
    exact hk.le
  set Fs : ℕ → Set E := fun i ↦ {x | ((i : ℝ≥0) + 1) * c ≤ f x} with hFs_def
  have hFs_closed : ∀ i, IsClosed (Fs i) := fun i ↦ isClosed_le continuous_const f.continuous
  have hind : ∀ i x, (Fs i).indicator (fun _ ↦ (c : ℝ≥0∞)) x =
      ((if ((i : ℝ≥0) + 1) * c ≤ f x then c else 0 : ℝ≥0) : ℝ≥0∞) := by
    intro i x
    by_cases hx : ((i : ℝ≥0) + 1) * c ≤ f x
    · simp [Fs, Set.indicator, hx]
    · simp [Fs, Set.indicator, hx]
  have hpt_up : ∀ x, (f x : ℝ≥0∞) ≤ c + ∑ i ∈ range k, (Fs i).indicator (fun _ ↦ (c : ℝ≥0∞)) x := by
    intro x
    simp_rw [hind]
    exact_mod_cast (riemann_sum_bounds hk0 hM (hfM x)).1
  have hpt_low : ∀ x, ∑ i ∈ range k, (Fs i).indicator (fun _ ↦ (c : ℝ≥0∞)) x ≤ f x := by
    intro x
    simp_rw [hind]
    exact_mod_cast (riemann_sum_bounds hk0 hM (hfM x)).2
  have hstep : ∀ n, outerLIntegral μ (fun ω ↦ (f (X n ω) : ℝ≥0∞)) ≤
      c + ∑ i ∈ range k, (c : ℝ≥0∞) * μ (X n ⁻¹' Fs i) := fun n ↦
    outerLIntegral_le_const_add_sum (s := fun i ↦ X n ⁻¹' Fs i) fun ω ↦ hpt_up (X n ω)
  have hint : ∑ i ∈ range k, (c : ℝ≥0∞) * (L : Measure E) (Fs i) ≤ ∫⁻ x, f x ∂(L : Measure E) := by
    calc ∑ i ∈ range k, (c : ℝ≥0∞) * (L : Measure E) (Fs i)
        = ∫⁻ x, ∑ i ∈ range k, (Fs i).indicator (fun _ ↦ (c : ℝ≥0∞)) x ∂(L : Measure E) := by
          rw [lintegral_finsetSum _ fun i _ ↦
            measurable_const.indicator (hFs_closed i).measurableSet]
          simp only [lintegral_indicator_const (hFs_closed _).measurableSet]
      _ ≤ ∫⁻ x, f x ∂(L : Measure E) := lintegral_mono hpt_low
  calc limsup (fun n ↦ outerLIntegral μ fun ω ↦ (f (X n ω) : ℝ≥0∞)) atTop
      ≤ limsup (fun n ↦ (c : ℝ≥0∞) + ∑ i ∈ range k, (c : ℝ≥0∞) * μ (X n ⁻¹' Fs i)) atTop :=
        limsup_le_limsup (Eventually.of_forall hstep)
    _ ≤ c + ∑ i ∈ range k, (c : ℝ≥0∞) * limsup (fun n ↦ μ (X n ⁻¹' Fs i)) atTop := by
        refine (limsup_add_le_nat (fun _ ↦ (c : ℝ≥0∞)) _).trans ?_
        rw [limsup_const]
        refine add_le_add le_rfl ((limsup_finset_sum_le _ _).trans (le_of_eq ?_))
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        exact ENNReal.limsup_const_mul_of_ne_top ENNReal.coe_ne_top
    _ ≤ c + ∑ i ∈ range k, (c : ℝ≥0∞) * (L : Measure E) (Fs i) := by
        gcongr with i
        exact h _ (hFs_closed i)
    _ ≤ c + ∫⁻ x, f x ∂(L : Measure E) := add_le_add le_rfl hint
    _ ≤ ∫⁻ x, f x ∂(L : Measure E) + ε := by
        rw [add_comm]
        exact add_le_add le_rfl (by exact_mod_cast hcε)

/-- **Portmanteau, outer form, (iii) ⇒ (i)** (van der Vaart–Wellner, Theorem 1.3.4): if
`limsup P*(X n ∈ F) ≤ L F` for every closed `F`, then `X n ⇝ L` in the outer sense. The lower
bound uses `M ≤ E* f(X n) + E* (M - f)(X n)` (subadditivity of the outer integral). -/
theorem TendstoInDistributionOuter.of_forall_isClosed_limsup_le [IsProbabilityMeasure μ]
    {X : ℕ → Ω → E} {L : ProbabilityMeasure E}
    (h : ∀ F : Set E, IsClosed F → limsup (fun n ↦ μ (X n ⁻¹' F)) atTop ≤ (L : Measure E) F) :
    TendstoInDistributionOuter X μ L := by
  intro f
  set M : ℝ≥0 := nndist f 0 with hM_def
  have hfM : ∀ x, f x ≤ M := BoundedContinuousFunction.NNReal.upper_bound f
  set g : E →ᵇ ℝ≥0 := BoundedContinuousFunction.const E M - f with hg_def
  have hfg : ∀ x, (f x : ℝ≥0∞) + g x = M := by
    intro x
    simp only [g, BoundedContinuousFunction.coe_sub, Pi.sub_apply,
      BoundedContinuousFunction.const_apply]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le (hfM x)]
  have hfin : ∫⁻ x, f x ∂(L : Measure E) ≠ ∞ :=
    (lintegral_mono (fun x ↦ ENNReal.coe_le_coe.2 (hfM x))).trans_lt
      (by simp [ENNReal.coe_lt_top]) |>.ne
  have hAB : ∫⁻ x, f x ∂(L : Measure E) + ∫⁻ x, g x ∂(L : Measure E) = M := by
    have hfm : Measurable fun x : E ↦ (f x : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp f.continuous.measurable
    rw [← lintegral_add_left hfm]
    simp [hfg]
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦
    eventually_lt_of_limsup_lt ((limsup_outerLIntegral_le h f).trans_lt hb)⟩
  -- lower bound through `g = M - f`
  have hAM : ∫⁻ x, f x ∂(L : Measure E) ≤ M := hAB ▸ le_self_add
  have haM : a < M := ha.trans_le hAM
  have hBlt : ∫⁻ x, g x ∂(L : Measure E) < M - a := by
    have hB : ∫⁻ x, g x ∂(L : Measure E) = M - ∫⁻ x, f x ∂(L : Measure E) := by
      rw [← hAB, ENNReal.add_sub_cancel_left hfin]
    rw [hB]
    exact (ENNReal.cancel_of_ne (ENNReal.sub_ne_top ENNReal.coe_ne_top)).tsub_lt_tsub_left_of_le
      hAM ha
  filter_upwards [eventually_lt_of_limsup_lt ((limsup_outerLIntegral_le h g).trans_lt hBlt)]
    with n hn
  by_contra hle
  rw [not_lt] at hle
  have hsum := le_outerLIntegral_add (μ := μ) (f₁ := fun ω ↦ (f (X n ω) : ℝ≥0∞))
    (f₂ := fun ω ↦ (g (X n ω) : ℝ≥0∞)) (M := M) fun ω ↦ (hfg (X n ω)).ge
  have : (M : ℝ≥0∞) < a + (M - a) := by
    calc (M : ℝ≥0∞) ≤ _ := hsum
      _ < a + (M - a) :=
        ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top (ne_top_of_lt haM) hle) hle hn
  rw [add_tsub_cancel_of_le haM.le] at this
  exact lt_irrefl _ this

end Weak

section ExtendedCMT

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Extended continuous mapping theorem for outer weak convergence** (van der Vaart–Wellner,
Theorem 1.11.1 (i); van der Vaart, Theorem 18.11 (i)). Let `U n ⇝ L` in the outer sense and let
`g n, g₀ : α → β` satisfy `g n xₙ → g₀ x` whenever `xₙ → x ∈ α₀` with `xₙ ∈ D n` (the filter
`atTop ×ˢ 𝓝 x` restricted to `{(n, y) | y ∈ D n}`). If `P*(U n ∉ D n) → 0`, `L` is carried by
`α₀` and `g₀` is `L`-a.e. measurable, then `g n (U n) ⇝ L ∘ g₀⁻¹` in the outer sense.

No measurability of `U n` or `g n` is assumed, and `α₀` need not be measurable. -/
theorem TendstoInDistributionOuter.extended_comp {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [HasOuterApproxClosed α] [TopologicalSpace β]
    [MeasurableSpace β] [OpensMeasurableSpace β] {U : ℕ → Ω → α} {L : ProbabilityMeasure α}
    {g : ℕ → α → β} {g₀ : α → β} {D : ℕ → Set α} {α₀ : Set α}
    (hU : TendstoInDistributionOuter U μ L)
    (hg : ∀ x ∈ α₀, Tendsto (fun p : ℕ × α ↦ g p.1 p.2) ((atTop ×ˢ 𝓝 x) ⊓ 𝓟 {p | p.2 ∈ D p.1})
      (𝓝 (g₀ x)))
    (hUD : Tendsto (fun n ↦ μ {ω | U n ω ∉ D n}) atTop (𝓝 0))
    (hα₀ : ∀ᵐ x ∂(L : Measure α), x ∈ α₀) (hg₀ : AEMeasurable g₀ (L : Measure α)) :
    TendstoInDistributionOuter (fun n ω ↦ g n (U n ω)) μ (L.map g₀) := by
  refine TendstoInDistributionOuter.of_forall_isClosed_limsup_le fun K hK ↦ ?_
  rw [L.map_apply' hg₀ hK.measurableSet]
  set S : ℕ → Set α := fun k ↦ closure (⋃ m ≥ k, D m ∩ g m ⁻¹' K) with hS_def
  have hS_closed : ∀ k, IsClosed (S k) := fun k ↦ isClosed_closure
  have hS_anti : Antitone S := fun k k' hkk' ↦ closure_mono <|
    Set.iUnion₂_mono' fun m hm ↦ ⟨m, hkk'.trans hm, subset_rfl⟩
  -- Step 1: `limsup P*(g n (U n) ∈ K) ≤ L (S k)` for each `k`.
  have h1 : ∀ k, limsup (fun n ↦ μ ((fun ω ↦ g n (U n ω)) ⁻¹' K)) atTop ≤
      (L : Measure α) (S k) := by
    intro k
    have hmid : limsup (fun n ↦ μ (U n ⁻¹' S k) + μ {ω | U n ω ∉ D n}) atTop ≤
        (L : Measure α) (S k) := by
      refine (limsup_add_le_nat _ _).trans ?_
      rw [hUD.limsup_eq, add_zero]
      exact hU.limsup_measure_le (hS_closed k)
    refine le_trans (limsup_le_limsup ?_) hmid
    filter_upwards [eventually_ge_atTop k] with n hn
    refine (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
    by_cases hωD : U n ω ∈ D n
    · exact Or.inl (subset_closure (Set.mem_biUnion hn ⟨hωD, hω⟩))
    · exact Or.inr hωD
  -- Step 2: points of `α₀` in every `S k` are mapped by `g₀` into `K`.
  have h2 : ∀ x ∈ α₀, x ∈ ⋂ k, S k → g₀ x ∈ K := by
    intro x hx hxS
    by_contra hgx
    have hev := (hg x hx).eventually (hK.isOpen_compl.mem_nhds hgx)
    rw [eventually_inf_principal, eventually_prod_iff] at hev
    obtain ⟨pa, hpa, pb, hpb, hpapb⟩ := hev
    obtain ⟨N, hN⟩ := eventually_atTop.1 hpa
    obtain ⟨y, hy, hyS⟩ := mem_closure_iff_nhds.1 (Set.mem_iInter.1 hxS N) _ hpb
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage] at hyS
    obtain ⟨m, hm, hyD, hyK⟩ := hyS
    exact hpapb (hN m hm) hy hyD hyK
  -- Step 3: continuity from above for the limit law.
  have h3 : (L : Measure α) (⋂ k, S k) ≤ (L : Measure α) (g₀ ⁻¹' K) := by
    refine measure_mono_ae ?_
    filter_upwards [hα₀] with x hx hxS
    exact h2 _ hx hxS
  have h4 : (L : Measure α) (⋂ k, S k) = ⨅ k, (L : Measure α) (S k) :=
    Antitone.measure_iInter hS_anti (fun k ↦ (hS_closed k).measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  exact (le_iInf h1).trans (h4 ▸ h3)

end ExtendedCMT

section FunctionalDelta

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Functional delta theorem for outer weak convergence** (van der Vaart, Theorem 20.8;
van der Vaart–Wellner, Theorem 3.9.4). Let `r n → ∞` and `r n • (X n - θ) ⇝ L` in the outer sense
in the normed space `E`, with `L` carried by `E₀`, and let `P*(X n ∉ D) → 0`. If `φ` is Hadamard
differentiable at `θ` tangentially to `E₀` with an `L`-a.e. measurable derivative `φ'`, then
`r n • (φ (X n) - φ θ) ⇝ L ∘ φ'⁻¹` in the outer sense.

No measurability of `X n` or `φ` is assumed and `E` need not be separable. The proof applies
`TendstoInDistributionOuter.extended_comp` to `g n y = r n • (φ (θ + (r n)⁻¹ • y) - φ θ)`. -/
theorem TendstoInDistributionOuter.functional_delta {X : ℕ → Ω → E} {θ : E} {r : ℕ → ℝ}
    {φ φ' : E → F} {D E₀ : Set E} {L : ProbabilityMeasure E}
    (hXL : TendstoInDistributionOuter (fun n ω ↦ r n • (X n ω - θ)) μ L)
    (hr : Tendsto r atTop atTop) (hφ : HasHadamardDerivWithinAt φ φ' D E₀ θ)
    (hXD : Tendsto (fun n ↦ μ {ω | X n ω ∉ D}) atTop (𝓝 0))
    (hE₀ : ∀ᵐ h ∂(L : Measure E), h ∈ E₀) (hφ' : AEMeasurable φ' (L : Measure E)) :
    TendstoInDistributionOuter (fun n ω ↦ r n • (φ (X n ω) - φ θ)) μ (L.map φ') := by
  set g : ℕ → E → F := fun n y ↦ r n • (φ (θ + (r n)⁻¹ • y) - φ θ) with hg_def
  have hgX : ∀ n ω, g n (r n • (X n ω - θ)) = r n • (φ (X n ω) - φ θ) := by
    intro n ω
    by_cases hn : r n = 0
    · simp [g, hn]
    · simp [g, smul_smul, inv_mul_cancel₀ hn]
  set Dn : ℕ → Set E := fun n ↦ {y | r n ≠ 0 → θ + (r n)⁻¹ • y ∈ D} with hDn_def
  have hlim : ∀ h ∈ E₀, Tendsto (fun p : ℕ × E ↦ g p.1 p.2)
      ((atTop ×ˢ 𝓝 h) ⊓ 𝓟 {p | p.2 ∈ Dn p.1}) (𝓝 (φ' h)) := by
    intro h hh
    have hψ : Tendsto (fun p : ℕ × E ↦ ((r p.1)⁻¹, p.2))
        ((atTop ×ˢ 𝓝 h) ⊓ 𝓟 {p | p.2 ∈ Dn p.1})
        ((𝓝[>] 0 ×ˢ 𝓝 h) ⊓ 𝓟 {q : ℝ × E | θ + q.1 • q.2 ∈ D}) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
      · exact (((tendsto_inv_atTop_nhdsGT_zero.comp hr).prodMap tendsto_id)).mono_left
          inf_le_left
      · have hpos : {p : ℕ × E | 0 < r p.1} ∈ atTop ×ˢ 𝓝 h :=
          (hr.eventually_gt_atTop 0).prod_inl _
        filter_upwards [mem_inf_of_left hpos, mem_inf_of_right (mem_principal_self _)]
          with p hp hpD
        exact hpD hp.ne'
    refine ((hφ h hh).comp hψ).congr fun p ↦ ?_
    simp [g]
  have hXDn : Tendsto (fun n ↦ μ {ω | r n • (X n ω - θ) ∉ Dn n}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hXD (fun n ↦ zero_le)
      fun n ↦ measure_mono fun ω hω ↦ ?_
    simp only [Dn, Set.mem_ofPred, not_forall] at hω ⊢
    obtain ⟨hn, hω⟩ := hω
    simpa [smul_smul, inv_mul_cancel₀ hn] using hω
  have key := hXL.extended_comp hlim hXDn hE₀ hφ'
  simpa only [hgX] using key

end FunctionalDelta

section GillJohansen

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Gill–Johansen product-integral limit with outer probability** (Gill–Johansen 1990;
van der Vaart–Wellner, §3.9.4; van der Vaart, §20.3). Let `P` be a product-integral map with
Duhamel operator `Ψ` on the domain `D` (T78's `IsDuhamelProductIntegral`), `A ∈ D`, `r n → ∞`,
and `r n • (Aₙ - A) ⇝ L` in the outer sense with `L` carried by the closure of the continuity
class `S`. If `P*(Aₙ ∉ D) → 0`, then `r n • (P (Aₙ) - P A) ⇝ L ∘ (Ψ A A)⁻¹` in the outer sense:
the limit is the law of the Duhamel integral `Ψ A A Z` of `Z ∼ L`. No measurability of `Aₙ`
is assumed. -/
theorem IsDuhamelProductIntegral.tendstoInDistributionOuter {P : E → F}
    {Ψ : E → E → E →L[ℝ] F} {D S : Set E} {C : ℝ} (hP : IsDuhamelProductIntegral P Ψ D S C)
    {A : ℕ → Ω → E} {θ : E} {r : ℕ → ℝ} {L : ProbabilityMeasure E} (hθ : θ ∈ D)
    (hA : TendstoInDistributionOuter (fun n ω ↦ r n • (A n ω - θ)) μ L)
    (hr : Tendsto r atTop atTop) (hAD : Tendsto (fun n ↦ μ {ω | A n ω ∉ D}) atTop (𝓝 0))
    (hL : ∀ᵐ h ∂(L : Measure E), h ∈ closure S) :
    TendstoInDistributionOuter (fun n ω ↦ r n • (P (A n ω) - P θ)) μ (L.map (Ψ θ θ)) :=
  TendstoInDistributionOuter.functional_delta hA hr (hP.hasHadamardDerivWithinAt hθ subset_rfl)
    hAD hL (Ψ θ θ).continuous.measurable.aemeasurable

/-- `ℓ^∞([0, τ])`: bounded real functions on `[0, τ]` with the sup norm. -/
local notation "𝔻[" τ "]" => lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞

/-- **Gill–Johansen limit for the survival map** `Λ ↦ P(-Λ) = ∏_{(0, t]} (1 - dΛ)` in
`ℓ^∞([0, τ])` with outer probability: if `r n • (Λₙ - Λ) ⇝ L` (outer) with `L` carried by
`{h | -h ∈ closure S}` and `P*(-Λₙ ∉ D) → 0`, then
`r n • (P(-Λₙ) - P(-Λ)) ⇝ L ∘ (-Ψ(-Λ, -Λ))⁻¹`. -/
theorem IsStieltjesProductIntegral.tendstoInDistributionOuter_neg {τ : ℝ}
    [MeasurableSpace 𝔻[τ]] [BorelSpace 𝔻[τ]] {P : 𝔻[τ] → 𝔻[τ]}
    {Ψ : 𝔻[τ] → 𝔻[τ] → 𝔻[τ] →L[ℝ] 𝔻[τ]} {D S : Set 𝔻[τ]} {C : ℝ}
    (hP : IsStieltjesProductIntegral τ P Ψ D S C) {Λn : ℕ → Ω → 𝔻[τ]} {Λ : 𝔻[τ]}
    {r : ℕ → ℝ} {L : ProbabilityMeasure 𝔻[τ]} (hΛ : -Λ ∈ D)
    (hCLT : TendstoInDistributionOuter (fun n ω ↦ r n • (Λn n ω - Λ)) μ L)
    (hr : Tendsto r atTop atTop) (hdom : Tendsto (fun n ↦ μ {ω | -Λn n ω ∉ D}) atTop (𝓝 0))
    (hL : ∀ᵐ h ∂(L : Measure 𝔻[τ]), -h ∈ closure S) :
    TendstoInDistributionOuter (fun n ω ↦ r n • (P (-Λn n ω) - P (-Λ))) μ
      (L.map fun h ↦ -Ψ (-Λ) (-Λ) h) :=
  hCLT.functional_delta (φ := fun A ↦ P (-A)) hr (hP.hasHadamardDerivWithinAt_neg hΛ) hdom hL
    ((Ψ (-Λ) (-Λ)).continuous.neg.measurable.aemeasurable)

open KaplanMeier in
/-- **Continuous-time Kaplan–Meier limit law in `ℓ^∞([0, τ])` with outer probability**
(van der Vaart–Wellner, §3.9.4; van der Vaart, §20.3; Gill–Johansen 1990).

Setting as in T78's `tendstoInDistribution_kmSurvival_lInfty`: `Dn n ω` is the grouped censored
data set of the `n`-th sample (all observation times positive), `Λhat n ω` and `KMhat n ω` are its
Nelson–Aalen and Kaplan–Meier estimates in `ℓ^∞([0, τ])`, `P` is the product integral (T78's
hypothesis bundle `IsStieltjesProductIntegral`), and `S = P(-Λ)`.

If `√n (Λ̂ₙ - Λ) ⇝ L` in the outer sense with `L` carried by `{h | -h ∈ closure S}` (`hCLT`, `hL`;
the Nelson–Aalen functional CLT is a hypothesis) and `P*(-Λ̂ₙ ∉ D) → 0` (`hdom`), then
`√n (Ŝₙ - S) ⇝ L ∘ (-Ψ(-Λ, -Λ))⁻¹` in the outer sense, i.e. the limit is the law of
`-∫_{(0, ·]} P(-Λ)(0, s) dZ(s) P(-Λ)(s, ·]` for `Z ∼ L`.

Unlike T78's statement there are **no measurability hypotheses**: the estimators may be
non-measurable maps into the nonseparable space `ℓ^∞([0, τ])`, as they are for continuous
failure-time distributions. The domain condition is in outer probability, so a total-variation
ball `D` is admissible whenever the Nelson–Aalen total variation on `[0, τ]` stays below its
radius with outer probability tending to one. -/
theorem tendstoInDistributionOuter_kmSurvival_lInfty {τ : ℝ} [MeasurableSpace 𝔻[τ]]
    [BorelSpace 𝔻[τ]] {P : 𝔻[τ] → 𝔻[τ]} {Ψ : 𝔻[τ] → 𝔻[τ] → 𝔻[τ] →L[ℝ] 𝔻[τ]}
    {D S : Set 𝔻[τ]} {C : ℝ} (hP : IsStieltjesProductIntegral τ P Ψ D S C)
    {kn : ℕ → Ω → ℕ} {Dn : ∀ n ω, CensoredData (kn n ω)}
    (htime : ∀ n ω j, 0 < (Dn n ω).time j)
    {Λhat KMhat : ℕ → Ω → 𝔻[τ]}
    (hΛhat : ∀ n ω t, Λhat n ω t = (Dn n ω).nelsonAalen t)
    (hKMhat : ∀ n ω t, KMhat n ω t = (Dn n ω).kmSurvival t)
    {Λ : 𝔻[τ]} {L : ProbabilityMeasure 𝔻[τ]} (hΛ : -Λ ∈ D)
    (hCLT : TendstoInDistributionOuter (fun (n : ℕ) ω ↦ √(n : ℝ) • (Λhat n ω - Λ)) μ L)
    (hL : ∀ᵐ h ∂(L : Measure 𝔻[τ]), -h ∈ closure S)
    (hdom : Tendsto (fun n ↦ μ {ω | -Λhat n ω ∉ D}) atTop (𝓝 0)) :
    TendstoInDistributionOuter (fun (n : ℕ) ω ↦ √(n : ℝ) • (KMhat n ω - P (-Λ))) μ
      (L.map fun h ↦ -Ψ (-Λ) (-Λ) h) := by
  have hKM : ∀ n ω, P (-Λhat n ω) = KMhat n ω := by
    intro n ω
    have hA : ∀ t, (-Λhat n ω) t = ∑ j with (Dn n ω).time j ≤ (t : ℝ),
        -(((Dn n ω).deaths j : ℝ) / (Dn n ω).atRisk j) := by
      intro t
      rw [lp.coeFn_neg, Pi.neg_apply, hΛhat, CensoredData.nelsonAalen, ← sum_neg_distrib]
    refine lp.ext (funext fun t ↦ ?_)
    rw [hP.pureJump _ _ (Dn n ω).strictMono_time (htime n ω) _ hA t, hKMhat]
    simp only [CensoredData.kmSurvival, CensoredData.kmFactor, sub_eq_add_neg]
  have hr : Tendsto (fun n : ℕ ↦ √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have key := IsStieltjesProductIntegral.tendstoInDistributionOuter_neg hP hΛ hCLT hr hdom hL
  simpa only [hKM] using key

end GillJohansen

end MathlibExt.Probability.Statistics.GillJohansenOuter
