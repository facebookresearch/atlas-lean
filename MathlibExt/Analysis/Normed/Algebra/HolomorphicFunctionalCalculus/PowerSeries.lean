/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Scalar power series and locally uniform Riesz limits

Let `a` belong to a complete unital complex normed algebra, with no
commutativity or nonzero-algebra assumption. On a common open neighborhood
`G` of its spectrum, locally uniform convergence of analytic scalar
representatives, along any index filter, implies norm convergence of their
Riesz values.

If a scalar series `sum cₙ zⁿ` has convergence radius strictly larger than
the spectral radius of `a`, the operator series `sum cₙ • aⁿ` converges to
the Riesz value of that series germ. The order of powers and algebra
multiplication is retained. The radius may be infinite, and no truncation of
natural powers is introduced.

`PreservesCompactOpenSeqLimits` records this common-domain locally uniform
limit property for a nonunital complex algebra homomorphism on the holomorphic
germ algebra. The Riesz algebra homomorphism satisfies it after forgetting
only its unital field. All norms are those of the original Banach algebra.

## References

John B. Conway, *A Course in Functional Analysis*, second edition, Graduate Texts in
Mathematics 96, Springer (1990), Chapter VII, §4, pp. 199–204, Theorem 4.7 on the
Riesz functional calculus and its power-series and locally uniform limit properties.
The filter-generic statement extends the sequential source formulation.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped BigOperators Topology

universe uA uι

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
  [CompleteSpace A]

private theorem ofScalars_partialSum_apply
    (c : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ c).partialSum N z =
      ∑ n ∈ Finset.range N, c n • z ^ n := by
  simp [FormalMultilinearSeries.partialSum, mul_comm]

omit [CompleteSpace A] in
private theorem HolomorphicNearSpectrum.ofFunction_ofScalars_partialSum
    (a : A) (c : ℕ → ℂ) (N : ℕ)
    (hN : AnalyticOnNhd ℂ
      ((FormalMultilinearSeries.ofScalars ℂ c).partialSum N)
      (spectrum ℂ a)) :
    HolomorphicNearSpectrum.ofFunction a
        ((FormalMultilinearSeries.ofScalars ℂ c).partialSum N) hN =
      ∑ n ∈ Finset.range N,
        c n • HolomorphicNearSpectrum.coordinate a ^ n := by
  apply Subtype.ext
  change
    (((FormalMultilinearSeries.ofScalars ℂ c).partialSum N) :
        SpectrumGerm a) =
      (∑ n ∈ Finset.range N,
        c n • HolomorphicNearSpectrum.coordinate a ^ n :
          HolomorphicNearSpectrum a).1
  rw [show (FormalMultilinearSeries.ofScalars ℂ c).partialSum N =
      fun z : ℂ ↦ ∑ n ∈ Finset.range N, c n • z ^ n by
    funext z
    exact ofScalars_partialSum_apply c N z]
  let x : HolomorphicNearSpectrum a := HolomorphicNearSpectrum.coordinate a
  have hsum (s : Finset ℕ) :
      ((fun z : ℂ ↦ ∑ n ∈ s, c n • z ^ n) : SpectrumGerm a) =
        (∑ n ∈ s, c n • x ^ n : HolomorphicNearSpectrum a).1 := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert n s hn ih =>
        simp only [Finset.sum_insert hn]
        change
          ((fun z : ℂ ↦ c n • z ^ n) : SpectrumGerm a) +
              ((fun z : ℂ ↦ ∑ m ∈ s, c m • z ^ m) : SpectrumGerm a) =
            (c n • x ^ n : HolomorphicNearSpectrum a).1 +
              (∑ m ∈ s, c m • x ^ m : HolomorphicNearSpectrum a).1
        rw [ih]
        rfl
  simpa only [x] using hsum (Finset.range N)

private theorem differentiable_ofScalars_partialSum
    (c : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ
      ((FormalMultilinearSeries.ofScalars ℂ c).partialSum N) := by
  rw [show (FormalMultilinearSeries.ofScalars ℂ c).partialSum N =
      fun z : ℂ ↦ ∑ n ∈ Finset.range N, c n • z ^ n by
    funext z
    exact ofScalars_partialSum_apply c N z]
  exact Differentiable.fun_sum fun n _ ↦
    (differentiable_pow n).const_smul (c n)

private theorem tendstoLocallyUniformlyOn_ofScalars_partialSum
    (c : ℕ → ℂ)
    (h : 0 < (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    TendstoLocallyUniformlyOn
      (fun N z ↦ (FormalMultilinearSeries.ofScalars ℂ c).partialSum N z)
      (FormalMultilinearSeries.ofScalars ℂ c).sum atTop
      (Metric.eball 0
        (FormalMultilinearSeries.ofScalars ℂ c).radius) := by
  simpa using
    HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn
      ((FormalMultilinearSeries.ofScalars ℂ c).hasFPowerSeriesOnBall h)

private theorem summable_smul_pow_of_spectralRadius_lt_radius
    (a : A) (c : ℕ → ℂ)
    (h : spectralRadius ℂ a <
      (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    Summable fun n : ℕ ↦ c n • a ^ n := by
  let p := FormalMultilinearSeries.ofScalars ℂ c
  obtain ⟨r, hsr, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hmajor : Summable fun n : ℕ ↦ ‖c n‖ * (r : ℝ) ^ n := by
    simpa [p] using p.summable_norm_mul_pow hr
  have hroot : ∀ᶠ n : ℕ in atTop,
      (‖a ^ n‖₊ : ENNReal) ^ (1 / n : ℝ) < (r : ENNReal) :=
    (spectrum.pow_nnNorm_pow_one_div_tendsto_nhds_spectralRadius a).eventually
      (Iio_mem_nhds hsr)
  apply hmajor.of_norm_bounded_eventually_nat
  filter_upwards [hroot, eventually_gt_atTop 0] with n hnroot hnpos
  rw [norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hpowENN : (‖a ^ n‖₊ : ENNReal) < (r : ENNReal) ^ n := by
    have hpow := (ENNReal.rpow_inv_lt_iff hnpos').mp <| by
      simpa only [one_div] using hnroot
    simpa only [ENNReal.rpow_natCast] using hpow
  have hpowNN : ‖a ^ n‖₊ ≤ r ^ n := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_pow] using hpowENN.le
  simpa only [coe_nnNorm, NNReal.coe_pow] using NNReal.coe_mono hpowNN

/-- **Locally uniform analytic limits pass through the Riesz calculus.** Let `A` be a complete
unital complex normed algebra, `a∈A`, and `S=spectrum ℂ a`. Let `ι` be any index type with
filter `l`, and let `G⊆ℂ` be open with `S⊆G`. Suppose every scalar function `F_i : ℂ→ℂ`
and `f : ℂ→ℂ` is complex differentiable on `G`. If `F_i→f` locally uniformly on `G` along
`l`, their Riesz values satisfy `F_i(a)→f(a)` in the norm of `A` along `l`. Locally
uniform means uniform on every compact subset of `G`. Noncommutative and zero algebras are
included. -/
theorem tendsto_rieszFunctionalCalculus_of_tendstoLocallyUniformlyOn
    {ι : Type uι} {l : Filter ι}
    (a : A) {G : Set ℂ} (hG : IsOpen G)
    (hσG : spectrum ℂ a ⊆ G) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, DifferentiableOn ℂ (F i) G)
    (hf : DifferentiableOn ℂ f G)
    (hconv : TendstoLocallyUniformlyOn F f l G) :
    Tendsto
      (fun i ↦ rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofFunction a (F i)
          (((hF i).analyticOnNhd hG).mono hσG)))
      l
      (𝓝 (rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofFunction a f
          ((hf.analyticOnNhd hG).mono hσG)))) := by
  obtain ⟨D, hD⟩ := GridFilling.exists_isAdmissibleFor
    (spectrum.isCompact a) hG hσG
  have hcompactTrace : IsCompact D.reducedTrace := by
    rw [GridFilling.reducedTrace]
    exact D.boundaryEdges.isCompact_biUnion fun e _ ↦
      D.isCompact_edgeTrace e
  have hUniform : TendstoUniformlyOn F f l D.reducedTrace :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hG).mp hconv
      D.reducedTrace (fun z hz ↦ (hD.1 hz).1) hcompactTrace
  have hresCont : ContinuousOn (resolvent a) D.reducedTrace := by
    intro z hz
    have hzres : z ∈ resolventSet ℂ a :=
      spectrum.notMem_iff.mp (hD.1 hz).2
    exact
      (spectrum.hasDerivAt_resolvent_const_left hzres).continuousAt.continuousWithinAt
  obtain ⟨M, hMpos, hM⟩ :=
    (hcompactTrace.image_of_continuousOn hresCont).isBounded.exists_pos_norm_le
  have hresBound (z : ℂ) (hz : z ∈ D.reducedTrace) :
      ‖resolvent a z‖ ≤ M :=
    hM (resolvent a z) ⟨z, hz, rfl⟩
  have hFcont (i : ι) :
      ContinuousOn (rieszIntegrand a (F i)) D.reducedTrace :=
    (differentiableOn_rieszIntegrand (hF i)).continuousOn.mono hD.1
  have hfcont : ContinuousOn (rieszIntegrand a f) D.reducedTrace :=
    (differentiableOn_rieszIntegrand hf).continuousOn.mono hD.1
  have hEvalF (i : ι) :
      rieszFunctionalCalculus a
          (HolomorphicNearSpectrum.ofFunction a (F i)
            (((hF i).analyticOnNhd hG).mono hσG)) =
        rieszIntegral D.toCycle a (F i) :=
    rieszFunctionalCalculus_ofFunction_eq_rieszIntegral
      a (F i) hG hσG (hF i) D hD
  have hEval :
      rieszFunctionalCalculus a
          (HolomorphicNearSpectrum.ofFunction a f
            ((hf.analyticOnNhd hG).mono hσG)) =
        rieszIntegral D.toCycle a f :=
    rieszFunctionalCalculus_ofFunction_eq_rieszIntegral
      a f hG hσG hf D hD
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I
  let ℓ : ℝ := (D.boundaryEdges.card : ℝ) / D.scale
  let B : ℝ := ‖c⁻¹‖ * ℓ * M
  have hℓ : 0 ≤ ℓ := by
    dsimp [ℓ]
    exact div_nonneg (Nat.cast_nonneg _) D.scale_pos.le
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hBpos : 0 < B + 1 := by linarith
  let δ : ℝ := ε / (B + 1)
  have hδ : 0 < δ := div_pos hε hBpos
  have hevent :
      ∀ᶠ i in l, ∀ z ∈ D.reducedTrace, dist (f z) (F i z) < δ :=
    (Metric.tendstoUniformlyOn_iff.mp hUniform) δ hδ
  filter_upwards [hevent] with i hi
  have hscalar (z : ℂ) (hz : z ∈ D.reducedTrace) :
      ‖F i z - f z‖ ≤ δ := by
    have hdist := (hi z hz).le
    rw [dist_comm] at hdist
    simpa only [dist_eq_norm] using hdist
  have hintegrand (z : ℂ) (hz : z ∈ D.reducedTrace) :
      ‖rieszIntegrand a (F i) z - rieszIntegrand a f z‖ ≤ δ * M := by
    simp only [rieszIntegrand]
    rw [← sub_smul, norm_smul]
    exact mul_le_mul (hscalar z hz) (hresBound z hz)
      (norm_nonneg _) hδ.le
  have hnegFunction :
      (-rieszIntegrand a f) = (-1 : ℂ) • rieszIntegrand a f := by
    funext z
    simp
  have hnegIntegral :
      D.toCycle.integral (-rieszIntegrand a f) =
        -D.toCycle.integral (rieszIntegrand a f) := by
    rw [hnegFunction,
      D.toCycle_integral_smul (-1) (rieszIntegrand a f) hfcont]
    simp
  have hdiffFunction :
      (fun z ↦ rieszIntegrand a (F i) z - rieszIntegrand a f z) =
        rieszIntegrand a (F i) + (-rieszIntegrand a f) := by
    funext z
    simp only [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  have hIntegralSub :
      D.toCycle.integral
          (fun z ↦ rieszIntegrand a (F i) z - rieszIntegrand a f z) =
        D.toCycle.integral (rieszIntegrand a (F i)) -
          D.toCycle.integral (rieszIntegrand a f) := by
    calc
      D.toCycle.integral
          (fun z ↦ rieszIntegrand a (F i) z - rieszIntegrand a f z) =
          D.toCycle.integral
            (rieszIntegrand a (F i) + (-rieszIntegrand a f)) :=
        congrArg D.toCycle.integral hdiffFunction
      _ = D.toCycle.integral (rieszIntegrand a (F i)) +
          D.toCycle.integral (-rieszIntegrand a f) :=
        D.toCycle_integral_add (hFcont i) hfcont.neg
      _ = D.toCycle.integral (rieszIntegrand a (F i)) -
          D.toCycle.integral (rieszIntegrand a f) := by
        rw [hnegIntegral]
        rw [sub_eq_add_neg]
  have hIntegralBound :
      ‖D.toCycle.integral
          (fun z ↦ rieszIntegrand a (F i) z - rieszIntegrand a f z)‖ ≤
        ℓ * (δ * M) := by
    simpa [ℓ] using
      D.norm_toCycle_integral_le_of_norm_le hintegrand
  rw [hEvalF i, hEval]
  change dist
    (c⁻¹ • D.toCycle.integral (rieszIntegrand a (F i)))
    (c⁻¹ • D.toCycle.integral (rieszIntegrand a f)) < ε
  rw [dist_eq_norm, ← smul_sub, norm_smul, ← hIntegralSub]
  calc
    ‖c⁻¹‖ *
        ‖D.toCycle.integral
          (fun z ↦ rieszIntegrand a (F i) z - rieszIntegrand a f z)‖ ≤
        ‖c⁻¹‖ * (ℓ * (δ * M)) :=
      mul_le_mul_of_nonneg_left hIntegralBound (norm_nonneg _)
    _ = B * δ := by
      dsimp [B]
      ring
    _ < ε := by
      dsimp [δ]
      rw [show B * (ε / (B + 1)) = (B * ε) / (B + 1) by ring,
        div_lt_iff₀ hBpos]
      nlinarith

/-- **A scalar power series sums to its Riesz value.** Let `A` be a complete unital complex
normed algebra, `a∈A`, and `S=spectrum ℂ a`. For coefficients `c : ℕ→ℂ`, let `R` be the
convergence radius of `∑ c_n z^n`. If `spectralRadius ℂ a<R`, let `f` be its analytic germ
near `S`. Then `∑ c_n • a^n` has sum `rieszFunctionalCalculus a f`. The radius may be
infinite. Natural powers and products are those of the original algebra; commutativity is
not assumed. -/
theorem hasSum_rieszFunctionalCalculus_ofScalars
    (a : A) (c : ℕ → ℂ)
    (h : spectralRadius ℂ a <
      (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    HasSum (fun n : ℕ ↦ c n • a ^ n)
      (rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofScalars a c h)) := by
  let p := FormalMultilinearSeries.ofScalars ℂ c
  let G : Set ℂ := Metric.eball 0 p.radius
  have hpRadius : 0 < p.radius :=
    (bot_le : 0 ≤ spectralRadius ℂ a).trans_lt h
  have hG : IsOpen G := Metric.isOpen_eball
  have hσG : spectrum ℂ a ⊆ G := by
    intro z hz
    change z ∈ Metric.eball 0 p.radius
    rw [mem_eball_zero_iff]
    have hzle : (‖z‖₊ : ENNReal) ≤ spectralRadius ℂ a := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup₂_of_le z hz (le_refl (‖z‖₊ : ENNReal))
    exact hzle.trans_lt h
  have hpartialDiff (N : ℕ) :
      DifferentiableOn ℂ (p.partialSum N) G := by
    have hpartialDiff' : Differentiable ℂ (p.partialSum N) := by
      simpa only [p] using differentiable_ofScalars_partialSum c N
    exact hpartialDiff'.differentiableOn
  have hsumDiff : DifferentiableOn ℂ p.sum G :=
    p.analyticOnNhd.differentiableOn
  have hconv : TendstoLocallyUniformlyOn
      (fun N z ↦ p.partialSum N z) p.sum atTop G := by
    simpa only [p, G] using
      tendstoLocallyUniformlyOn_ofScalars_partialSum c hpRadius
  have htendsto :=
    tendsto_rieszFunctionalCalculus_of_tendstoLocallyUniformlyOn
      a hG hσG hpartialDiff hsumDiff hconv
  have hpartial (N : ℕ) :
      rieszFunctionalCalculus a
          (HolomorphicNearSpectrum.ofFunction a (p.partialSum N)
            (((hpartialDiff N).analyticOnNhd hG).mono hσG)) =
        ∑ n ∈ Finset.range N, c n • a ^ n := by
    rw [HolomorphicNearSpectrum.ofFunction_ofScalars_partialSum]
    change (rieszFunctionalCalculusAlgHom a)
        (∑ n ∈ Finset.range N,
          c n • HolomorphicNearSpectrum.coordinate a ^ n) = _
    simp only [map_sum, map_smul, map_pow,
      rieszFunctionalCalculusAlgHom_apply,
      rieszFunctionalCalculus_coordinate]
  have hlimit :
      HolomorphicNearSpectrum.ofFunction a p.sum
          ((hsumDiff.analyticOnNhd hG).mono hσG) =
        HolomorphicNearSpectrum.ofScalars a c h := by
    apply Subtype.ext
    rfl
  have hpartialFun :
      (fun N ↦ rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofFunction a (p.partialSum N)
          (((hpartialDiff N).analyticOnNhd hG).mono hσG))) =
        fun N ↦ ∑ n ∈ Finset.range N, c n • a ^ n :=
    funext hpartial
  rw [hpartialFun, hlimit] at htendsto
  exact (Summable.hasSum_iff_tendsto_nat
    (summable_smul_pow_of_spectralRadius_lt_radius a c h)).2 htendsto

/-- **Sequential compact-open continuity of a spectrum-germ algebra map.** Let `A` be a
complete unital complex normed algebra, `a∈A`, and `S=spectrum ℂ a`. Let `Hol(a)` be the
complex algebra of scalar-function germs analytic near `S`, and let `τ : Hol(a)→ₙₐ[ℂ]A` be
a nonunital complex algebra homomorphism. `PreservesCompactOpenSeqLimits a τ` means: for
every open `G⊇S`, scalar functions `F_n,f` complex differentiable on `G`, and locally
uniform convergence `F_n→f` on `G`, one has `τ([F_n])→τ([f])` in the algebra norm.
Brackets denote germs at `S`; representative values outside `G` do not affect them. -/
def PreservesCompactOpenSeqLimits
    (a : A) (τ : HolomorphicNearSpectrum a →ₙₐ[ℂ] A) : Prop :=
  ∀ {G : Set ℂ} (hG : IsOpen G) (hσG : spectrum ℂ a ⊆ G)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) G)
    (hf : DifferentiableOn ℂ f G),
    TendstoLocallyUniformlyOn F f atTop G →
      Tendsto
        (fun n ↦ τ (HolomorphicNearSpectrum.ofFunction a (F n)
          (((hF n).analyticOnNhd hG).mono hσG)))
        atTop
        (𝓝 (τ (HolomorphicNearSpectrum.ofFunction a f
          ((hf.analyticOnNhd hG).mono hσG))))

/-- **The Riesz homomorphism preserves sequential analytic limits.** Let `A` be a complete
unital complex normed algebra, `a∈A`, and `S=spectrum ℂ a`. For each common open `G⊇S` and
scalar functions `F_n,f` complex differentiable on `G`, locally uniform convergence
`F_n→f` gives convergence of their Riesz values in norm. Thus the canonical Riesz
homomorphism, viewed as a nonunital complex algebra homomorphism on `Hol(a)`, satisfies
`PreservesCompactOpenSeqLimits a τ`. Zero and noncommutative algebras are included. -/
theorem rieszFunctionalCalculusAlgHom_preservesCompactOpenSeqLimits
    (a : A) :
    PreservesCompactOpenSeqLimits a
      (rieszFunctionalCalculusAlgHom a).toNonUnitalAlgHom := by
  intro G hG hσG F f hF hf hconv
  change Tendsto
    (fun n ↦ rieszFunctionalCalculus a
      (HolomorphicNearSpectrum.ofFunction a (F n)
        (((hF n).analyticOnNhd hG).mono hσG)))
    atTop
    (𝓝 (rieszFunctionalCalculus a
      (HolomorphicNearSpectrum.ofFunction a f
        ((hf.analyticOnNhd hG).mono hσG))))
  exact tendsto_rieszFunctionalCalculus_of_tendstoLocallyUniformlyOn
    a hG hσG hF hf hconv

#print axioms tendsto_rieszFunctionalCalculus_of_tendstoLocallyUniformlyOn
#print axioms hasSum_rieszFunctionalCalculus_ofScalars
#print axioms PreservesCompactOpenSeqLimits
#print axioms rieszFunctionalCalculusAlgHom_preservesCompactOpenSeqLimits
