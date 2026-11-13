/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.SIR
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import MathlibExt.Analysis.ODE.MaximalSolution
import MathlibExt.Biology.Epidemiology.StochasticSIRKurtz
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Diffusion approximation (central limit theorem) for the stochastic SIR epidemic

In a closed population of size `N`, the stochastic SIR epidemic jumps
`(S, I) → (S - 1, I + 1)` at rate `β S I / N` and `(S, I) → (S, I - 1)` at rate `γ I`. Both rates
have the density-dependent form `N λ(S / N, I / N)`, with jump vectors `ℓ₁ = (-1, 1)`,
`ℓ₂ = (0, -1)` and intensities `λ₁(s, i) = β s i`, `λ₂(s, i) = γ i`. Write `X_N = (S, I) / N` for
the scaled chain and `x = (s, i)` for the solution of the Kermack–McKendrick system
`s' = -β s i`, `i' = β s i - γ i` (`SIR.IsSolution β γ 1`). Kurtz's law of large numbers says
`X_N → x` uniformly on compacts in probability. The diffusion approximation (Kurtz 1971;
Ethier–Kurtz 1986, ch. 11, Thm 2.3) describes the Gaussian fluctuations around it: the scaled
fluctuation `U_N = √N (X_N - x)` converges to the solution `U` of the linear SDE

  `U(t) = U(0) + M(t) + ∫₀ᵗ DF(x(s)) U(s) ds`,

where `F(s, i) = (-β s i, β s i - γ i)` is the drift (`drift`), `DF` its Jacobian (`jacobian`),
and `M` is a continuous centered Gaussian martingale with independent increments and covariance
`E[M(t) M(t)ᵀ] = ∫₀ᵗ G(x(s)) ds`, `G = Σ_ℓ λ_ℓ ℓ ℓᵀ` (`diffusionMatrix`). If `U(0)` is centered
Gaussian with covariance `V₀` and independent of `M`, then `U(t)` is centered Gaussian with
covariance `V(t)` solving the Lyapunov equation `V' = DF(x) V + V DF(x)ᵀ + G(x)`, `V(0) = V₀`
(`lyapunovField`, `IsLimitCovariance`).

## Kurtz's argument, and what is assumed

For the chain, `X_N(t) = X_N(0) + ∫₀ᵗ F(X_N) + N^{-1/2} M_N(t)`, where
`M_N = √N (X_N(t) - X_N(0) - ∫₀ᵗ F(X_N))` (`scaledMartingale`) is the scaled compensated Poisson
martingale `Σ_ℓ ℓ N^{-1/2} Ỹ_ℓ(N ∫₀ᵗ λ_ℓ(X_N))`. Subtracting the integral equation for `x`,

  `U_N(t) = U_N(0) + M_N(t) + ∫₀ᵗ √N (F(X_N) - F(x)) ds`.

For SIR the drift is quadratic, so the linearization is exact up to one product term:
`F(x + h) = F(x) + DF(x) h + β h₁ h₂ (-1, 1)` (`drift_add`), whence
`√N (F(X_N) - F(x)) = DF(x) U_N + β (U_N)₁ (X_N - x)₂ (-1, 1)`. The remainder is at most
`β |X_N - x| |U_N|`, which the law of large numbers makes small. Gronwall's inequality then
controls `U_N - U` pathwise by the initial error, the martingale error `sup |M_N - M|`, and
`sup |X_N - x|` (`norm_sqrt_smul_sub_sub_le`). This file proves that deterministic estimate and
the probabilistic conclusion, taking as **explicit hypotheses**

* the law of large numbers: for every `δ > 0`, `P(∃ t ∈ [0, T], |X_N(t) - x(t)| ≥ δ) → 0`
  (`StochasticSIR.tendsto_measure_deviation` proves it for the SIR chain;
  `tendsto_measure_norm_sub_of_deviation` translates its `ℓ¹` form), and
* the martingale functional CLT in coupled (Skorokhod-representation) form: for every `δ > 0`,
  `P(∃ t ∈ [0, T], |M_N(t) - M(t)| ≥ δ) → 0`, for a process `M` with continuous paths.

The proof of the convergence theorem uses no property of `M` beyond continuity of its paths and
measurability of its marginals, so the theorem holds for whatever limit the martingale CLT
supplies; the Gaussian description of `M` above is what Ethier–Kurtz ch. 7, Thm 1.4 gives for
the SIR chain, and it is not used here.

## Main results

* `drift_add`: the exact second-order expansion of the SIR drift.
* `norm_sqrt_smul_sub_sub_le`: Kurtz's pathwise estimate for `|U_N(t) - U(t)|`.
* `tendsto_measure_fluctuation_sub`: **the diffusion approximation.** Under the two hypotheses
  above and convergence of the initial fluctuation, for every `ε > 0`,
  `P(∃ t ∈ [0, T], |√N (X_N(t) - x(t)) - U(t)| ≥ ε) → 0`: uniform convergence in probability
  on `[0, T]`.
* `tendsto_measure_iSup_fluctuation_sub`: the same for the supremum event
  `sup_{t ∈ [0, T]} |√N (X_N(t) - x(t)) - U(t)| ≥ ε`, whose supremum need not be attained.
* `tendstoInDistribution_fluctuation`: consequently `√N (X_N(t) - x(t)) → U(t)` in
  distribution for each `t ∈ [0, T]`.
* `tendsto_measure_norm_gt`: tightness of the limit data `(U₀, sup_{[0, T]} ‖M‖)`, used to
  control the remainder term.
* `tendsto_measure_norm_sub_of_deviation`: the `ℓ¹` law of large numbers
  `StochasticSIR.tendsto_measure_deviation` implies the law-of-large-numbers hypothesis used
  here.
* `exists_isFluctuationPath`, `IsFluctuationPath.unique`, `IsFluctuationPath.initial`: the linear
  fluctuation equation has exactly one continuous solution on `[0, T]` for each initial value
  `u₀` and each continuous driving path, and it starts at `u₀`.
* `IsLimitCovariance.eqOn`: the Lyapunov equation for the limit covariance has at most one
  solution from a given initial covariance.

## Scope

* The martingale functional CLT for `M_N` (Poisson Donsker theorem plus the random time change)
  is a hypothesis, as is the law of large numbers.
* That `U(t)` is Gaussian with covariance `V(t)` (`IsLimitCovariance`) when `M` is the Gaussian
  martingale above is not proved: it needs the Wiener integral `∫ Φ(t, s) dM(s)` for the
  two-dimensional, time-inhomogeneous equation. The Lyapunov equation is stated and its
  solutions are shown to be unique, so `V(t)` is determined by the definitions.
* Probabilities of events over `[0, T]` (some time at which a deviation reaches a threshold, or
  a supremum at least a threshold) are outer measures; those events are not assumed measurable.

## References

* T. G. Kurtz, *Limit theorems for sequences of jump Markov processes approximating ordinary
  differential processes*, J. Appl. Probab. 8 (1971) 344–356.
* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), ch. 11, §2 (Theorem 2.3) and ch. 7, §1.
* H. Andersson and T. Britton, *Stochastic Epidemic Models and Their Statistical Analysis*,
  Lecture Notes in Statistics 151, Springer (2000), ch. 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal

namespace MathlibExt.Biology.Epidemiology.StochasticSIRDiffusion

/-! ### Drift, Jacobian, diffusion matrix -/

/-- The density drift of the SIR chain, `F(s, i) = (-β s i, β s i - γ i)`: the sum over the
two transitions of jump vector times intensity, `(-1, 1) β s i + (0, -1) γ i`. -/
def drift (β γ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (-(β * p.1 * p.2), β * p.1 * p.2 - γ * p.2)

/-- The Jacobian of the drift at `p = (s, i)` applied to `h`:
`DF(p) h = (-β (i h₁ + s h₂), β (i h₁ + s h₂) - γ h₂)`, i.e. the matrix
`[[-β i, -β s], [β i, β s - γ]]`. -/
def jacobian (β γ : ℝ) (p h : ℝ × ℝ) : ℝ × ℝ :=
  (-(β * (p.2 * h.1 + p.1 * h.2)), β * (p.2 * h.1 + p.1 * h.2) - γ * h.2)

/-- The infinitesimal covariance `G(p) = Σ_ℓ λ_ℓ(p) ℓ ℓᵀ` of the SIR chain at `p = (s, i)`,
stored as its entries `(G₁₁, G₁₂, G₂₂) = (β s i, -β s i, β s i + γ i)`. -/
def diffusionMatrix (β γ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (β * p.1 * p.2, -(β * p.1 * p.2), β * p.1 * p.2 + γ * p.2)

/-- The Lyapunov vector field `V ↦ DF(p) V + V DF(p)ᵀ + G(p)` on symmetric `2 × 2` matrices,
with `V` stored as `(V₁₁, V₁₂, V₂₂)`. The columns of `DF(p) V` are `DF(p)` applied to the columns
`(V₁₁, V₁₂)` and `(V₁₂, V₂₂)` of `V`. -/
def lyapunovField (β γ : ℝ) (p : ℝ × ℝ) (c : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (2 * (jacobian β γ p (c.1, c.2.1)).1 + (diffusionMatrix β γ p).1,
    (jacobian β γ p (c.2.1, c.2.2)).1 + (jacobian β γ p (c.1, c.2.1)).2 +
      (diffusionMatrix β γ p).2.1,
    2 * (jacobian β γ p (c.2.1, c.2.2)).2 + (diffusionMatrix β γ p).2.2)

/-- The Lyapunov field written out: with `p = (s, i)` and `V = (a, b, c)`,
`a' = -2 β (i a + s b) + β s i`, `b' = β i (a - b) + (β s - γ) b - β s c - β s i`,
`c' = 2 β i b + 2 (β s - γ) c + β s i + γ i`. -/
theorem lyapunovField_apply (β γ : ℝ) (p : ℝ × ℝ) (c : ℝ × ℝ × ℝ) :
    lyapunovField β γ p c =
      (-2 * β * (p.2 * c.1 + p.1 * c.2.1) + β * p.1 * p.2,
        β * p.2 * (c.1 - c.2.1) + (β * p.1 - γ) * c.2.1 - β * p.1 * c.2.2 - β * p.1 * p.2,
        2 * β * p.2 * c.2.1 + 2 * (β * p.1 - γ) * c.2.2 + β * p.1 * p.2 + γ * p.2) := by
  simp only [lyapunovField, jacobian, diffusionMatrix, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- **Exact linearization of the SIR drift.** The drift is quadratic, so
`F(p + h) = F(p) + DF(p) h + β h₁ h₂ (-1, 1)`. -/
theorem drift_add (β γ : ℝ) (p h : ℝ × ℝ) :
    drift β γ (p + h) = drift β γ p + jacobian β γ p h + (β * h.1 * h.2) • ((-1 : ℝ), (1 : ℝ)) := by
  simp only [drift, jacobian, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul,
    Prod.mk_add_mk, Prod.mk.injEq]
  refine ⟨by ring, by ring⟩

theorem jacobian_sub (β γ : ℝ) (p h k : ℝ × ℝ) :
    jacobian β γ p (h - k) = jacobian β γ p h - jacobian β γ p k := by
  simp only [jacobian, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk, Prod.mk.injEq]
  refine ⟨by ring, by ring⟩

theorem jacobian_smul (β γ : ℝ) (p h : ℝ × ℝ) (c : ℝ) :
    jacobian β γ p (c • h) = c • jacobian β γ p h := by
  simp only [jacobian, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk, Prod.mk.injEq]
  refine ⟨by ring, by ring⟩

@[simp]
theorem jacobian_zero (β γ : ℝ) (p : ℝ × ℝ) : jacobian β γ p 0 = 0 := by
  simp [jacobian]

theorem continuous_drift (β γ : ℝ) : Continuous (drift β γ) := by
  unfold drift
  fun_prop

theorem continuous_jacobian (β γ : ℝ) :
    Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) => jacobian β γ q.1 q.2) := by
  unfold jacobian
  fun_prop

private theorem abs_fst_le (p : ℝ × ℝ) : |p.1| ≤ ‖p‖ := by
  rw [← Real.norm_eq_abs]; exact norm_fst_le p

private theorem abs_snd_le (p : ℝ × ℝ) : |p.2| ≤ ‖p‖ := by
  rw [← Real.norm_eq_abs]; exact norm_snd_le p

/-- Operator-norm bound for the Jacobian in the sup norm of `ℝ × ℝ`:
`‖DF(p) h‖ ≤ (2 β ‖p‖ + γ) ‖h‖`. -/
theorem norm_jacobian_le {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (p h : ℝ × ℝ) :
    ‖jacobian β γ p h‖ ≤ (2 * β * ‖p‖ + γ) * ‖h‖ := by
  have hp1 := abs_fst_le p
  have hp2 := abs_snd_le p
  have hh1 := abs_fst_le h
  have hh2 := abs_snd_le h
  have ha : |p.2 * h.1 + p.1 * h.2| ≤ 2 * ‖p‖ * ‖h‖ := by
    calc |p.2 * h.1 + p.1 * h.2| ≤ |p.2 * h.1| + |p.1 * h.2| := abs_add_le _ _
      _ = |p.2| * |h.1| + |p.1| * |h.2| := by rw [abs_mul, abs_mul]
      _ ≤ ‖p‖ * ‖h‖ + ‖p‖ * ‖h‖ := by gcongr
      _ = 2 * ‖p‖ * ‖h‖ := by ring
  have hβa : β * |p.2 * h.1 + p.1 * h.2| ≤ 2 * β * ‖p‖ * ‖h‖ := by
    calc β * |p.2 * h.1 + p.1 * h.2| ≤ β * (2 * ‖p‖ * ‖h‖) :=
          mul_le_mul_of_nonneg_left ha hβ
      _ = 2 * β * ‖p‖ * ‖h‖ := by ring
  have hγh : γ * |h.2| ≤ γ * ‖h‖ := mul_le_mul_of_nonneg_left hh2 hγ
  have hγ0 : 0 ≤ γ * ‖h‖ := mul_nonneg hγ (norm_nonneg h)
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · simp only [jacobian, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hβ]
    nlinarith
  · simp only [jacobian, Real.norm_eq_abs]
    calc |β * (p.2 * h.1 + p.1 * h.2) - γ * h.2|
        ≤ |β * (p.2 * h.1 + p.1 * h.2)| + |γ * h.2| := abs_sub _ _
      _ = β * |p.2 * h.1 + p.1 * h.2| + γ * |h.2| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hβ, abs_of_nonneg hγ]
      _ ≤ (2 * β * ‖p‖ + γ) * ‖h‖ := by nlinarith

/-- The Jacobian bound with `‖p‖ ≤ B`. -/
theorem norm_jacobian_le_of_le {β γ B : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {p : ℝ × ℝ}
    (hp : ‖p‖ ≤ B) (h : ℝ × ℝ) :
    ‖jacobian β γ p h‖ ≤ (2 * β * B + γ) * ‖h‖ := by
  refine (norm_jacobian_le hβ hγ p h).trans ?_
  gcongr

/-! ### Integrability helpers -/

private theorem intervalIntegrable_of_integrableOn {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {T t : ℝ} (hf : IntegrableOn f (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable f volume 0 t :=
  (hf.mono_set (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)).intervalIntegrable

private theorem continuousOn_uIcc_of_Icc {E : Type*} [TopologicalSpace E] {f : ℝ → E} {T t : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (ht : t ∈ Icc 0 T) : ContinuousOn f (uIcc 0 t) :=
  hf.mono (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2)

/-! ### The linear fluctuation equation -/

/-- `U` solves the **linear fluctuation equation** on `[0, T]` driven by the path `m`, with
initial value `u₀`, around the deterministic path `x`:
`U(t) = u₀ + (m(t) - m(0)) + ∫₀ᵗ DF(x(s)) U(s) ds`, and `U` is continuous on `[0, T]`. The
driving path enters only through its increments, so `U(0) = u₀` for every `m`
(`IsFluctuationPath.initial`). With `m` the Gaussian martingale of the module docstring, which
starts at `0`, this is the Ornstein–Uhlenbeck-type SDE `dU = DF(x(t)) U dt + dM(t)` of the
diffusion approximation, solved pathwise. -/
structure IsFluctuationPath (β γ T : ℝ) (x : ℝ → ℝ × ℝ) (u₀ : ℝ × ℝ) (m U : ℝ → ℝ × ℝ) :
    Prop where
  /-- The solution is continuous on `[0, T]`. -/
  continuousOn : ContinuousOn U (Icc 0 T)
  /-- The integral equation. -/
  eq : ∀ t ∈ Icc 0 T, U t = u₀ + (m t - m 0) + ∫ s in (0 : ℝ)..t, jacobian β γ (x s) (U s)

namespace IsFluctuationPath

variable {β γ T : ℝ} {x : ℝ → ℝ × ℝ} {u₀ : ℝ × ℝ} {m U : ℝ → ℝ × ℝ}

private theorem continuousOn_jacobian (hxc : ContinuousOn x (Icc 0 T))
    (hU : ContinuousOn U (Icc 0 T)) :
    ContinuousOn (fun s => jacobian β γ (x s) (U s)) (Icc 0 T) :=
  (continuous_jacobian β γ).comp_continuousOn (hxc.prodMk hU)

/-- The solution starts at its initial value: `U(0) = u₀` for every driving path `m`. -/
theorem initial (hT : 0 ≤ T) (hU : IsFluctuationPath β γ T x u₀ m U) : U 0 = u₀ := by
  simpa using hU.eq 0 ⟨le_rfl, hT⟩

/-- A priori bound: if `‖u₀‖ ≤ k`, `‖m‖ ≤ k` and `‖x‖ ≤ B` on `[0, T]`, then
`‖U(t)‖ ≤ 3 k e^{(2 β B + γ) t}` (the increment `m(t) - m(0)` contributes `2 k`). -/
theorem norm_le (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {B k : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ B) (hxc : ContinuousOn x (Icc 0 T))
    (hU : IsFluctuationPath β γ T x u₀ m U) (hu₀ : ‖u₀‖ ≤ k) (hm : ∀ t ∈ Icc 0 T, ‖m t‖ ≤ k) :
    ∀ t ∈ Icc 0 T, ‖U t‖ ≤ 3 * k * exp ((2 * β * B + γ) * t) := by
  have hL : 0 ≤ 2 * β * B + γ := by positivity
  have hcont := continuousOn_jacobian (β := β) (γ := γ) hxc hU.continuousOn
  refine StochasticSIR.le_mul_exp_of_le_add_integral hL
    (hU.continuousOn.norm.integrableOn_Icc (μ := volume)) (fun _ _ => norm_nonneg _)
    fun t ht => ?_
  have hii : IntervalIntegrable (fun s => jacobian β γ (x s) (U s)) volume 0 t :=
    (continuousOn_uIcc_of_Icc hcont ht).intervalIntegrable
  have hUi : IntervalIntegrable (fun s => ‖U s‖) volume 0 t :=
    (continuousOn_uIcc_of_Icc hU.continuousOn.norm ht).intervalIntegrable
  rw [hU.eq t ht]
  calc ‖u₀ + (m t - m 0) + ∫ s in (0 : ℝ)..t, jacobian β γ (x s) (U s)‖
      ≤ ‖u₀‖ + ‖m t - m 0‖ + ‖∫ s in (0 : ℝ)..t, jacobian β γ (x s) (U s)‖ := norm_add₃_le
    _ ≤ k + (k + k) + ∫ s in (0 : ℝ)..t, ‖jacobian β γ (x s) (U s)‖ := by
        gcongr
        · exact norm_sub_le_of_le (hm t ht) (hm 0 ⟨le_rfl, ht.1.trans ht.2⟩)
        · exact intervalIntegral.norm_integral_le_integral_norm ht.1
    _ ≤ k + (k + k) + ∫ s in (0 : ℝ)..t, (2 * β * B + γ) * ‖U s‖ := by
        gcongr
        refine intervalIntegral.integral_mono_on ht.1 hii.norm (hUi.const_mul _) fun s hs => ?_
        exact norm_jacobian_le_of_le hβ hγ (hB s ⟨hs.1, hs.2.trans ht.2⟩) _
    _ = 3 * k + (2 * β * B + γ) * ∫ s in (0 : ℝ)..t, ‖U s‖ := by
        rw [intervalIntegral.integral_const_mul]; ring

/-- **Uniqueness** of the solution of the fluctuation equation on `[0, T]`. -/
theorem unique (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hxc : ContinuousOn x (Icc 0 T)) {U' : ℝ → ℝ × ℝ}
    (hU : IsFluctuationPath β γ T x u₀ m U) (hU' : IsFluctuationPath β γ T x u₀ m U') :
    ∀ t ∈ Icc 0 T, U t = U' t := by
  rcases (Icc 0 T).eq_empty_or_nonempty with hE | ⟨t₀, ht₀⟩
  · simp [hE]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hxc
  set B := max C 0
  have hB : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ B := fun t ht => (hC t ht).trans (le_max_left _ _)
  have hL : 0 ≤ 2 * β * B + γ := by positivity
  have hD : ContinuousOn (fun s => U s - U' s) (Icc 0 T) := hU.continuousOn.sub hU'.continuousOn
  have hc := continuousOn_jacobian (β := β) (γ := γ) hxc hU.continuousOn
  have hc' := continuousOn_jacobian (β := β) (γ := γ) hxc hU'.continuousOn
  have key := StochasticSIR.le_mul_exp_of_le_add_integral (a := 0) hL
    (hD.norm.integrableOn_Icc (μ := volume)) (fun _ _ => norm_nonneg _) fun t ht => ?_
  · intro t ht
    have := key t ht
    rw [zero_mul] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hi := (continuousOn_uIcc_of_Icc hc ht).intervalIntegrable (μ := volume)
  have hi' := (continuousOn_uIcc_of_Icc hc' ht).intervalIntegrable (μ := volume)
  have hDi : IntervalIntegrable (fun s => ‖U s - U' s‖) volume 0 t :=
    (continuousOn_uIcc_of_Icc hD.norm ht).intervalIntegrable
  rw [hU.eq t ht, hU'.eq t ht, zero_add, add_sub_add_left_eq_sub,
    ← intervalIntegral.integral_sub hi hi']
  calc ‖∫ s in (0 : ℝ)..t, (jacobian β γ (x s) (U s) - jacobian β γ (x s) (U' s))‖
      ≤ ∫ s in (0 : ℝ)..t, ‖jacobian β γ (x s) (U s) - jacobian β γ (x s) (U' s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
    _ ≤ ∫ s in (0 : ℝ)..t, (2 * β * B + γ) * ‖U s - U' s‖ := by
        refine intervalIntegral.integral_mono_on ht.1 (hi.sub hi').norm (hDi.const_mul _)
          fun s hs => ?_
        rw [← jacobian_sub]
        exact norm_jacobian_le_of_le hβ hγ (hB s ⟨hs.1, hs.2.trans ht.2⟩) _
    _ = (2 * β * B + γ) * ∫ s in (0 : ℝ)..t, ‖U s - U' s‖ :=
        intervalIntegral.integral_const_mul _ _

end IsFluctuationPath

/-- **Existence** of the solution of the fluctuation equation on `[0, T]` for a driving path `m`
continuous on `[0, T]`. The proof extends `x` and `m` continuously to `ℝ`, solves the globally
Lipschitz ODE `V' = DF(x) (V + (m - m(0)))`, `V(0) = u₀`, and sets `U = V + (m - m(0))`. -/
theorem exists_isFluctuationPath {β γ T : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {x : ℝ → ℝ × ℝ}
    (hxc : ContinuousOn x (Icc 0 T)) (u₀ : ℝ × ℝ) {m : ℝ → ℝ × ℝ}
    (hm : ContinuousOn m (Icc 0 T)) :
    ∃ U, IsFluctuationPath β γ T x u₀ m U := by
  rcases lt_or_ge T 0 with hT | hT
  · refine ⟨0, ?_, ?_⟩
    · simp [Icc_eq_empty_of_lt hT]
    · intro t ht
      exact absurd (ht.1.trans ht.2) (not_le.2 hT)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hxc
  set B := max C 0
  set proj : ℝ → ℝ := fun t => (projIcc 0 T hT t : ℝ)
  have hπc : Continuous proj := continuous_subtype_val.comp continuous_projIcc
  have hπmem : ∀ t, proj t ∈ Icc 0 T := fun t => (projIcc 0 T hT t).2
  have hπeq : ∀ t ∈ Icc 0 T, proj t = t := fun t ht => by
    simp only [proj, projIcc_of_mem hT ht]
  set xe : ℝ → ℝ × ℝ := fun t => x (proj t)
  set me : ℝ → ℝ × ℝ := fun t => m (proj t)
  have hxe : Continuous xe := hxc.comp_continuous hπc hπmem
  have hme : Continuous me := hm.comp_continuous hπc hπmem
  have hxeB : ∀ t, ‖xe t‖ ≤ B := fun t => (hC _ (hπmem t)).trans (le_max_left _ _)
  set f : ℝ → ℝ × ℝ → ℝ × ℝ := fun t v => jacobian β γ (xe t) (v + (me t - m 0))
  have hfc : Continuous (Function.uncurry f) := by
    change Continuous (fun q : ℝ × (ℝ × ℝ) => jacobian β γ (xe q.1) (q.2 + (me q.1 - m 0)))
    exact (continuous_jacobian β γ).comp ((hxe.comp continuous_fst).prodMk
      (continuous_snd.add ((hme.comp continuous_fst).sub continuous_const)))
  have hL : 0 ≤ 2 * β * B + γ := by positivity
  have hlip : ∀ t, LipschitzWith (Real.toNNReal (2 * β * B + γ)) (f t) := by
    intro t
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [Real.coe_toNNReal _ hL, dist_eq_norm, dist_eq_norm]
    simp only [f]
    rw [← jacobian_sub, add_sub_add_right_eq_sub]
    exact norm_jacobian_le_of_le hβ hγ (hxeB t) _
  obtain ⟨V, ⟨hV0, hV⟩, -⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
      f 0 u₀ _ hfc hlip
  have hVc : Continuous V := continuous_iff_continuousAt.2 fun t => (hV t).continuousAt
  refine ⟨fun t => V t + (m t - m 0), hVc.continuousOn.add (hm.sub continuousOn_const),
    fun t ht => ?_⟩
  have hfV : Continuous (fun s => f s (V s)) :=
    hfc.comp (continuous_id.prodMk hVc)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun s _ => hV s) (hfV.intervalIntegrable 0 t)
  have hcongr : ∫ s in (0 : ℝ)..t, f s (V s) =
      ∫ s in (0 : ℝ)..t, jacobian β γ (x s) (V s + (m s - m 0)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    have hsI : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    simp only [f, xe, me, hπeq s hsI]
  rw [hcongr, hV0] at hFTC
  rw [hFTC]
  abel

/-! ### The ODE limit in integral form -/

/-- A solution of the SIR system (with `N = 1`, i.e. in densities) satisfies the integral
equation `x(t) = x(0) + ∫₀ᵗ F(x(s)) ds` for `t ≥ 0`, where `x = (s, i)`. -/
theorem eq_add_integral_drift {β γ : ℝ} {s i r : ℝ → ℝ} (hode : SIR.IsSolution β γ 1 s i r)
    {t : ℝ} (ht : 0 ≤ t) :
    (s t, i t) = (s 0, i 0) + ∫ u in (0 : ℝ)..t, drift β γ (s u, i u) := by
  have hd : ∀ u ∈ uIcc 0 t, HasDerivAt (fun u => (s u, i u)) (drift β γ (s u, i u)) u := by
    intro u hu
    rw [uIcc_of_le ht] at hu
    have h := (hode.hasDerivAt_susceptible u hu.1).prodMk (hode.hasDerivAt_infected u hu.1)
    rw [show drift β γ (s u, i u) = (-(β * s u * i u / 1), β * s u * i u / 1 - γ * i u) by
      simp only [drift, div_one]]
    exact h
  have hc : ContinuousOn (fun u => drift β γ (s u, i u)) (uIcc 0 t) :=
    (continuous_drift β γ).comp_continuousOn (HasDerivAt.continuousOn hd)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  abel

/-- A solution of the SIR system is continuous on `[0, T]`. -/
theorem continuousOn_of_isSolution {β γ T : ℝ} {s i r : ℝ → ℝ}
    (hode : SIR.IsSolution β γ 1 s i r) : ContinuousOn (fun t => (s t, i t)) (Icc 0 T) :=
  fun t ht => ((hode.hasDerivAt_susceptible t ht.1).continuousAt.prodMk
    (hode.hasDerivAt_infected t ht.1).continuousAt).continuousWithinAt

/-! ### Kurtz's pathwise estimate -/

/-- **Kurtz's pathwise estimate for the fluctuations.** Let `x` solve `x(t) = x(0) + ∫₀ᵗ F(x)`
on `[0, T]` with `‖x‖ ≤ B`, let `X` be a measurable path with `‖X - x‖ ≤ δ ≤ 1` on `[0, T]`,
and let `U` solve the fluctuation equation driven by `m` from `u₀`, with `‖u₀‖, ‖m‖ ≤ k`. If the
initial fluctuation `√N (X(0) - x(0))` is within `ρ` of `u₀` and the scaled martingale
`√N (X(t) - X(0) - ∫₀ᵗ F(X))` is within `ρ` of `m(t)` on `[0, T]`, then on `[0, T]`

  `‖√N (X(t) - x(t)) - U(t)‖ ≤ (3 ρ + β δ T · 3 k e^{L T}) e^{(L + β) T}`,  `L = 2 β B + γ`.

The scaled martingale vanishes at `t = 0`, so `‖m(0)‖ ≤ ρ`; this third `ρ` and the `3 k` of
`IsFluctuationPath.norm_le` come from the increment `m(t) - m(0)` in the fluctuation equation.
The proof writes `√N (F(X) - F(x)) = DF(x) U_N + β (U_N)₁ (X - x)₂ (-1, 1)` (`drift_add`) and
applies Gronwall's inequality to `‖U_N - U‖`. -/
theorem norm_sqrt_smul_sub_sub_le {β γ T B δ ρ k : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {N : ℕ}
    {X x : ℝ → ℝ × ℝ} {u₀ : ℝ × ℝ} {m U : ℝ → ℝ × ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ B) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, drift β γ (x s))
    (hX : Measurable X) (hδ : ∀ t ∈ Icc 0 T, ‖X t - x t‖ ≤ δ) (hδ1 : δ ≤ 1)
    (hU : IsFluctuationPath β γ T x u₀ m U) (hu₀ : ‖u₀‖ ≤ k) (hm : ∀ t ∈ Icc 0 T, ‖m t‖ ≤ k)
    (hρ₀ : ‖Real.sqrt N • (X 0 - x 0) - u₀‖ ≤ ρ)
    (hρ : ∀ t ∈ Icc 0 T,
      ‖Real.sqrt N • (X t - X 0 - ∫ s in (0 : ℝ)..t, drift β γ (X s)) - m t‖ ≤ ρ) :
    ∀ t ∈ Icc 0 T, ‖Real.sqrt N • (X t - x t) - U t‖ ≤
      (3 * ρ + β * δ * T * (3 * k * exp ((2 * β * B + γ) * T))) *
        exp ((2 * β * B + γ + β) * T) := by
  intro t₀ ht₀
  have hT : 0 ≤ T := ht₀.1.trans ht₀.2
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hk : 0 ≤ k := (norm_nonneg _).trans hu₀
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 h0)
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ₀
  -- the scaled martingale vanishes at `t = 0`, so `m 0` is within `ρ` of `0`
  have hm0 : ‖m 0‖ ≤ ρ := by simpa using hρ 0 h0
  set c : ℝ := Real.sqrt N with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  set L : ℝ := 2 * β * B + γ with hLdef
  have hL : 0 ≤ L := by positivity
  set K' : ℝ := 3 * k * exp (L * T) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hUb : ∀ s ∈ Icc 0 T, ‖U s‖ ≤ K' := fun s hs =>
    (hU.norm_le hβ hγ hB0 hB hxc hu₀ hm s hs).trans (by
      rw [hK']; gcongr; exact hs.2)
  -- measurability on `[0, T]`
  have hXae : AEStronglyMeasurable X (volume.restrict (Icc 0 T)) := hX.aestronglyMeasurable
  have hxae : AEStronglyMeasurable x (volume.restrict (Icc 0 T)) :=
    hxc.aestronglyMeasurable measurableSet_Icc
  have hUae : AEStronglyMeasurable U (volume.restrict (Icc 0 T)) :=
    hU.continuousOn.aestronglyMeasurable measurableSet_Icc
  have hbound : ∀ {f : ℝ → ℝ × ℝ}, AEStronglyMeasurable f (volume.restrict (Icc 0 T)) →
      ∀ C, (∀ s ∈ Icc 0 T, ‖f s‖ ≤ C) → IntegrableOn f (Icc 0 T) := fun hf C hC =>
    IntegrableOn.of_bound measure_Icc_lt_top hf C
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hC))
  -- the pieces
  set u : ℝ → ℝ × ℝ := fun s => c • (X s - x s) with hu
  set d : ℝ → ℝ × ℝ := fun s => u s - U s with hd
  set e : ℝ → ℝ × ℝ := fun s =>
    (c * (β * (X s - x s).1 * (X s - x s).2)) • ((-1 : ℝ), (1 : ℝ)) with he
  set g : ℝ → ℝ × ℝ := fun s => jacobian β γ (x s) (d s) + e s with hg
  have huae : AEStronglyMeasurable u (volume.restrict (Icc 0 T)) := (hXae.sub hxae).const_smul c
  have hui : IntegrableOn u (Icc 0 T) := hbound huae (c * δ) fun s hs => by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hδ s hs) hc0
  have hdi : IntegrableOn d (Icc 0 T) := hui.sub hU.continuousOn.integrableOn_Icc
  obtain ⟨CF, hCF⟩ := (isCompact_closedBall (0 : ℝ × ℝ) (B + 1)).exists_bound_of_continuousOn
    (continuous_drift β γ).continuousOn
  have hFXi : IntegrableOn (fun s => drift β γ (X s)) (Icc 0 T) :=
    hbound ((continuous_drift β γ).comp_aestronglyMeasurable hXae) CF fun s hs => by
      refine hCF _ (mem_closedBall_zero_iff.2 ?_)
      calc ‖X s‖ = ‖(X s - x s) + x s‖ := by rw [sub_add_cancel]
        _ ≤ ‖X s - x s‖ + ‖x s‖ := norm_add_le _ _
        _ ≤ 1 + B := add_le_add ((hδ s hs).trans hδ1) (hB s hs)
        _ = B + 1 := add_comm _ _
  have hFxc : ContinuousOn (fun s => drift β γ (x s)) (Icc 0 T) :=
    (continuous_drift β γ).comp_continuousOn hxc
  have hJU : ContinuousOn (fun s => jacobian β γ (x s) (U s)) (Icc 0 T) :=
    (continuous_jacobian β γ).comp_continuousOn (hxc.prodMk hU.continuousOn)
  have heae : AEStronglyMeasurable e (volume.restrict (Icc 0 T)) := by
    have hφ : Continuous (fun h : ℝ × ℝ => (c * (β * h.1 * h.2)) • ((-1 : ℝ), (1 : ℝ))) := by
      fun_prop
    exact hφ.comp_aestronglyMeasurable (hXae.sub hxae)
  -- pointwise bound on the remainder
  have hnorm11 : ‖((-1 : ℝ), (1 : ℝ))‖ = 1 := by simp
  have heb : ∀ s ∈ Icc 0 T, ‖e s‖ ≤ β * δ * (‖d s‖ + K') := by
    intro s hs
    have h1 : c * |(X s - x s).1| ≤ ‖d s‖ + K' := by
      have : c * |(X s - x s).1| = |(u s).1| := by
        simp only [u, Prod.smul_fst, smul_eq_mul, abs_mul, abs_of_nonneg hc0]
      rw [this]
      calc |(u s).1| ≤ ‖u s‖ := abs_fst_le _
        _ = ‖d s + U s‖ := by simp only [d, sub_add_cancel]
        _ ≤ ‖d s‖ + ‖U s‖ := norm_add_le _ _
        _ ≤ ‖d s‖ + K' := by gcongr; exact hUb s hs
    have h2 : |(X s - x s).2| ≤ δ := (abs_snd_le _).trans (hδ s hs)
    simp only [e, norm_smul, hnorm11, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0,
      abs_of_nonneg hβ]
    calc c * (β * |(X s - x s).1| * |(X s - x s).2|)
        = β * (c * |(X s - x s).1|) * |(X s - x s).2| := by ring
      _ ≤ β * (‖d s‖ + K') * δ := by gcongr
      _ = β * δ * (‖d s‖ + K') := by ring
  have hgb : ∀ s ∈ Icc 0 T, ‖g s‖ ≤ (L + β) * ‖d s‖ + β * δ * K' := by
    intro s hs
    have hj := norm_jacobian_le_of_le hβ hγ (hB s hs) (d s)
    have hes := heb s hs
    have hds := norm_nonneg (d s)
    calc ‖g s‖ ≤ ‖jacobian β γ (x s) (d s)‖ + ‖e s‖ := norm_add_le _ _
      _ ≤ L * ‖d s‖ + β * δ * (‖d s‖ + K') := add_le_add hj hes
      _ ≤ (L + β) * ‖d s‖ + β * δ * K' := by
          have : β * δ * ‖d s‖ ≤ β * ‖d s‖ := by
            have := mul_le_mul_of_nonneg_left hδ1 hβ
            nlinarith
          nlinarith
  have hgi : IntegrableOn g (Icc 0 T) := by
    have hgae : AEStronglyMeasurable g (volume.restrict (Icc 0 T)) :=
      ((continuous_jacobian β γ).comp_aestronglyMeasurable (hxae.prodMk hdi.1)).add heae
    refine hbound hgae ((L + β) * (c * δ + K') + β * δ * K') fun s hs => (hgb s hs).trans ?_
    have hds : ‖d s‖ ≤ c * δ + K' := by
      calc ‖d s‖ ≤ ‖u s‖ + ‖U s‖ := norm_sub_le _ _
        _ ≤ c * δ + K' := by
            gcongr
            · simp only [u, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
              exact mul_le_mul_of_nonneg_left (hδ s hs) hc0
            · exact hUb s hs
    gcongr
  -- the integral identity
  have hident : ∀ t ∈ Icc 0 T, d t = (c • (X 0 - x 0) - u₀) +
      (c • (X t - X 0 - ∫ s in (0 : ℝ)..t, drift β γ (X s)) - m t) + m 0 +
      ∫ s in (0 : ℝ)..t, g s := by
    intro t ht
    have hpt : ∀ s, g s = c • (drift β γ (X s) - drift β γ (x s)) - jacobian β γ (x s) (U s) := by
      intro s
      have hexp := drift_add β γ (x s) (X s - x s)
      rw [add_sub_cancel] at hexp
      rw [hexp]
      simp only [g, d, u, e, jacobian_sub, jacobian_smul]
      module
    have hFXii := intervalIntegrable_of_integrableOn hFXi ht
    have hFxii := (continuousOn_uIcc_of_Icc hFxc ht).intervalIntegrable (μ := volume)
    have hJUii := (continuousOn_uIcc_of_Icc hJU ht).intervalIntegrable (μ := volume)
    have hA : IntervalIntegrable (fun s => c • (drift β γ (X s) - drift β γ (x s))) volume 0 t :=
      (hFXii.sub hFxii).smul c
    rw [intervalIntegral.integral_congr (fun s _ => hpt s),
      intervalIntegral.integral_sub hA hJUii,
      intervalIntegral.integral_smul, intervalIntegral.integral_sub hFXii hFxii]
    have hxt := hx t ht
    have hUt := hU.eq t ht
    have hint_x : ∫ s in (0 : ℝ)..t, drift β γ (x s) = x t - x 0 := by
      rw [hxt]; abel
    have hint_U : ∫ s in (0 : ℝ)..t, jacobian β γ (x s) (U s) = U t - u₀ - (m t - m 0) := by
      rw [hUt]; abel
    rw [hint_x, hint_U]
    simp only [d, u, smul_sub]
    abel
  -- Gronwall
  have hgron := StochasticSIR.le_mul_exp_of_le_add_integral (a := 3 * ρ + β * δ * T * K')
    (by positivity : 0 ≤ L + β) hdi.norm (fun _ _ => norm_nonneg _) fun t ht => ?_
  · calc ‖c • (X t₀ - x t₀) - U t₀‖ = ‖d t₀‖ := rfl
      _ ≤ (3 * ρ + β * δ * T * K') * exp ((L + β) * t₀) := hgron t₀ ht₀
      _ ≤ (3 * ρ + β * δ * T * K') * exp ((L + β) * T) := by
          gcongr
          exact ht₀.2
  have hgii := intervalIntegrable_of_integrableOn hgi ht
  have hdii := intervalIntegrable_of_integrableOn hdi.norm ht
  rw [hident t ht]
  calc ‖(c • (X 0 - x 0) - u₀) + (c • (X t - X 0 - ∫ s in (0 : ℝ)..t, drift β γ (X s)) - m t) +
        m 0 + ∫ s in (0 : ℝ)..t, g s‖
      ≤ ‖c • (X 0 - x 0) - u₀‖ +
          ‖c • (X t - X 0 - ∫ s in (0 : ℝ)..t, drift β γ (X s)) - m t‖ + ‖m 0‖ +
          ‖∫ s in (0 : ℝ)..t, g s‖ := norm_add₄_le
    _ ≤ ρ + ρ + ρ + ∫ s in (0 : ℝ)..t, ((L + β) * ‖d s‖ + β * δ * K') := by
        gcongr
        · exact hρ t ht
        · refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
          exact intervalIntegral.integral_mono_on ht.1 hgii.norm
            ((hdii.const_mul _).add intervalIntegrable_const) fun s hs =>
              hgb s ⟨hs.1, hs.2.trans ht.2⟩
    _ = 3 * ρ + β * δ * K' * t + (L + β) * ∫ s in (0 : ℝ)..t, ‖d s‖ := by
        rw [intervalIntegral.integral_add (hdii.const_mul _) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ 3 * ρ + β * δ * T * K' + (L + β) * ∫ s in (0 : ℝ)..t, ‖d s‖ := by
        have : β * δ * K' * t ≤ β * δ * T * K' := by
          have := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0 ≤ β * δ * K')
          linarith
        linarith

/-! ### The diffusion approximation -/

/-- The scaled fluctuation `U_N(t) = √N (X_N(t) - x(t))` of a family of density paths
`X N ω : ℝ → ℝ × ℝ` around the deterministic path `x`. For the SIR chain,
`X N ω t = (S(t) / N, I(t) / N)`. -/
noncomputable def fluctuation {Ω : Type*} (X : ℕ → Ω → ℝ → ℝ × ℝ) (x : ℝ → ℝ × ℝ) (N : ℕ)
    (ω : Ω) (t : ℝ) : ℝ × ℝ :=
  Real.sqrt N • (X N ω t - x t)

/-- The scaled martingale `M_N(t) = √N (X_N(t) - X_N(0) - ∫₀ᵗ F(X_N(s)) ds)`. For the SIR chain
in its random time-change representation this is
`Σ_ℓ ℓ N^{-1/2} (Y_ℓ(N ∫₀ᵗ λ_ℓ(X_N)) - N ∫₀ᵗ λ_ℓ(X_N))` with unit Poisson processes `Y_ℓ`. For a
general family `X` it is just the process above: it is a martingale only when `X` is the scaled
SIR chain, and no result here uses the martingale property. -/
noncomputable def scaledMartingale {Ω : Type*} (β γ : ℝ) (X : ℕ → Ω → ℝ → ℝ × ℝ) (N : ℕ)
    (ω : Ω) (t : ℝ) : ℝ × ℝ :=
  Real.sqrt N • (X N ω t - X N ω 0 - ∫ s in (0 : ℝ)..t, drift β γ (X N ω s))

private theorem exists_rat_mem_Icc_dist_lt {T t ε : ℝ} (ht : t ∈ Icc 0 T) (hε : 0 < ε) :
    ∃ q : ℚ, (q : ℝ) ∈ Icc 0 T ∧ dist (q : ℝ) t < ε := by
  rcases eq_or_lt_of_le (ht.1.trans ht.2) with hT | hT
  · subst hT
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    exact ⟨0, by simp, by simp [ht0, hε]⟩
  · have hlt : max 0 (t - ε) < min T (t + ε) :=
      max_lt (lt_min hT (by linarith [ht.1])) (lt_min (by linarith [ht.2]) (by linarith))
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    refine ⟨q, ⟨(le_max_left _ _).trans hq1.le, hq2.le.trans (min_le_left _ _)⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_right 0 (t - ε)]
    · linarith [min_le_right T (t + ε)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Tightness of the limit data.** If `U₀` is measurable and `M` has continuous paths on
`[0, T]` and measurable marginals, then `P(‖U₀‖ > k or ‖M(t)‖ > k for some t ∈ [0, T]) → 0` as
`k → ∞`. (The event is measurable: by path continuity it is a countable union over rational
times.) -/
theorem tendsto_measure_norm_gt [IsFiniteMeasure μ] {T : ℝ} {U₀ : Ω → ℝ × ℝ}
    {M : Ω → ℝ → ℝ × ℝ} (hU₀ : Measurable U₀) (hMc : ∀ ω, ContinuousOn (M ω) (Icc 0 T))
    (hMm : ∀ t, Measurable fun ω => M ω t) :
    Tendsto (fun k : ℕ => μ {ω | (k : ℝ) < ‖U₀ ω‖ ∨ ∃ t ∈ Icc 0 T, (k : ℝ) < ‖M ω t‖})
      atTop (𝓝 0) := by
  set A : ℕ → Set Ω := fun k => {ω | (k : ℝ) < ‖U₀ ω‖ ∨ ∃ t ∈ Icc 0 T, (k : ℝ) < ‖M ω t‖}
  have hA : ∀ k, A k = {ω | (k : ℝ) < ‖U₀ ω‖} ∪
      ⋃ q : ℚ, {ω | (q : ℝ) ∈ Icc 0 T ∧ (k : ℝ) < ‖M ω q‖} := by
    intro k
    ext ω
    simp only [A, mem_ofPred_eq, mem_union, mem_iUnion]
    constructor
    · rintro (h | ⟨t, ht, h⟩)
      · exact Or.inl h
      · right
        have hev : ∀ᶠ s in 𝓝[Icc 0 T] t, (k : ℝ) < ‖M ω s‖ :=
          ((hMc ω t ht).norm).eventually_const_lt h
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
        obtain ⟨q, hq, hqd⟩ := exists_rat_mem_Icc_dist_lt ht hε
        exact ⟨q, hq, hball ⟨Metric.mem_ball.2 hqd, hq⟩⟩
    · rintro (h | ⟨q, hq, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, hq, h⟩
  have hmeas : ∀ k, MeasurableSet (A k) := by
    intro k
    rw [hA k]
    refine (measurableSet_lt measurable_const hU₀.norm).union (MeasurableSet.iUnion fun q => ?_)
    by_cases hq : (q : ℝ) ∈ Icc 0 T
    · simpa [hq] using measurableSet_lt measurable_const (hMm q).norm
    · simp [hq]
  have hanti : Antitone A := by
    intro k k' hkk' ω hω
    have hk : (k : ℝ) ≤ k' := Nat.cast_le.2 hkk'
    rcases hω with h | ⟨t, ht, h⟩
    · exact Or.inl (hk.trans_lt h)
    · exact Or.inr ⟨t, ht, hk.trans_lt h⟩
  have hInter : (⋂ k, A k) = ∅ := by
    refine eq_empty_of_forall_notMem fun ω hω => ?_
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hMc ω)
    obtain ⟨n, hn⟩ := exists_nat_gt (max C ‖U₀ ω‖)
    rcases mem_iInter.1 hω n with h | ⟨t, ht, h⟩
    · exact lt_asymm hn (h.trans_le (le_max_right _ _))
    · exact absurd ((h.trans_le (hC t ht)).trans_le (le_max_left _ _)) (not_lt.2 hn.le)
  have := tendsto_measure_iInter_atTop (μ := μ) (fun k => (hmeas k).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rwa [hInter, measure_empty] at this

/-- **Diffusion approximation for the stochastic SIR epidemic** (Kurtz 1971;
Ethier–Kurtz 1986, ch. 11, Thm 2.3), with the law of large numbers and the martingale
functional CLT as hypotheses.

Let `x = (s, i)` solve the Kermack–McKendrick system in densities (`SIR.IsSolution β γ 1`), and
let `X N ω : ℝ → ℝ × ℝ` be measurable density paths. Assume, for every `δ > 0`,

* (law of large numbers) `P(∃ t ∈ [0, T], ‖X_N(t) - x(t)‖ ≥ δ) → 0`;
* (initial fluctuations) `P(‖U_N(0) - U₀‖ ≥ δ) → 0`, with `U₀` measurable;
* (martingale CLT, coupled form) `P(∃ t ∈ [0, T], ‖M_N(t) - M(t)‖ ≥ δ) → 0`, for a process
  `M` with continuous paths on `[0, T]` and measurable marginals;

and let `U` solve the linear fluctuation equation `U(t) = U₀ + (M(t) - M(0)) + ∫₀ᵗ DF(x) U`
pathwise.
Then the scaled fluctuations converge to `U` uniformly on `[0, T]` in probability:
`P(∃ t ∈ [0, T], ‖√N (X_N(t) - x(t)) - U(t)‖ ≥ ε) → 0` for every `ε > 0`. This event contains
the strict supremum event `sup > ε`; the non-strict supremum event `sup ≥ ε` is
`tendsto_measure_iSup_fluctuation_sub`. -/
theorem tendsto_measure_fluctuation_sub [IsFiniteMeasure μ] {β γ T : ℝ} (hβ : 0 ≤ β)
    (hγ : 0 ≤ γ) {s i r : ℝ → ℝ} (hode : SIR.IsSolution β γ 1 s i r)
    {X : ℕ → Ω → ℝ → ℝ × ℝ} (hX : ∀ N ω, Measurable (X N ω))
    (hLLN : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      δ ≤ ‖X N ω t - (s t, i t)‖}) atTop (𝓝 0))
    {U₀ : Ω → ℝ × ℝ} (hU₀ : Measurable U₀)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω |
      δ ≤ ‖fluctuation X (fun t => (s t, i t)) N ω 0 - U₀ ω‖}) atTop (𝓝 0))
    {M : Ω → ℝ → ℝ × ℝ} (hMc : ∀ ω, ContinuousOn (M ω) (Icc 0 T))
    (hMm : ∀ t, Measurable fun ω => M ω t)
    (hFCLT : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      δ ≤ ‖scaledMartingale β γ X N ω t - M ω t‖}) atTop (𝓝 0))
    {U : Ω → ℝ → ℝ × ℝ}
    (hU : ∀ ω, IsFluctuationPath β γ T (fun t => (s t, i t)) (U₀ ω) (M ω) (U ω))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      ε ≤ ‖fluctuation X (fun t => (s t, i t)) N ω t - U ω t‖}) atTop (𝓝 0) := by
  set x : ℝ → ℝ × ℝ := fun t => (s t, i t) with hxdef
  rcases lt_or_ge T 0 with hT | hT
  · simp [Icc_eq_empty_of_lt hT]
  have hxc : ContinuousOn x (Icc 0 T) := continuousOn_of_isSolution hode
  have hxint : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ u in (0 : ℝ)..t, drift β γ (x u) :=
    fun t ht => eq_add_integral_drift hode ht.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hxc
  set B := max C 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ B := fun t ht => (hC t ht).trans (le_max_left _ _)
  set L : ℝ := 2 * β * B + γ
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨k, hk⟩ := ((ENNReal.tendsto_nhds_zero.1
    (tendsto_measure_norm_gt (μ := μ) hU₀ hMc hMm)) _ hη2).exists
  set kk : ℝ := (k : ℝ)
  have hkk : 0 ≤ kk := Nat.cast_nonneg k
  set Cst : ℝ := (3 + β * T * (3 * kk * exp (L * T))) * exp ((L + β) * T) with hCst
  have hCst0 : 0 < Cst := by positivity
  set θ : ℝ := min 1 (ε / (2 * Cst))
  have hθ : 0 < θ := lt_min one_pos (by positivity)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθC : θ * Cst < ε := by
    have : θ ≤ ε / (2 * Cst) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  set A : Set Ω := {ω | (k : ℝ) < ‖U₀ ω‖ ∨ ∃ t ∈ Icc 0 T, (k : ℝ) < ‖M ω t‖}
  set B₁ : ℕ → Set Ω := fun N => {ω | ∃ t ∈ Icc 0 T, θ ≤ ‖X N ω t - (s t, i t)‖}
  set B₂ : ℕ → Set Ω := fun N => {ω | θ ≤ ‖fluctuation X (fun t => (s t, i t)) N ω 0 - U₀ ω‖}
  set B₃ : ℕ → Set Ω := fun N => {ω | ∃ t ∈ Icc 0 T, θ ≤ ‖scaledMartingale β γ X N ω t - M ω t‖}
  have hsub : ∀ N, {ω | ∃ t ∈ Icc 0 T,
      ε ≤ ‖fluctuation X (fun t => (s t, i t)) N ω t - U ω t‖} ⊆ A ∪ (B₁ N ∪ B₂ N ∪ B₃ N) := by
    intro N ω ⟨t, ht, hle⟩
    by_contra hcon
    simp only [mem_union, not_or, A, B₁, B₂, B₃, mem_ofPred_eq, not_exists, not_and, not_le,
      not_lt] at hcon
    obtain ⟨⟨hU₀k, hMk⟩, ⟨h₁, h₂⟩, h₃⟩ := hcon
    have hbound := norm_sqrt_smul_sub_sub_le (N := N) (δ := θ) (ρ := θ) (k := kk) hβ hγ hB0 hB
      hxc hxint (hX N ω) (fun t ht => (h₁ t ht).le) hθ1 (hU ω) hU₀k hMk h₂.le
      (fun t ht => (h₃ t ht).le) t ht
    have heq : (3 * θ + β * θ * T * (3 * kk * exp ((2 * β * B + γ) * T))) *
        exp ((2 * β * B + γ + β) * T) = θ * Cst := by
      simp only [hCst, L]; ring
    rw [heq] at hbound
    exact absurd (hle.trans hbound) (not_le.2 hθC)
  have hlim : Tendsto (fun N => μ (B₁ N) + μ (B₂ N) + μ (B₃ N)) atTop (𝓝 (0 + 0 + 0)) :=
    ((hLLN θ hθ).add (hinit θ hθ)).add (hFCLT θ hθ)
  rw [add_zero, add_zero] at hlim
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hlim) _ hη2] with N hN
  calc μ {ω | ∃ t ∈ Icc 0 T, ε ≤ ‖fluctuation X (fun t => (s t, i t)) N ω t - U ω t‖}
      ≤ μ (A ∪ (B₁ N ∪ B₂ N ∪ B₃ N)) := measure_mono (hsub N)
    _ ≤ μ A + (μ (B₁ N) + μ (B₂ N) + μ (B₃ N)) := by
        refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hk hN
    _ = η := ENNReal.add_halves η

/-- **Diffusion approximation, supremum form.** Under the hypotheses of
`tendsto_measure_fluctuation_sub`, the supremum over `[0, T]` of
`‖√N (X_N(t) - x(t)) - U(t)‖` is at least `ε` with probability tending to `0`:

  `P(sup_{t ∈ [0, T]} ‖√N (X_N(t) - x(t)) - U(t)‖ ≥ ε) → 0`  as `N → ∞`.

The supremum is taken in `ℝ≥0∞`, so it exists for every path, bounded or not, and need not be
attained. The event lies inside the event of `tendsto_measure_fluctuation_sub` at threshold
`ε / 2`; it is not assumed measurable, and `μ` is applied as an outer measure. -/
theorem tendsto_measure_iSup_fluctuation_sub [IsFiniteMeasure μ] {β γ T : ℝ} (hβ : 0 ≤ β)
    (hγ : 0 ≤ γ) {s i r : ℝ → ℝ} (hode : SIR.IsSolution β γ 1 s i r)
    {X : ℕ → Ω → ℝ → ℝ × ℝ} (hX : ∀ N ω, Measurable (X N ω))
    (hLLN : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      δ ≤ ‖X N ω t - (s t, i t)‖}) atTop (𝓝 0))
    {U₀ : Ω → ℝ × ℝ} (hU₀ : Measurable U₀)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω |
      δ ≤ ‖fluctuation X (fun t => (s t, i t)) N ω 0 - U₀ ω‖}) atTop (𝓝 0))
    {M : Ω → ℝ → ℝ × ℝ} (hMc : ∀ ω, ContinuousOn (M ω) (Icc 0 T))
    (hMm : ∀ t, Measurable fun ω => M ω t)
    (hFCLT : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      δ ≤ ‖scaledMartingale β γ X N ω t - M ω t‖}) atTop (𝓝 0))
    {U : Ω → ℝ → ℝ × ℝ}
    (hU : ∀ ω, IsFluctuationPath β γ T (fun t => (s t, i t)) (U₀ ω) (M ω) (U ω))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => μ {ω | ENNReal.ofReal ε ≤
      ⨆ t ∈ Icc 0 T, ENNReal.ofReal ‖fluctuation X (fun t => (s t, i t)) N ω t - U ω t‖})
      atTop (𝓝 0) := by
  have hε2 : 0 < ε / 2 := half_pos hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_measure_fluctuation_sub hβ hγ hode hX hLLN hU₀ hinit hMc hMm hFCLT hU hε2)
    (fun _ => bot_le) (fun N => measure_mono fun ω hω => ?_)
  simp only [mem_ofPred_eq] at hω ⊢
  have hlt : ENNReal.ofReal (ε / 2) <
      ⨆ t ∈ Icc 0 T, ENNReal.ofReal ‖fluctuation X (fun t => (s t, i t)) N ω t - U ω t‖ :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε)) hω
  obtain ⟨t, ht⟩ := lt_iSup_iff.1 hlt
  obtain ⟨htT, hdev⟩ := lt_iSup_iff.1 ht
  exact ⟨t, htT, ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε2.le).1 hdev).le⟩

/-- **Convergence in distribution at a fixed time.** Under the hypotheses of
`tendsto_measure_fluctuation_sub`, and if each `X_N(t)` is a random variable, the scaled
fluctuation `√N (X_N(t) - x(t))` converges in distribution to `U(t)` for every `t ∈ [0, T]`. -/
theorem tendstoInDistribution_fluctuation [IsProbabilityMeasure μ] {β γ T : ℝ} (hβ : 0 ≤ β)
    (hγ : 0 ≤ γ) {s i r : ℝ → ℝ} (hode : SIR.IsSolution β γ 1 s i r)
    {X : ℕ → Ω → ℝ → ℝ × ℝ} (hX : ∀ N ω, Measurable (X N ω))
    (hLLN : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      δ ≤ ‖X N ω t - (s t, i t)‖}) atTop (𝓝 0))
    {U₀ : Ω → ℝ × ℝ} (hU₀ : Measurable U₀)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω |
      δ ≤ ‖fluctuation X (fun t => (s t, i t)) N ω 0 - U₀ ω‖}) atTop (𝓝 0))
    {M : Ω → ℝ → ℝ × ℝ} (hMc : ∀ ω, ContinuousOn (M ω) (Icc 0 T))
    (hMm : ∀ t, Measurable fun ω => M ω t)
    (hFCLT : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      δ ≤ ‖scaledMartingale β γ X N ω t - M ω t‖}) atTop (𝓝 0))
    {U : Ω → ℝ → ℝ × ℝ}
    (hU : ∀ ω, IsFluctuationPath β γ T (fun t => (s t, i t)) (U₀ ω) (M ω) (U ω))
    (hXt : ∀ N t, AEMeasurable (fun ω => X N ω t) μ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    TendstoInDistribution (fun N ω => fluctuation X (fun t => (s t, i t)) N ω t) atTop
      (fun ω => U ω t) (fun _ => μ) μ := by
  have hmeas : TendstoInMeasure μ (fun N ω => fluctuation X (fun t => (s t, i t)) N ω t) atTop
      (fun ω => U ω t) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_measure_fluctuation_sub hβ hγ hode hX hLLN hU₀ hinit hMc hMm hFCLT hU hε)
      (fun _ => bot_le) fun N => measure_mono fun ω hω => ⟨t, ht, ?_⟩
    rw [mem_ofPred_eq, dist_eq_norm] at hω
    exact hω
  refine hmeas.tendstoInDistribution fun N => ?_
  unfold fluctuation
  exact ((hXt N t).sub (aemeasurable_const (b := (s t, i t)))).const_smul (Real.sqrt N)

/-- **Interface with Kurtz's law of large numbers.** The `ℓ¹` form of Kurtz's law of large
numbers for the count paths `(S, I, R)`, as proved by `StochasticSIR.tendsto_measure_deviation`
(whose `StochasticSIR.deviation` is the sum below), implies the hypothesis `hLLN` of
`tendsto_measure_fluctuation_sub` for the density paths `X_N = (S / N, I / N)`. -/
theorem tendsto_measure_norm_sub_of_deviation {S I R : ℕ → Ω → ℝ → ℕ} {s i r : ℝ → ℝ} {T : ℝ}
    (h : ∀ ε, 0 < ε → Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      ε ≤ |(S N ω t : ℝ) / N - s t| + |(I N ω t : ℝ) / N - i t| + |(R N ω t : ℝ) / N - r t|})
      atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      δ ≤ ‖((S N ω t : ℝ) / N, (I N ω t : ℝ) / N) - (s t, i t)‖}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h δ hδ)
    (fun _ => bot_le) fun N => measure_mono fun ω ⟨t, ht, hle⟩ => ⟨t, ht, hle.trans ?_⟩
  rw [Prod.mk_sub_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
  refine max_le ?_ ?_
  · linarith [abs_nonneg ((I N ω t : ℝ) / N - i t), abs_nonneg ((R N ω t : ℝ) / N - r t)]
  · linarith [abs_nonneg ((S N ω t : ℝ) / N - s t), abs_nonneg ((R N ω t : ℝ) / N - r t)]

/-! ### The limit covariance -/

/-- `V = (V₁₁, V₁₂, V₂₂)` is the **limit covariance** of the SIR diffusion approximation around
`x`, started from `V₀`: it solves the Lyapunov equation `V' = DF(x) V + V DF(x)ᵀ + G(x)`
(`lyapunovField`, written out in `lyapunovField_apply`) for `t ≥ 0`, with `V(0) = V₀`. The
derivative is taken within `[0, ∞)`, so it is one-sided at `t = 0` and the values of `V` at
negative times play no role. This is the covariance of the solution of `dU = DF(x(t)) U dt + dM`
when `M` is a Gaussian martingale with `d⟨M⟩ = G(x(t)) dt` and `U(0)` is centered Gaussian with
covariance `V₀`, independent of `M`; that identification is not proved in this file. -/
structure IsLimitCovariance (β γ : ℝ) (x : ℝ → ℝ × ℝ) (V₀ : ℝ × ℝ × ℝ) (V : ℝ → ℝ × ℝ × ℝ) :
    Prop where
  /-- The initial covariance. -/
  initial : V 0 = V₀
  /-- The Lyapunov equation on `[0, ∞)`, with a right derivative at `t = 0`. -/
  hasDerivWithinAt : ∀ t, 0 ≤ t → HasDerivWithinAt V (lyapunovField β γ (x t) (V t)) (Ici 0) t

/-- The Lyapunov field is Lipschitz in `V` with constant `2 (2 β B + γ)` when `‖p‖ ≤ B`. -/
theorem norm_lyapunovField_sub_le {β γ B : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {p : ℝ × ℝ}
    (hp : ‖p‖ ≤ B) (c c' : ℝ × ℝ × ℝ) :
    ‖lyapunovField β γ p c - lyapunovField β γ p c'‖ ≤ 2 * (2 * β * B + γ) * ‖c - c'‖ := by
  set Δ₁ : ℝ × ℝ := (c.1 - c'.1, c.2.1 - c'.2.1)
  set Δ₂ : ℝ × ℝ := (c.2.1 - c'.2.1, c.2.2 - c'.2.2)
  have hΔ₁ : ‖Δ₁‖ ≤ ‖c - c'‖ := by
    rw [Prod.norm_mk]
    refine max_le (norm_fst_le (c - c')) ?_
    exact (norm_fst_le (c - c').2).trans (norm_snd_le (c - c'))
  have hΔ₂ : ‖Δ₂‖ ≤ ‖c - c'‖ := by
    rw [Prod.norm_mk]
    refine max_le ?_ ?_
    · exact (norm_fst_le (c - c').2).trans (norm_snd_le (c - c'))
    · exact (norm_snd_le (c - c').2).trans (norm_snd_le (c - c'))
  have hJ₁ := norm_jacobian_le_of_le hβ hγ hp Δ₁
  have hJ₂ := norm_jacobian_le_of_le hβ hγ hp Δ₂
  have hj11 := abs_fst_le (jacobian β γ p Δ₁)
  have hj12 := abs_snd_le (jacobian β γ p Δ₁)
  have hj21 := abs_fst_le (jacobian β γ p Δ₂)
  have hj22 := abs_snd_le (jacobian β γ p Δ₂)
  have hL : 0 ≤ 2 * β * B + γ := by
    have := (norm_nonneg p).trans hp
    positivity
  have h₁ : (2 * β * B + γ) * ‖Δ₁‖ ≤ (2 * β * B + γ) * ‖c - c'‖ :=
    mul_le_mul_of_nonneg_left hΔ₁ hL
  have h₂ : (2 * β * B + γ) * ‖Δ₂‖ ≤ (2 * β * B + γ) * ‖c - c'‖ :=
    mul_le_mul_of_nonneg_left hΔ₂ hL
  have hdiff : lyapunovField β γ p c - lyapunovField β γ p c' =
      (2 * (jacobian β γ p Δ₁).1,
        (jacobian β γ p Δ₂).1 + (jacobian β γ p Δ₁).2, 2 * (jacobian β γ p Δ₂).2) := by
    simp only [lyapunovField, jacobian, Δ₁, Δ₂, Prod.mk_sub_mk, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  rw [hdiff, Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  refine max_le ?_ (max_le ?_ ?_)
  · rw [abs_mul, abs_two]; linarith
  · calc |(jacobian β γ p Δ₂).1 + (jacobian β γ p Δ₁).2|
        ≤ |(jacobian β γ p Δ₂).1| + |(jacobian β γ p Δ₁).2| := abs_add_le _ _
      _ ≤ 2 * (2 * β * B + γ) * ‖c - c'‖ := by linarith
  · rw [abs_mul, abs_two]; linarith

/-- **Uniqueness of the limit covariance.** Two solutions of the Lyapunov equation around a path
`x` continuous on `[0, T]`, with the same initial covariance, agree on `[0, T]`. In particular
the limit covariance `V(t)` is determined by `β`, `γ`, `x` and `V₀`. -/
theorem IsLimitCovariance.eqOn {β γ T : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {x : ℝ → ℝ × ℝ}
    (hxc : ContinuousOn x (Icc 0 T)) {V₀ : ℝ × ℝ × ℝ} {V V' : ℝ → ℝ × ℝ × ℝ}
    (hV : IsLimitCovariance β γ x V₀ V) (hV' : IsLimitCovariance β γ x V₀ V') :
    EqOn V V' (Icc 0 T) := by
  rcases (Icc 0 T).eq_empty_or_nonempty with hE | ⟨t₀, ht₀⟩
  · simp [hE]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hxc
  set B := max C 0
  have hB : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ B := fun t ht => (hC t ht).trans (le_max_left _ _)
  have hK : 0 ≤ 2 * (2 * β * B + γ) := by positivity
  have hcont : ∀ {W : ℝ → ℝ × ℝ × ℝ}, IsLimitCovariance β γ x V₀ W → ContinuousOn W (Icc 0 T) :=
    fun hW t ht => (hW.hasDerivWithinAt t ht.1).continuousWithinAt.mono Icc_subset_Ici_self
  refine ODE_solution_unique_of_mem_Icc_right (v := fun t => lyapunovField β γ (x t))
    (s := fun _ => univ) (K := Real.toNNReal (2 * (2 * β * B + γ))) (fun t ht => ?_)
    (hcont hV) (fun t ht => (hV.hasDerivWithinAt t ht.1).mono (Ici_subset_Ici.2 ht.1))
    (fun _ _ => mem_univ _)
    (hcont hV') (fun t ht => (hV'.hasDerivWithinAt t ht.1).mono (Ici_subset_Ici.2 ht.1))
    (fun _ _ => mem_univ _)
    (hV.initial.trans hV'.initial.symm)
  refine (LipschitzWith.of_dist_le_mul fun c c' => ?_).lipschitzOnWith
  rw [Real.coe_toNNReal _ hK, dist_eq_norm, dist_eq_norm]
  exact norm_lyapunovField_sub_le hβ hγ (hB t (Ico_subset_Icc_self ht)) c c'

end MathlibExt.Biology.Epidemiology.StochasticSIRDiffusion
