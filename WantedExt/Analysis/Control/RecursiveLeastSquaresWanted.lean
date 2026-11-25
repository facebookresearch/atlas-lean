/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Control.RecursiveLeastSquares
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Wanted: strong consistency of recursive least squares in stochastic regression

The convergence theorem of least squares for stochastic regression models with feedback,
attributed by the source below to Lai and Wei (Ann. Statist. 10 (1982)) and to Chen and Guo
(*Identification and Stochastic Adaptive Control*, Birkhäuser 1991): for the model
`y_{k+1} = φ_kᵀ θ + w_{k+1}` with martingale-difference noise and adapted regressors, the RLS
estimate satisfies
`|θ_{t+1} - θ|² = O(log r_t / λ_min(t))` almost surely, without any excitation assumption. It is
stated here in the single-sensor form of Xie, Zhang and Guo (*Convergence of a distributed least
squares*, IEEE Trans. Automat. Control, accepted version 2020, DOI 10.1109/TAC.2020.3047989,
Theorem 3.3 with `n = 1` sensor and graph diameter `D_G = 1`, as in their Remark 3.3).
-/

open MeasureTheory Filter Matrix
open MathlibExt.Analysis.Control.RecursiveLeastSquares

@[expose] public section

namespace MathlibExt.Analysis.Control.RecursiveLeastSquaresWanted

/-- **Convergence rate of recursive least squares under martingale-difference noise**
(Xie, Zhang and Guo, IEEE Trans. Automat. Control, DOI 10.1109/TAC.2020.3047989, Theorem 3.3
with one sensor; their introduction and Remark 3.3 attribute the single-sensor theory to Lai and
Wei, Ann. Statist. 10 (1982), and to Chen and Guo, *Identification and Stochastic Adaptive
Control*, Birkhäuser 1991). Let `(ℱ_k)` be a filtration, `θ ∈ ℝ^d` and
`y_{k+1} = φ_kᵀ θ + w_{k+1}`, where the regressor `φ_k` and the noise `w_k` are
`ℱ_k`-measurable (so `φ_k` may be computed by feedback from past outputs), the noise is a
martingale difference, `E[w_{k+1} | ℱ_k] = 0`, and for some `β > 2`,
`sup_k E[|w_{k+1}|^β | ℱ_k] < ∞` almost surely. Let `θ_t` be the RLS estimate from `θ_0` and a
positive definite `P_0`. Then almost surely, on the event `∑_{k ≤ t} |φ_k|² → ∞`, there is `C`
with `λ_min(t) |θ_{t+1} - θ|² ≤ C log(1 + ∑_{k ≤ t} |φ_k|²)` for all large `t`, where
`λ_min(t)` is the smallest eigenvalue of `P_0⁻¹ + ∑_{k ≤ t} φ_k φ_kᵀ`.

The smallest eigenvalue enters through its lower bounds `lam`
(`lam |x|² ≤ xᵀ (P_0⁻¹ + ∑_{k ≤ t} φ_k φ_kᵀ) x` for all `x`), which is equivalent. Compared
with the source, this statement also assumes `E|w_{k+1}|^β < ∞` (Mathlib's conditional
expectation of a non-integrable function is zero), and it is restricted to the event
`∑ |φ_k|² → ∞`, on which `log(1 + ∑ |φ_k|²)` and the source's
`log r_t = log(λ_max(P_0⁻¹) + ∑ |φ_k|²)` differ by a factor tending to one. -/
theorem_wanted rls_error_sq_le_log_div_lambdaMin {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀) {d : ℕ}
    (θ : Fin d → ℝ) (φ : ℕ → Ω → Fin d → ℝ) (w y : ℕ → Ω → ℝ)
    (hφ : Adapted ℱ φ) (hw : Adapted ℱ w) {β : ℝ} (hβ : 2 < β)
    (hint : ∀ k, Integrable (fun ω => |w (k + 1) ω| ^ β) μ)
    (hmart : ∀ k, μ[w (k + 1) | ℱ k] =ᵐ[μ] 0)
    (hmom : ∃ C : Ω → ℝ, ∀ k, μ[fun ω => |w (k + 1) ω| ^ β | ℱ k] ≤ᵐ[μ] C)
    (hy : ∀ k ω, y (k + 1) ω = φ k ω ⬝ᵥ θ + w (k + 1) ω)
    (θ₀ : Fin d → ℝ) {P₀ : Matrix (Fin d) (Fin d) ℝ} (hP₀ : P₀.PosDef) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun t => ∑ k ∈ Finset.range (t + 1), φ k ω ⬝ᵥ φ k ω) atTop atTop →
      ∃ C : ℝ, ∀ᶠ t in atTop, ∀ lam : ℝ,
        (∀ x : Fin d → ℝ,
          lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ (rlsInformation P₀ (fun k => φ k ω) (t + 1) *ᵥ x)) →
        lam * (((rls (fun k => φ k ω) (fun k => y k ω) θ₀ P₀ (t + 1)).1 - θ) ⬝ᵥ
            ((rls (fun k => φ k ω) (fun k => y k ω) θ₀ P₀ (t + 1)).1 - θ)) ≤
          C * Real.log (1 + ∑ k ∈ Finset.range (t + 1), φ k ω ⬝ᵥ φ k ω)

/-- **Logarithmic regret of the least-squares adaptive predictor** (Xie, Zhang and Guo, IEEE Trans.
Automat. Control, DOI 10.1109/TAC.2020.3047989, Theorem 3.2 with one sensor). In the setting of
`rls_error_sq_le_log_div_lambdaMin`, the best predictor of `y_{k+1}` given `ℱ_k` is `φ_kᵀ θ` and the
adaptive predictor is `φ_kᵀ θ_k`; their squared difference is the regret
`R_k = (φ_kᵀ (θ_k - θ))²`. If `φ_tᵀ P_t φ_t` is bounded in `t` almost surely, then almost surely,
on the event `∑_{k ≤ t} |φ_k|² → ∞`, there is `C` with
`∑_{k ≤ t} R_k ≤ C log(1 + ∑_{k ≤ t} |φ_k|²)` for all large `t`. No excitation condition is
assumed. As for `rls_error_sq_le_log_div_lambdaMin`, this assumes `E|w_{k+1}|^β < ∞` and is
restricted to the event `∑ |φ_k|² → ∞`, on which `log(1 + ∑ |φ_k|²)` and the source's `log r_t`
differ by a factor tending to one. -/
theorem_wanted rls_regret_sum_le_log {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m₀) {d : ℕ}
    (θ : Fin d → ℝ) (φ : ℕ → Ω → Fin d → ℝ) (w y : ℕ → Ω → ℝ)
    (hφ : Adapted ℱ φ) (hw : Adapted ℱ w) {β : ℝ} (hβ : 2 < β)
    (hint : ∀ k, Integrable (fun ω => |w (k + 1) ω| ^ β) μ)
    (hmart : ∀ k, μ[w (k + 1) | ℱ k] =ᵐ[μ] 0)
    (hmom : ∃ C : Ω → ℝ, ∀ k, μ[fun ω => |w (k + 1) ω| ^ β | ℱ k] ≤ᵐ[μ] C)
    (hy : ∀ k ω, y (k + 1) ω = φ k ω ⬝ᵥ θ + w (k + 1) ω)
    (θ₀ : Fin d → ℝ) {P₀ : Matrix (Fin d) (Fin d) ℝ} (hP₀ : P₀.PosDef)
    (hbdd : ∀ᵐ ω ∂μ, ∃ B : ℝ, ∀ t,
      φ t ω ⬝ᵥ ((rls (fun k => φ k ω) (fun k => y k ω) θ₀ P₀ t).2 *ᵥ φ t ω) ≤ B) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun t => ∑ k ∈ Finset.range (t + 1), φ k ω ⬝ᵥ φ k ω) atTop atTop →
      ∃ C : ℝ, ∀ᶠ t in atTop,
        ∑ k ∈ Finset.range (t + 1),
            (φ k ω ⬝ᵥ ((rls (fun k => φ k ω) (fun k => y k ω) θ₀ P₀ k).1 - θ)) ^ 2 ≤
          C * Real.log (1 + ∑ k ∈ Finset.range (t + 1), φ k ω ⬝ᵥ φ k ω)

end MathlibExt.Analysis.Control.RecursiveLeastSquaresWanted
