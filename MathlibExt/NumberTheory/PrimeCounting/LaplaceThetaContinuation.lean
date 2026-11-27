/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.NumberTheory.LSeries.PrimeLog
public import MathlibExt.NumberTheory.PrimeCounting.LaplaceTheta
@[expose] public section

/-!
# Shifted continuation for the normalized Chebyshev error

## ATLAS source correspondence

This module implements ATLAS NumberTheoryI N323, Corollary 16.12. At
atlas-lean commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, the statement is indexed
in [`v1/Atlas/NumberTheoryI/targets.yaml`, lines 2260--2265](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L2260-L2265): both
`Φ(s + 1) - 1 / s` and
`(ℒ H)(s) = Φ(s + 1) / (s + 1) - 1 / s` extend meromorphically to
`-1 / 2 < re s` and holomorphically to `0 ≤ re s`.

The primary formal source is
[`v1/Atlas/NumberTheoryI/code/PNT.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/PNT.lean):

* [`H` and its Laplace identity](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/PNT.lean#L1083-L1170)
  occupy lines 1083--1170;
* [`cor_16_12_Phi_shift_meromorphic`, lines 1172--1189](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/PNT.lean#L1172-L1189), shifts the N322
  continuation by `s ↦ s + 1`;
* [`cor_16_12_laplace_H_holomorphic`, lines 1191--1224](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/PNT.lean#L1191-L1224), uses
  `(g₁(s + 1) - 1) / (s + 1)` for the normalized error.

The declarations here map to those clauses as follows:

* `shiftedLogDirichletContinuation` is the shifted witness `g₁(s) = g(s + 1)`;
  its `_meromorphic`, `_analyticOn`, and `_agree` theorems give respectively
  the source domains `-1 / 2 < re s`, `0 ≤ re s`, and the continuation identity
  with `Φ(s + 1) - 1 / s` on `0 < re s`.
* `normalizedThetaError` is exactly the source `H(t) = θ(e^t)e^{-t} - 1`.
* `normalizedThetaErrorContinuation` is the source witness
  `(g₁(s) - 1) / (s + 1)`; its meromorphic and analytic theorems give the same
  two domains.
* `hasLaplace_normalizedThetaError` proves genuine convergence and the identity
  `(ℒ H)(s) = Φ(s + 1)/(s + 1) - 1/s` on `0 < re s`, using N321/Lemma 16.10
  ([`PNT.lean`, lines 282--284](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/PNT.lean#L282-L284))
  through `Chebyshev.hasLaplace_theta_exp`.

The source states existential continuations. Choosing the already constructed
canonical N322 witness is only an explicit representative of those existentials:
the `_agree` theorems prove the same identities on the original domains, so no
uniqueness or extra conclusion is assumed. Likewise, coercing the real-valued
`H` to `ℂ` is exactly the complex-valued Laplace transform required for complex
`s`; it changes neither `H` nor its convergence statement. `AnalyticOnNhd` is
the Mathlib encoding of holomorphy on the closed half-plane, namely analyticity
in a neighborhood of every point of that set.

This module formalizes the full N323 target, both continuation clauses of Corollary 16.12, via
explicit canonical witnesses for the source's existential statements.
-/

open MeasureTheory

namespace Nat.Primes

/-- **The shifted log-Dirichlet continuation.** Let $\Phi(s) = \sum_p \log p / p^s$, the sum over
primes, and let $g$ be the canonical continuation of $\Phi(s) - 1/(s - 1)$ to
$\operatorname{Re} s > 1/2$. For $s \in \mathbb{C}$, the shifted continuation is
$g_1(s) = g(s + 1)$. -/
noncomputable def shiftedLogDirichletContinuation (s : ℂ) : ℂ :=
  logDirichletContinuation (s + 1)

/-- **Meromorphy of the shifted continuation.** The shifted continuation $g_1$ is meromorphic at
every point $s \in \mathbb{C}$ with $\operatorname{Re} s > -1/2$. -/
theorem shiftedLogDirichletContinuation_meromorphic :
    MeromorphicOn shiftedLogDirichletContinuation
      {s | -(1 : ℝ) / 2 < s.re} := by
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  have hx1 : (1 : ℝ) / 2 < (x + 1).re := by
    have hAdd : (x + 1).re = x.re + 1 := by simp
    linarith
  have hBase : MeromorphicAt logDirichletContinuation (x + 1) :=
    logDirichletContinuation_meromorphic (x + 1) hx1
  have hAnalytic : AnalyticAt ℂ (fun s : ℂ => s + 1) x :=
    analyticAt_id.add analyticAt_const
  have hHas : HasDerivAt (fun s : ℂ => s + 1) 1 x := by
    simpa using (hasDerivAt_id x).add_const (1 : ℂ)
  have hDeriv : deriv (fun s : ℂ => s + 1) x ≠ 0 := by
    rw [hHas.deriv]
    exact one_ne_zero
  have hComp : MeromorphicAt
      (logDirichletContinuation ∘ fun s : ℂ => s + 1) x :=
    (meromorphicAt_comp_iff_of_deriv_ne_zero hAnalytic hDeriv).mpr hBase
  exact hComp

/-- **Holomorphy of the shifted continuation on the closed half-plane.** The shifted
continuation $g_1$ is complex analytic at every point $s \in \mathbb{C}$ with
$\operatorname{Re} s \ge 0$. -/
theorem shiftedLogDirichletContinuation_analyticOn :
    AnalyticOnNhd ℂ shiftedLogDirichletContinuation
      {s | 0 ≤ s.re} := by
  have hBase := logDirichletContinuation_analyticOn
  have hAnalytic : AnalyticOnNhd ℂ (fun s : ℂ => s + 1)
      {s | 0 ≤ s.re} :=
    analyticOnNhd_id.add analyticOnNhd_const
  have hMaps : Set.MapsTo (fun s : ℂ => s + 1) {s | 0 ≤ s.re}
      {s | 1 ≤ s.re} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hAdd : (x + 1).re = x.re + 1 := by simp
    linarith
  have hComp := hBase.comp hAnalytic hMaps
  exact hComp

/-- **The shifted continuation agrees with the shifted series.** Let
$\Phi(s) = \sum_p \log p / p^s$ be the prime logarithmic Dirichlet series and $g_1$ the shifted
continuation. For every $s \in \mathbb{C}$ with $\operatorname{Re} s > 0$,
$g_1(s) = \Phi(s + 1) - 1/s$. -/
theorem shiftedLogDirichletContinuation_agree :
    Set.EqOn shiftedLogDirichletContinuation
      (fun s => logDirichletSeries (s + 1) - 1 / s)
      {s | 0 < s.re} := by
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs
  have hRe : (1 : ℝ) < (s + 1).re := by
    have hAdd : (s + 1).re = s.re + 1 := by simp
    linarith
  have hMem : s + 1 ∈ {s | 1 < s.re} := by
    simpa only [Set.mem_ofPred_eq] using hRe
  have hEq := logDirichletContinuation_agree hMem
  have hSub : s + 1 - 1 = s := by ring
  have hBeta : (fun z : ℂ => logDirichletSeries z - 1 / (z - 1)) (s + 1)
      = logDirichletSeries (s + 1) - 1 / s := by
    change logDirichletSeries (s + 1) - 1 / (s + 1 - 1) = _
    rw [hSub]
  simp only [shiftedLogDirichletContinuation]
  exact hEq.trans hBeta

end Nat.Primes

namespace Chebyshev

/-- **The normalized Chebyshev error.** For real $t$, let $H(t) = \theta(e^t) e^{-t} - 1$, where
$\theta(x) = \sum_{p \le x} \log p$ is the Chebyshev function, the sum running over primes
$p \le x$. -/
noncomputable def normalizedThetaError (t : ℝ) : ℝ :=
  theta (Real.exp t) * Real.exp (-t) - 1

/-- **The normalized-error continuation.** Let $\Phi(s) = \sum_p \log p / p^s$, the sum over
primes, let $g$ be the canonical continuation of $\Phi(s) - 1/(s - 1)$, and let
$g_1(s) = g(s + 1)$ be the shifted continuation. For $s \in \mathbb{C}$, the normalized-error
continuation is $F(s) = (g_1(s) - 1)/(s + 1)$, with $F(-1) = 0$ since division by zero gives $0$.
-/
noncomputable def normalizedThetaErrorContinuation (s : ℂ) : ℂ :=
  (Nat.Primes.shiftedLogDirichletContinuation s - 1) / (s + 1)

/-- **Meromorphy of the normalized-error continuation.** The normalized-error continuation $F$
is meromorphic at every point $s \in \mathbb{C}$ with $\operatorname{Re} s > -1/2$. -/
theorem normalizedThetaErrorContinuation_meromorphic :
    MeromorphicOn normalizedThetaErrorContinuation
      {s | -(1 : ℝ) / 2 < s.re} := by
  have hShift := Nat.Primes.shiftedLogDirichletContinuation_meromorphic
  have hSub : MeromorphicOn
      (fun s : ℂ => Nat.Primes.shiftedLogDirichletContinuation s - 1)
      {s | -(1 : ℝ) / 2 < s.re} :=
    hShift.sub analyticOnNhd_const.meromorphicOn
  have hDen : MeromorphicOn (fun s : ℂ => s + 1)
      {s | -(1 : ℝ) / 2 < s.re} :=
    (analyticOnNhd_id.add analyticOnNhd_const).meromorphicOn
  have hDiv := hSub.div hDen
  exact hDiv

/-- **Holomorphy of the normalized-error continuation on the closed half-plane.** The
normalized-error continuation $F$ is complex analytic at every point $s \in \mathbb{C}$ with
$\operatorname{Re} s \ge 0$. -/
theorem normalizedThetaErrorContinuation_analyticOn :
    AnalyticOnNhd ℂ normalizedThetaErrorContinuation
      {s | 0 ≤ s.re} := by
  have hShift := Nat.Primes.shiftedLogDirichletContinuation_analyticOn
  have hSub : AnalyticOnNhd ℂ
      (fun s : ℂ => Nat.Primes.shiftedLogDirichletContinuation s - 1)
      {s | 0 ≤ s.re} :=
    hShift.sub analyticOnNhd_const
  have hDen : AnalyticOnNhd ℂ (fun s : ℂ => s + 1)
      {s | 0 ≤ s.re} :=
    analyticOnNhd_id.add analyticOnNhd_const
  have hNe : ∀ s ∈ {s : ℂ | 0 ≤ s.re}, (s + 1 : ℂ) ≠ 0 := by
    intro s hs h0
    simp only [Set.mem_ofPred_eq] at hs
    have hZero : (s + 1).re = 0 := by
      simp [h0]
    have hAdd : (s + 1).re = s.re + 1 := by simp
    linarith
  have hDiv := hSub.div hDen hNe
  exact hDiv

/-- **Laplace transform of the normalized Chebyshev error.** Let
$\theta(x) = \sum_{p \le x} \log p$ be the Chebyshev function (the sum over primes $p \le x$),
let $H(t) = \theta(e^t) e^{-t} - 1$ for real $t$ be the normalized Chebyshev error, viewed as a
complex-valued function, and let $F$ be the normalized-error continuation. For every
$s \in \mathbb{C}$ with $\operatorname{Re} s > 0$, the function $t \mapsto e^{-st} H(t)$ is
integrable on $(0, \infty)$ and $\int_{(0, \infty)} e^{-st} H(t)\,dt = F(s)$. -/
theorem hasLaplace_normalizedThetaError (s : ℂ) (hs : 0 < s.re) :
    HasLaplace (fun t : ℝ => (normalizedThetaError t : ℂ)) s
      (normalizedThetaErrorContinuation s) := by
  have hs1 : (1 : ℝ) < (s + 1).re := by
    have hAdd : (s + 1).re = s.re + 1 := by simp
    linarith
  have hTheta := Chebyshev.hasLaplace_theta_exp (s + 1) hs1
  obtain ⟨hThetaConv, hThetaVal⟩ := hTheta
  have hs0 : s ≠ 0 := by
    intro h0
    simp [h0] at hs
  have hs1ne : s + 1 ≠ 0 := by
    intro h0
    have hZero : (s + 1).re = 0 := by simp [h0]
    have hAdd : (s + 1).re = s.re + 1 := by simp
    linarith
  have hNeg : (-s).re < 0 := by
    have hEq : (-s).re = -s.re := by simp
    linarith
  have hBaseInt := integrableOn_exp_mul_complex_Ioi hNeg 0
  have hEqFun2 : (fun t : ℝ =>
      Complex.exp (-s * (t : ℂ)) • (1 : ℂ))
      = (fun t : ℝ => Complex.exp ((-s) * (t : ℂ))) := by
    funext t
    simp only [smul_eq_mul, mul_one, neg_mul]
  have h2 : IntegrableOn
      (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • (1 : ℂ))
      (Set.Ioi 0) := by
    rw [hEqFun2]
    exact hBaseInt
  have h1 : IntegrableOn (fun t : ℝ =>
      Complex.exp (-(s + 1) * (t : ℂ)) •
        (theta (Real.exp t) : ℂ)) (Set.Ioi 0) :=
    hThetaConv
  have hExpEq : ∀ t : ℝ, Complex.exp (-s * (t : ℂ)) *
      ((Real.exp (-t) : ℝ) : ℂ)
      = Complex.exp (-(s + 1) * (t : ℂ)) := by
    intro t
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hPoint : ∀ t : ℝ, Complex.exp (-s * (t : ℂ)) •
      (normalizedThetaError t : ℂ)
      = (Complex.exp (-(s + 1) * (t : ℂ)) •
        (theta (Real.exp t) : ℂ))
        - (Complex.exp (-s * (t : ℂ)) • (1 : ℂ)) := by
    intro t
    simp only [normalizedThetaError, smul_eq_mul]
    rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one]
    have hE := hExpEq t
    linear_combination (theta (Real.exp t) : ℂ) * hE
  have hEqFun : (fun t : ℝ =>
      Complex.exp (-s * (t : ℂ)) • (normalizedThetaError t : ℂ))
      = (fun t : ℝ => (Complex.exp (-(s + 1) * (t : ℂ)) •
        (theta (Real.exp t) : ℂ))
        - (Complex.exp (-s * (t : ℂ)) • (1 : ℂ))) := by
    funext t
    exact hPoint t
  have hConv : LaplaceConvergent (fun t : ℝ => (normalizedThetaError t : ℂ)) s := by
    unfold LaplaceConvergent
    rw [hEqFun]
    exact h1.sub h2
  have hThetaInt : (∫ t : ℝ in Set.Ioi 0,
      Complex.exp (-(s + 1) * (t : ℂ)) •
        (theta (Real.exp t) : ℂ))
      = Chebyshev.primeLogSeries (s + 1) / (s + 1) :=
    hThetaVal
  have hEqInt : (∫ t : ℝ in Set.Ioi 0,
      Complex.exp (-s * (t : ℂ)) • (1 : ℂ))
      = (∫ t : ℝ in Set.Ioi 0,
        Complex.exp ((-s) * (t : ℂ))) := by
    congr 1
  have hConstBase := integral_exp_mul_complex_Ioi hNeg 0
  have hBridge : Chebyshev.primeLogSeries (s + 1)
      = Nat.Primes.logDirichletSeries (s + 1) := by
    unfold Chebyshev.primeLogSeries Nat.Primes.logDirichletSeries
    apply tsum_congr
    intro b
    simp only [Complex.cpow_neg, div_eq_mul_inv]
  have hAgree := Nat.Primes.shiftedLogDirichletContinuation_agree
    (by simpa only [Set.mem_ofPred_eq] using hs :
      s ∈ {s | 0 < s.re})
  have hVal : laplace (fun t : ℝ => (normalizedThetaError t : ℂ)) s
      = Chebyshev.primeLogSeries (s + 1) / (s + 1) - 1 / s := by
    have hIntEq : (∫ t : ℝ in Set.Ioi 0,
        Complex.exp (-s * (t : ℂ)) • (normalizedThetaError t : ℂ))
        = (∫ t : ℝ in Set.Ioi 0,
          Complex.exp (-(s + 1) * (t : ℂ)) •
            (theta (Real.exp t) : ℂ))
          - (∫ t : ℝ in Set.Ioi 0,
            Complex.exp (-s * (t : ℂ)) • (1 : ℂ)) := by
      rw [hEqFun]
      exact integral_sub h1 h2
    have hLap : laplace (fun t : ℝ => (normalizedThetaError t : ℂ)) s
        = (∫ t : ℝ in Set.Ioi 0,
          Complex.exp (-s * (t : ℂ)) •
            (normalizedThetaError t : ℂ)) :=
      rfl
    rw [hLap, hIntEq, hThetaInt, hEqInt]
    have hRw : (∫ t : ℝ in Set.Ioi 0,
        Complex.exp ((-s) * (t : ℂ))) = 1 / s := by
      have hField : (-1 : ℂ) / (-s) = 1 / s := by
        field_simp
      have hRw0 : (∫ t : ℝ in Set.Ioi 0,
          Complex.exp ((-s) * (t : ℂ))) = (-1 : ℂ) / (-s) := by
        simpa using hConstBase
      rw [hRw0, hField]
    rw [hRw, hBridge]
  have hFinal : laplace (fun t : ℝ => (normalizedThetaError t : ℂ)) s
      = normalizedThetaErrorContinuation s := by
    rw [hVal]
    simp only [normalizedThetaErrorContinuation]
    rw [hAgree, hBridge]
    field_simp
    ring
  exact ⟨hConv, hFinal⟩

end Chebyshev
