/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import MathlibExt.Analysis.Wavelet.Scattering1D

/-!
# Energy conservation and deformation stability of the scattering transform (wanted)

Two main theorems of S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012),
1331–1398 (arXiv:1101.2286, Section 2), stated in dimension `d = 1` for real-valued signals with
the definitions of `MathlibExt.Analysis.Wavelet.Scattering1D`:

* Theorem 2.6: for an admissible wavelet the windowed scattering transform preserves the
  `L²` norm, `‖S_J[P_J] f‖ = ‖f‖`. The structural half of the proof (norm preservation is
  equivalent to the decay of the energy propagated to depth `m`) is proved abstractly in
  `MathlibExt.Analysis.Wavelet.ScatteringCascade.tsum_enorm_sq_eq_iff_tendsto`; the analytic
  half (the decay, through Lemmas 2.7–2.8) is deferred.
* Theorem 2.12: the windowed scattering transform is Lipschitz continuous to the action
  `L_τ f(x) = f(x - τ(x))` of `C²` deformations with `‖τ'‖∞ ≤ 1/2`.

Squared `L²` norms are written as lower Lebesgue integrals `∫⁻ ‖·‖ₑ²` so that sums over all
paths need no summability side conditions. Specialising the paper's `ℝ^d` statements to
`d = 1` (and the rotation group to `{1, -1}`) is the only restriction.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace MathlibExt.Analysis.Wavelet.ScatteringWanted

open MathlibExt.Analysis.Wavelet.Scattering1D MathlibExt.Analysis.Wavelet.ScatteringCascade

/-- **Energy conservation of the windowed scattering transform** (S. Mallat, *Group invariant
scattering*, Comm. Pure Appl. Math. 65 (2012), Theorem 2.6, equation (32), in dimension `d = 1`
for real-valued signals). If `ψ` is an admissible scattering wavelet with low-pass `φ`
(conditions (9), (29), (30)), then for every `J ∈ ℤ` and every real-valued `f ∈ L²(ℝ)`,
`∑_{p ∈ P_J} ‖S_J[p] f‖² = ‖f‖²`, where `P_J` is the set of all finite paths of frequency
indices `j > -J`. -/
theorem_wanted tsum_lintegral_windowedScattering_eq
    {ψ φ : ℝ → ℂ} (hψ : IsAdmissible ψ φ) (J : ℤ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hreal : ∀ x, (f x).im = 0) :
    ∑' p : (Σ m, Fin m → {j : ℤ // -J < j}),
        ∫⁻ x, ‖windowedScattering ψ φ J p.2 f x‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2

/-- **Lipschitz continuity of the windowed scattering transform to deformations** (S. Mallat,
*Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), Theorem 2.12, equations
(49)–(50), in dimension `d = 1` for real-valued signals). Let `ψ` be an admissible scattering
wavelet and `J ∈ ℤ`. There is `C` such that for every real-valued `f ∈ L²(ℝ)` with
`‖U[P_J] f‖₁ = ∑_m (∑_{|p| = m} ‖U[p] f‖²)^{1/2} < ∞` and every `C²` displacement `τ` with
`‖τ'‖∞ ≤ 1/2`,
`‖S_J[P_J] L_τ f - S_J[P_J] f‖ ≤ C ‖U[P_J] f‖₁ K(τ)`, where `L_τ f(x) = f(x - τ(x))` and
`K(τ) = 2^{-J} ‖τ‖∞ + ‖τ'‖∞ max(log (‖Δτ‖∞ / ‖τ'‖∞), 1) + ‖τ''‖∞`, with
`‖Δτ‖∞ = sup_{x, u} |τ(x) - τ(u)|`.

The bound is vacuous when `τ` or `τ''` is unbounded (then `K(τ) = ∞` in the paper); the
statement assumes both bounded so that the suprema are finite. The paper's constant is in fact
uniform in `J` (its proof uses Lemmas 2.11 and 2.14, whose constants do not depend on `J`); the
statement records the weaker form with `C` chosen after `J`. -/
theorem_wanted windowedScattering_lipschitz_deformation
    {ψ φ : ℝ → ℂ} (hψ : IsAdmissible ψ φ) (J : ℤ) :
    ∃ C : ℝ≥0, ∀ f : ℝ → ℂ, MemLp f 2 volume → (∀ x, (f x).im = 0) →
      (∑' m : ℕ, (∑' p : Fin m → {j : ℤ // -J < j},
          ∫⁻ x, ‖propagator (fun j : {j : ℤ // -J < j} => modulusLayer ψ j) p f x‖ₑ ^ 2) ^
            (1 / 2 : ℝ)) < ∞ →
      ∀ τ : ℝ → ℝ, ContDiff ℝ 2 τ → (∀ x, |deriv τ x| ≤ 1 / 2) →
        (∃ M, ∀ x, |τ x| ≤ M) → (∃ M, ∀ x, |iteratedDeriv 2 τ x| ≤ M) →
        (∑' p : (Σ m, Fin m → {j : ℤ // -J < j}),
            ∫⁻ x, ‖windowedScattering ψ φ J p.2 (fun y => f (y - τ y)) x -
              windowedScattering ψ φ J p.2 f x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
          C * (∑' m : ℕ, (∑' p : Fin m → {j : ℤ // -J < j},
              ∫⁻ x, ‖propagator (fun j : {j : ℤ // -J < j} => modulusLayer ψ j) p f x‖ₑ ^ 2) ^
                (1 / 2 : ℝ)) *
            ENNReal.ofReal ((2 : ℝ) ^ (-J) * (⨆ x, |τ x|) +
              (⨆ x, |deriv τ x|) *
                max (Real.log ((⨆ xu : ℝ × ℝ, |τ xu.1 - τ xu.2|) / ⨆ x, |deriv τ x|)) 1 +
              ⨆ x, |iteratedDeriv 2 τ x|)

end MathlibExt.Analysis.Wavelet.ScatteringWanted
