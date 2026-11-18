/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GameTheory.BlackwellApproachabilityWanted

@[expose] public section

/-! # Asymptotic calibration of randomised forecasts

A forecaster announces each day a probability of rain from the grid `0, 1/k, …, 1`; it is
calibrated if, among the days with forecast `i / k`, it rained on a fraction close to `i / k`.
No deterministic forecaster is calibrated against every sequence (Oakes 1985, Dawid 1985), but a
randomised one can be, against an adaptive Nature that sees the past but not the current
randomisation (Foster and Vohra 1998). Foster and Vohra's forecast chooses, each day, a
distribution `μ` on the grid satisfying the *conservation condition* (2) of §5, which is the
regret-invariance condition (3.1) of Hart and Mas-Colell 2000
(`CorrelatedEquilibrium.IsRegretInvariant`) for the regrets of replacing one forecast by another.

## References

* D. P. Foster and R. V. Vohra, "Asymptotic calibration", Biometrika 85(2) (1998), 379–390:
  §2 (calibration score), §3 (Rules 1–3, Definition of ε-calibration), Theorem 1 (§5).
-/

namespace MathlibExt.GameTheory.CalibrationWanted

open MeasureTheory Filter Topology Finset
open MathlibExt.GameTheory.BlackwellApproachabilityWanted (historySigma)

/-- The **calibration score** of binary forecasts (Foster and Vohra 1998, §2). The forecasts
`f s ∈ {0, 1/k, …, 1}` (the index `i` standing for `i / k`) are made for the outcomes `x s` of
`t` rounds; with `n(i)` the number of rounds forecast `i / k` and `ρ(i)` the fraction of those
rounds with outcome `1`, `C_t = ∑ᵢ (ρ(i) − i / k)² n(i) / t`. -/
noncomputable def calibrationScore {k t : ℕ} (f : Fin t → Fin (k + 1)) (x : Fin t → Bool) :
    ℝ :=
  ∑ i : Fin (k + 1),
    ((#{s | f s = i ∧ x s = true} : ℝ) / #{s | f s = i} - (i : ℝ) / k) ^ 2 *
      #{s | f s = i} / t

/-- **Asymptotic calibration** (Foster and Vohra 1998, Theorem 1, with §3's definition of
`ε`-calibration against an adaptive adversary). For every `ε > 0` there are a grid size `k` and a
randomised forecasting rule `μ`, choosing a distribution on the forecasts `0, 1/k, …, 1` from the
history, such that against every Nature, who chooses each outcome knowing the past but not the
current randomisation, the calibration score after `t` rounds is below `ε` with probability
greater than `1 − ε` for all large `t`. This is weaker than Foster and Vohra's `ε`-calibration,
`lim_t Pr(C_t < ε) > 1 − ε`, which implies it; it does not require the limit to exist. -/
theorem_wanted exists_calibrated_forecast {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 0 < k ∧
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
          calibrationScore (fun s : Fin t => (Z s ω).1) (fun s => (Z s ω).2) < ε}

end MathlibExt.GameTheory.CalibrationWanted
