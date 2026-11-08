/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.ConvexSubGaussianComparison

/-!
# Sharp one-dimensional convex sub-Gaussian comparison: literature requests

All six results below are private unproved data, not proofs. The implemented probability
model and characteristic APIs are upstream. The numerical approximations in Davis–Power
Remark 2 are not asserted here, and the solved one-dimensional problem is not an open target.
-/

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.ConvexSubGaussianComparison

-- The Davis–Power equation data (Davis–Power 2026, equations (3)-(6)), kept with its
-- owning literature requests instead of the reusable `MathlibExt` library.
namespace MathlibExt.Probability.ConvexSubGaussianComparisonWantedDavis

open Set

/-- The standard Gaussian upper tail uses Mathlib's actual normalized Gaussian density. -/
noncomputable def standardNormalTail (x : ℝ) : ℝ :=
  ∫ t in Ici x, gaussianPDFReal 0 1 t

/-- The transition threshold `sqrt(2 log 2)`. -/
noncomputable def davisPowerT0 : ℝ :=
  Real.sqrt (2 * Real.log 2)

/-- Equation (3): the integral of the capped tail envelope. -/
noncomputable def davisPowerA : ℝ :=
  ∫ t in Ici (0 : ℝ), gaussianTailEnvelope t

/-- Equation (3): half the envelope integral. -/
noncomputable def davisPowerB : ℝ :=
  davisPowerA / 2

/-- Equation (4), used only above the transition threshold in the valid solution system. -/
noncomputable def davisPowerH (x : ℝ) : ℝ :=
  2 * x * Real.exp (-x ^ 2 / 2) + 2 * ∫ t in Ici x, Real.exp (-t ^ 2 / 2)

/-- The four real parameters in the exact Davis–Power equation system. -/
@[ext] structure DavisPowerSolution where
  a : ℝ
  p0 : ℝ
  z : ℝ
  c0 : ℝ

/-- Equations (3)–(6), with the domains that select the solution. -/
noncomputable def DavisPowerSolution.IsValid (q : DavisPowerSolution) : Prop :=
  davisPowerT0 < q.a ∧
    davisPowerH q.a = davisPowerB ∧
    q.p0 = 2 * Real.exp (-q.a ^ 2 / 2) ∧
    0 < q.p0 ∧ q.p0 < 1 ∧
    standardNormalTail q.z = q.p0 ∧
    q.c0 = davisPowerB / gaussianPDFReal 0 1 q.z

/-- The `c0` coordinates of solutions to the actual equation system. -/
noncomputable def davisPowerC0Values : Set ℝ :=
  {c | ∃ q : DavisPowerSolution, q.IsValid ∧ q.c0 = c}

/-- The exact parameter, defined from the equation system rather than numerical data. -/
noncomputable def davisPowerC0 : ℝ :=
  sInf davisPowerC0Values

theorem davisPowerC0Values_eq_singleton {q : DavisPowerSolution}
    (hq : q.IsValid) (hunique : ∀ r : DavisPowerSolution, r.IsValid → r = q) :
    davisPowerC0Values = {q.c0} := by
  ext c
  constructor
  · rintro ⟨r, hr, hrc⟩
    simpa [hunique r hr] using hrc.symm
  · intro hc
    exact ⟨q, hq, (mem_singleton_iff.mp hc).symm⟩

theorem davisPowerC0_eq_of_unique_solution {q : DavisPowerSolution}
    (hq : q.IsValid) (hunique : ∀ r : DavisPowerSolution, r.IsValid → r = q) :
    davisPowerC0 = q.c0 := by
  rw [davisPowerC0, davisPowerC0Values_eq_singleton hq hunique, csInf_singleton]

end MathlibExt.Probability.ConvexSubGaussianComparisonWantedDavis

open MathlibExt.Probability.ConvexSubGaussianComparisonWantedDavis

namespace MathlibExt.Probability.ConvexSubGaussianComparisonWanted

/-- Source: Davis–Power (2026), equations (3)–(6), existence and uniqueness. -/
theorem_wanted davisPowerSystem_existsUnique :
    ∃! q : DavisPowerSolution, q.IsValid

/-- Source: van Handel (2025), historical one-dimensional finiteness consequence. -/
theorem_wanted historicalFinitenessUpperBound :
    comparisonConstant ≠ ⊤

/-- Source: Davis–Power (2026), Theorem 1, the exact `c0^2` comparator upper bound. -/
theorem_wanted davisPowerSharpUpper :
    IsAdmissibleConstant (ENNReal.ofReal (davisPowerC0 ^ 2))

/-- Source: Davis–Power (2026), Theorem 1, sharpness for every admissible variance factor. -/
theorem_wanted davisPowerSharpLower (C : ENNReal) (hC : IsAdmissibleConstant C) :
    ENNReal.ofReal (davisPowerC0 ^ 2) ≤ C

/-- Source: Davis–Power (2026), the exact solved one-dimensional catalogue constant. -/
theorem_wanted comparisonConstant_eq_davisPowerC0_sq :
    comparisonConstant = ENNReal.ofReal (davisPowerC0 ^ 2)

/-- Source: Davis–Power (2026), the tail-saturating extremizer and smaller-factor sharpness. -/
theorem_wanted davisPowerExtremalAttainment :
    ∃ (Ω : Type) (m : MeasurableSpace Ω)
      (μ : @Measure Ω m) (hμ : @IsProbabilityMeasure Ω m μ) (X : Ω → ℝ),
      @IsOneSubGaussianTail Ω m μ hμ X ∧ SaturatesGaussianTail μ X ∧
        ∀ c : ℝ, 0 < c → c < davisPowerC0 →
          ¬ConvexDominated μ X (gaussianReal 0 1) (fun g : ℝ => c * g)

end MathlibExt.Probability.ConvexSubGaussianComparisonWanted
