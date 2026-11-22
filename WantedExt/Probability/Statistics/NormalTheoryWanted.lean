/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.ChiSquare
public import MathlibExt.Probability.Statistics.UStatistic
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Batteries.Util.ProofWanted

/-!
# Normal-theory sampling laws and the U-statistic central limit theorem (wanted)

Statements requested but not yet proved:

* Hoeffding's central limit theorem `√n (U - θ) ⇒ N(0, m² σ₁²)` for U-statistics.

The independence inputs (`X̄ ⊥ S²`, joint independence in Cochran's theorem) are proved in
`MathlibExt/Probability/Distributions/CochranIndependence.lean`; the `χ²` laws of the quadratic
forms are the single-projection form of Cochran's theorem.
The Student `t` law of `Z / √(V / k)` is proved as
`ProbabilityTheory.map_div_sqrt_chiSquare_eq_studentT` in
`MathlibExt/Probability/Distributions/StudentT.lean`.
The Snedecor `F` law of `(V₁ / d₁) / (V₂ / d₂)` for independent `Vᵢ ~ χ²_{dᵢ}` is proved as
`ProbabilityTheory.map_div_chiSquare_eq_snedecorF` in
`MathlibExt/Probability/Distributions/SnedecorF.lean`.
The one-sample `t` law `√n (X̄ - μ) / S ~ t_{n-1}` is proved as
`ProbabilityTheory.map_tStatistic_pi_gaussianReal` in
`MathlibExt/Probability/Statistics/LinearModel/Inference.lean`.

## References

* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002), Theorem 5.3.1
  and Definition 5.3.4.
* W. Hoeffding, *A class of statistics with asymptotically normal distribution*, Ann. Math.
  Statist. 19 (1948), 293–325, §7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace ProbabilityTheory.NormalTheoryWanted

/-- **Hoeffding's central limit theorem** (1948, §7): for an i.i.d. sample from `μ` and a
symmetric square-integrable kernel `h` of degree `m`, `√n (U_n - θ)` converges in distribution
to `N(0, m² σ₁²)`, where `θ = E h` and `σ₁² = Var h₁`. -/
public theorem_wanted tendstoInDistribution_uStatistic {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {m : ℕ} {h : (Fin m → α) → ℝ}
    (hsymm : ∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y)
    (hh : MemLp h 2 (Measure.pi fun _ => μ)) :
    TendstoInDistribution
      (fun (n : ℕ) (x : Fin n → α) =>
        √n * (uStatistic h x - ∫ y, h y ∂(Measure.pi fun _ => μ)))
      Filter.atTop id (fun n => Measure.pi fun _ : Fin n => μ)
      (gaussianReal 0
        ((m : ℝ) ^ 2 * Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ]).toNNReal)

end ProbabilityTheory.NormalTheoryWanted
