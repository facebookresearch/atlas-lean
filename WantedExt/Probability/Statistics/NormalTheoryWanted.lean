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

* the Student `t` law of `Z / √(V / k)` for independent `Z ~ N(0, 1)`, `V ~ χ²_k`;
* the Snedecor `F` law of `(V₁ / d₁) / (V₂ / d₂)` for independent `Vᵢ ~ χ²_{dᵢ}`;
* the one-sample `t` statistic `√n (X̄ - μ) / S ~ t_{n-1}` for an i.i.d. normal sample;
* Hoeffding's central limit theorem `√n (U - θ) ⇒ N(0, m² σ₁²)` for U-statistics.

The independence inputs (`X̄ ⊥ S²`, joint independence in Cochran's theorem) are proved in
`MathlibExt/Probability/Distributions/CochranIndependence.lean`; the `χ²` laws of the quadratic
forms are the single-projection form of Cochran's theorem.

## References

* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002), Theorem 5.3.1
  and Definitions 5.3.4, 5.3.6.
* W. Hoeffding, *A class of statistics with asymptotically normal distribution*, Ann. Math.
  Statist. 19 (1948), 293–325, §7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace ProbabilityTheory.NormalTheoryWanted

/-- **Student's `t` law** (Casella–Berger, Definition 5.3.4): for independent `Z ~ N(0, 1)` and
`V ~ χ²_k` with `k ≥ 1`, `Z / √(V / k)` has density
`Γ((k + 1)/2) / (√(k π) Γ(k/2)) · (1 + t²/k)^{-(k+1)/2}`. -/
public theorem_wanted map_div_sqrt_chiSquare_eq_studentT {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ} (hk : 0 < k) {Z V : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) P) (hV : HasLaw V (chiSquareMeasure k) P)
    (hZV : IndepFun Z V P) :
    P.map (fun ω => Z ω / √(V ω / k)) =
      volume.withDensity fun t => ENNReal.ofReal
        (Gamma ((k + 1) / 2) / (√(k * π) * Gamma (k / 2)) *
          (1 + t ^ 2 / k) ^ (-((k : ℝ) + 1) / 2))

/-- **Snedecor's `F` law** (Casella–Berger, Definition 5.3.6): for independent `V₁ ~ χ²_{d₁}` and
`V₂ ~ χ²_{d₂}` with `d₁, d₂ ≥ 1`, `(V₁ / d₁) / (V₂ / d₂)` has density
`Γ((d₁ + d₂)/2) / (Γ(d₁/2) Γ(d₂/2)) · (d₁/d₂)^{d₁/2} x^{d₁/2 - 1} (1 + d₁ x / d₂)^{-(d₁+d₂)/2}`
on `x > 0`. -/
public theorem_wanted map_div_chiSquare_eq_snedecorF {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    {V₁ V₂ : Ω → ℝ} (hV₁ : HasLaw V₁ (chiSquareMeasure d₁) P)
    (hV₂ : HasLaw V₂ (chiSquareMeasure d₂) P) (hV : IndepFun V₁ V₂ P) :
    P.map (fun ω => (V₁ ω / d₁) / (V₂ ω / d₂)) =
      volume.withDensity fun x => ENNReal.ofReal (if 0 < x then
        Gamma ((d₁ + d₂) / 2) / (Gamma (d₁ / 2) * Gamma (d₂ / 2)) *
          ((d₁ : ℝ) / d₂) ^ ((d₁ : ℝ) / 2) * x ^ ((d₁ : ℝ) / 2 - 1) *
            (1 + d₁ * x / d₂) ^ (-((d₁ : ℝ) + d₂) / 2)
        else 0)

/-- **One-sample `t` statistic**: for an i.i.d. sample `X₁, …, Xₙ ~ N(μ, v)` with `n ≥ 2` and
`v > 0`, `√n (X̄ - μ) / S` with `S² = ∑ (Xᵢ - X̄)² / (n - 1)` has the Student `t` law with
`n - 1` degrees of freedom. -/
public theorem_wanted map_tStatistic_pi_gaussianReal {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal}
    (hv : v ≠ 0) :
    (Measure.pi fun _ : Fin n => gaussianReal μ v).map
        (fun x : Fin n → ℝ => √n * ((∑ i, x i) / n - μ) /
          √((∑ i, (x i - (∑ j, x j) / n) ^ 2) / ((n : ℝ) - 1))) =
      volume.withDensity fun t => ENNReal.ofReal
        (Gamma (((n - 1 : ℕ) + 1) / 2) / (√((n - 1 : ℕ) * π) * Gamma ((n - 1 : ℕ) / 2)) *
          (1 + t ^ 2 / (n - 1 : ℕ)) ^ (-(((n - 1 : ℕ) : ℝ) + 1) / 2))

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
