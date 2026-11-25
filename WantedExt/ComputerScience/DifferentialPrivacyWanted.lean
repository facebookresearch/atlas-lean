/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Crypto.Privacy.Gaussian
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Differential privacy: wanted results

Central results of differential privacy whose proofs are deferred. The definitions are those of
`CSLibExt.Crypto.Privacy.Basic` (`DifferentiallyPrivate`, `hammingAdj`), where basic composition
(`differentiallyPrivate_pi`, Dwork and Roth, Theorem 3.16) is proved.

* `differentiallyPrivate_pi_advanced`: advanced composition for a symmetric neighbouring relation
  (Dwork and Roth, *The Algorithmic Foundations of Differential Privacy*, 2014, Theorem 3.20,
  stated here for `k` mechanisms run independently; the theorem allows them to be chosen
  adaptively).
* `differentiallyPrivate_transfer`: differential privacy implies generalization for adaptively
  chosen statistical queries (Dwork, Feldman, Hardt, Pitassi, Reingold and Roth,
  arXiv:1411.2664v3, identical in v2, Theorem 9; preliminary version in STOC 2015).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Cslib.Crypto.Privacy

variable {X : Type*} {Adj : X → X → Prop}

/-- **Advanced composition.** Let the neighbouring relation `Adj` be symmetric (`Std.Symm Adj`), as
for Dwork and Roth's databases at `ℓ₁` distance at most one, and let `ε, δ ≥ 0` and `δ' > 0`. If
each of `k` mechanisms `M i : X → Measure (Ω i)` with values in probability measures is
`(ε, δ)`-differentially private, then running them independently is
`(ε', k δ + δ')`-differentially private with `ε' = √(2 k ln (1 / δ')) ε + k ε (e^ε - 1)` (Dwork
and Roth, *The Algorithmic Foundations of Differential Privacy*, 2014, Theorem 3.20; there the `k`
mechanisms may be chosen adaptively by an adversary, and independent mechanisms are a special
case). Symmetry is needed, since the source bounds the privacy loss in both directions. For a
one-sided relation the statement fails: with `k = 100`, `ε = 0.1`, `δ = 0` and `δ' = 1/2`,
mechanisms that send `x` to `δ_true` and its one-sided neighbour `y` to a law with mass `e^{-ε}` on
`true` are each `ε`-private, but the all-true event would need `1 ≤ 0.5004…`. -/
public theorem_wanted differentiallyPrivate_pi_advanced {k : ℕ} {Ω : Fin k → Type*}
    [∀ i, MeasurableSpace (Ω i)] {M : ∀ i, X → Measure (Ω i)}
    [∀ i x, IsProbabilityMeasure (M i x)] [Std.Symm Adj] {ε δ' : ℝ} {δ : ℝ≥0∞}
    (hε : 0 ≤ ε) (hδ' : 0 < δ') (h : ∀ i, DifferentiallyPrivate Adj (M i) ε δ) :
    DifferentiallyPrivate Adj (fun x ↦ Measure.pi fun i ↦ M i x)
      (Real.sqrt (2 * k * Real.log (1 / δ')) * ε + k * ε * (Real.exp ε - 1))
      (k * δ + ENNReal.ofReal δ')

/-- **Transfer theorem for adaptive data analysis.** Let `P` be a probability distribution on
`𝒳`, let the data set `S` consist of `n` independent samples from `P`, and let the analyst's
algorithm `A`, a Markov kernel from data sets to a space `Q` of queries `φ q : 𝒳 → [0, 1]`, be
`ε`-differentially private for data sets differing in one element. If `β, τ > 0`,
`n ≥ 12 ln (4 / β) / τ ^ 2` and `0 ≤ ε ≤ τ / 2`, then the selected query `q ~ A(S)` satisfies
`|E_P[φ q] - (1/n) ∑ i, φ q (S i)| ≤ τ` except with probability at most `β`, over both `S` and
the randomness of `A` (Dwork, Feldman, Hardt, Pitassi, Reingold and Roth, *Preserving
Statistical Validity in Adaptive Data Analysis*, arXiv:1411.2664v3, identical in v2, Theorem 9;
preliminary version in STOC 2015). Taking the queries from a measurable space `Q`, with `φ`
jointly measurable, is this formalization's choice; the source lets the algorithm output any
function from `𝒳` to `[0, 1]`. -/
public theorem_wanted differentiallyPrivate_transfer {𝒳 Q : Type*} [MeasurableSpace 𝒳]
    [MeasurableSpace Q] {P : Measure 𝒳} [IsProbabilityMeasure P] {n : ℕ}
    (A : Kernel (Fin n → 𝒳) Q) [IsMarkovKernel A] (φ : Q → 𝒳 → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (hφ01 : ∀ q z, φ q z ∈ Set.Icc (0 : ℝ) 1)
    {ε β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ) (hn : 12 * Real.log (4 / β) / τ ^ 2 ≤ n)
    (hε₀ : 0 ≤ ε) (hε : ε ≤ τ / 2) (hA : DifferentiallyPrivate hammingAdj (fun S ↦ A S) ε 0) :
    ((Measure.pi fun _ : Fin n ↦ P) ⊗ₘ A)
        {p | τ < |∫ z, φ p.2 z ∂P - (1 / n : ℝ) * ∑ i, φ p.2 (p.1 i)|} ≤ ENNReal.ofReal β

end Cslib.Crypto.Privacy
