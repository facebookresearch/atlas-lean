/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Crypto.Privacy.Gaussian
public import CSLibExt.Crypto.Privacy.Transfer
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Differential privacy: wanted results

Advanced composition of differential privacy, whose proof is deferred. The definitions are
those of `CSLibExt.Crypto.Privacy.Basic` (`DifferentiallyPrivate`, `hammingAdj`), where
basic composition (`differentiallyPrivate_pi`, Dwork and Roth, Theorem 3.16) is proved.

* `differentiallyPrivate_pi_advanced`: advanced composition for a symmetric neighbouring relation
  (Dwork and Roth, *The Algorithmic Foundations of Differential Privacy*, 2014, Theorem 3.20,
  stated here for `k` mechanisms run independently; the theorem allows them to be chosen
  adaptively).
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

end Cslib.Crypto.Privacy
