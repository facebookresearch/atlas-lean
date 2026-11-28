/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.RenyiDivergence

/-!
# Rényi differential privacy

For real orders `α > 1`, a probability-valued mechanism `M : X → Measure Ω` is `(α, ε)`-Rényi
differentially private for a neighbouring relation `Adj` when `D_α(M x ‖ M y) ≤ ε` for all
neighbours `x, y` (Mironov, *Rényi differential privacy*, 2017, Definition 4). The Lean
predicate records the inequality, without requiring that the output measures be probabilities.

`gaussianMechanism_renyiDifferentiallyPrivate`: adding `N(0, v)` noise with `v > 0` to a
real-valued query whose values on neighbours differ by at most `Δ` gives
`(α, α Δ² / (2 v))`-Rényi differential privacy for every `α > 1` (Mironov, Corollary 3 at
orders `α > 1`, the case `Δ = 1`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.InformationTheory.RenyiDivergence
open scoped NNReal

namespace Cslib.Crypto.Privacy

variable {X Ω : Type*} [MeasurableSpace Ω]

/-- **Rényi differential privacy.** For probability-valued outputs and real orders `α > 1`,
Mironov's Definition 4 (*Rényi differential privacy*, 2017) requires
`D_α(M x ‖ M y) ≤ ε` whenever `Adj x y`. Here `D_α(μ ‖ ν)` is `renyiDiv μ ν α`. The
predicate records that inequality for arbitrary measures; it does not enforce the
probability-law assumption.

Mironov also admits `α = 1`, where `D₁` is the Kullback–Leibler divergence, and `α = ∞`, where
`(∞, ε)`-Rényi differential privacy is `ε`-differential privacy. Neither is captured here. At
real orders `α ≤ 1`, `renyiDiv` is `⊤`, so the inequality for a real budget holds only when no
two inputs are neighbours. -/
def RenyiDifferentiallyPrivate (Adj : X → X → Prop) (M : X → Measure Ω) (α ε : ℝ) : Prop :=
  ∀ ⦃x y : X⦄, Adj x y → renyiDiv (M x) (M y) α ≤ ε

/-- **Rényi differential privacy of the Gaussian mechanism.** Let `f : X → ℝ` satisfy
`|f x - f y| ≤ Δ` whenever `Adj x y`, and let `v ≠ 0` be a variance. The Gaussian mechanism,
which releases `f x + Z` with `Z ∼ N(0, v)` and so has output law `gaussianReal (f x) v`, is
`(α, α Δ² / (2 v))`-Rényi differentially private for every `α > 1`. With `Δ = 1` and `v = σ²`
this is `(α, α / (2 σ²))`-Rényi differential privacy (Mironov, *Rényi differential privacy*,
2017, Corollary 3 at orders `α > 1`). -/
theorem gaussianMechanism_renyiDifferentiallyPrivate {Adj : X → X → Prop} {f : X → ℝ} {Δ : ℝ}
    (hf : ∀ ⦃x y⦄, Adj x y → |f x - f y| ≤ Δ) {v : ℝ≥0} (hv : v ≠ 0) {α : ℝ} (hα : 1 < α) :
    RenyiDifferentiallyPrivate Adj (fun x ↦ gaussianReal (f x) v) α (α * Δ ^ 2 / (2 * v)) :=
  fun _ _ hxy ↦ renyiDiv_gaussianReal_le _ _ hv hα (hf hxy)

end Cslib.Crypto.Privacy
