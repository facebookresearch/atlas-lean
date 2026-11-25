/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Fourier.BooleanCubeFKN
public import MathlibExt.Analysis.Fourier.BooleanCubeNoiseStability
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Structure theorems for Boolean functions

Majority Is Stablest is stated for a bounded function on the uniform cube `{-1, 1}ⁿ` in
terms of its coordinate influences `boolInfluence` and noise stability `boolNoiseStab`.
The Friedgut–Kalai–Naor theorem is available in `MathlibExt.Analysis.Fourier.BooleanCubeFKN`.

## References

* E. Mossel, R. O'Donnell and K. Oleszkiewicz, *Noise stability of functions with low
  influences: invariance and optimality*, Ann. of Math. 171 (2010), 295-341
  (arXiv:math/0503503).
* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Sections 2.5, 5.2, 5.4, 9.1 and Chapter 11.

Friedgut's Junta Theorem and the Level-1 Inequality, stated in the same terms, are proved in
`MathlibExt.Analysis.Fourier.BooleanCubeFriedgut` and
`MathlibExt.Probability.Hypercontractivity.LevelInequalities`.
-/

@[expose] public section

namespace BooleanCube

open scoped BigOperators

/-- **Majority Is Stablest.** Fix `ρ ∈ (0, 1)`. For every `ε > 0` there is `τ > 0` such that
every `f : BoolCube n → ℝ` with values in `[-1, 1]`, `𝔼[f] = 0` and `Inf_i[f] ≤ τ` for all `i`
satisfies `Stab_ρ[f] ≤ (2/π) arcsin ρ + ε` (E. Mossel, R. O'Donnell and K. Oleszkiewicz, Ann. of
Math. 171 (2010); R. O'Donnell, *Analysis of Boolean Functions*, 2014, Majority Is Stablest
Theorem, Section 5.2, where the error is written `o_τ(1)`; proved in Chapter 11). The bound is
the limit of `Stab_ρ[Maj_n]` over odd `n`, `(2/π) arcsin ρ = 1 - (2/π) arccos ρ`
(Theorem 2.45). -/
theorem_wanted majority_is_stablest {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (n : ℕ) (f : BoolCube n → ℝ), (∀ x, |f x| ≤ 1) →
      𝔼 x, f x = 0 → (∀ i, boolInfluence f i ≤ τ) →
        boolNoiseStab ρ f ≤ 2 / Real.pi * Real.arcsin ρ + ε

end BooleanCube
