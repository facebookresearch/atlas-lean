/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Fourier.BooleanCubeBLR
public import MathlibExt.Analysis.Fourier.BooleanCubeNoiseStability
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Structure theorems for Boolean functions

Two theorems of the analysis of Boolean functions, stated for `f : BoolCube n → ℝ` on the
uniform cube `{-1, 1}ⁿ` with the definitions of `MathlibExt.Analysis.Fourier`: the Fourier
coefficients `boolFourierCoeff`, influences `boolInfluence`, total influence
`boolTotalInfluence`, noise stability `boolNoiseStab` and relative Hamming distance `boolDist`.
A Boolean function is a `±1`-valued `f`; `W¹[f] = ∑_{|S| = 1} f̂(S)²` is its degree-1 weight.

## Main statements

* `BooleanCube.fkn_theorem`: Friedgut–Kalai–Naor.
* `BooleanCube.majority_is_stablest`: Majority Is Stablest (Mossel–O'Donnell–Oleszkiewicz).

## References

* E. Friedgut, G. Kalai and A. Naor, *Boolean functions whose Fourier transform is concentrated
  on the first two levels*, Adv. in Appl. Math. 29 (2002), 427-437.
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

/-- **Friedgut–Kalai–Naor (FKN) Theorem.** There is a universal constant `C` such that for every
`n ≥ 1` and every `f : BoolCube n → ℝ` with values `±1`, if `W¹[f] ≥ 1 - δ` then `f` is
`Cδ`-close to a dictator `χ_i` or a negated dictator `-χ_i` for some coordinate `i` (E. Friedgut,
G. Kalai and A. Naor, 2002; R. O'Donnell, *Analysis of Boolean Functions*, 2014, FKN Theorem,
stated in Section 2.5 with closeness `O(δ)` and proved in Section 9.1). The hypothesis `n ≥ 1`
is implicit in the source: for `n = 0` there is no coordinate to name. -/
theorem_wanted fkn_theorem :
    ∃ C : ℝ, ∀ (n : ℕ), 0 < n → ∀ f : BoolCube n → ℝ, (∀ x, f x = 1 ∨ f x = -1) →
      ∀ δ : ℝ, 1 - δ ≤ ∑ S with S.card = 1, boolFourierCoeff n f S ^ 2 →
        ∃ i : Fin n, boolDist f (fun x => cubeVal (x i)) ≤ C * δ ∨
          boolDist f (fun x => -cubeVal (x i)) ≤ C * δ

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
