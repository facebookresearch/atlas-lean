/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nontrivial relative commutant of B(H) in its ultrapower forces flatness (AimPL Problem 1.4)

AimPL, Set theory and C* algebras, Problem 1.4: is a nonprincipal ultrafilter `U` on `ℕ` with
`B(H)' ∩ B(H)^U ≠ ℂ I` flat? The list adds that the reverse implication is true
(Farah-Phillips-Steprāns). Chetcuti and Zamora-Aviles proved the implication, so the relative
commutant is nontrivial exactly for the flat ultrafilters.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

namespace MathlibExt.Analysis.FlatUltrafilterRelativeCommutantAIMFunctionalAnalysisProblem20Wanted

/-!
Source: AimPL: Set theory and C* algebras, Section 1 (Ultrapowers), Problem 1.4,
http://aimpl.org/settheorycstar/1/. UnsolvedMath record UM-20001461
(`AIM-FUNCTIONAL_ANALYSIS-0020`), dataset ulamai/UnsolvedMath v1.8.0.

`H = ℓ²(ℕ)`, a separable infinite-dimensional Hilbert space. The norm ultrapower `B(H)^U` is the
algebra of bounded sequences of operators modulo those with `‖xₙ‖ → 0` along `U`, and `B(H)` sits in
it as the constant sequences. A class `[xₙ]` lies in the relative commutant `B(H)' ∩ B(H)^U` exactly
when `‖xₙ a - a xₙ‖ → 0` along `U` for every operator `a`, and it equals `c · 1` exactly when
`‖xₙ - c · 1‖ → 0` along `U`; the hypothesis is stated through representatives in this way.
Nonprincipal means `U ≤ cofinite`. Flatness is the list's definition (`hₙ` nonincreasing with values
in `[0, 1]`, `hₙ 0 = 1`, `hₙ j → 0`, and `sup_j |hₙ j - hₙ (f j)| → 0` along `U` for every strictly
increasing `f`, the paper's `ℕ↑`), which is Farah-Phillips-Steprāns Definition 3.2 and
Chetcuti-Zamora-Aviles Proposition 10 with `ℕ` indexed from `0`.
-/

open Filter Topology

/-- An ultrafilter `U` on `ℕ` is *flat* (Farah-Phillips-Steprāns; the definition of AimPL Problem
1.4): there are nonincreasing functions `hₙ : ℕ → [0, 1]` with `hₙ 0 = 1` and `hₙ j → 0` as
`j → ∞`, such that for every strictly increasing `f : ℕ → ℕ`, `sup_j |hₙ j - hₙ (f j)| → 0` as
`n → U`. -/
def IsFlat (U : Ultrafilter ℕ) : Prop :=
  ∃ h : ℕ → ℕ → ℝ, (∀ n j, h n j ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ n, Antitone (h n)) ∧
    (∀ n, h n 0 = 1) ∧ (∀ n, Tendsto (h n) atTop (𝓝 0)) ∧
    ∀ f : ℕ → ℕ, StrictMono f →
      Tendsto (fun n => ⨆ j, |h n j - h n (f j)|) (U : Filter ℕ) (𝓝 0)

/-- AimPL Problem 1.4, answered yes: let `H = ℓ²(ℕ)`. If `U` is a nonprincipal ultrafilter on `ℕ`
and the relative commutant `B(H)' ∩ B(H)^U` of the diagonal copy of `B(H)` in its norm ultrapower
is not `ℂ I` (some bounded sequence `(xₙ)` of operators asymptotically commutes along `U` with every
fixed operator but is not asymptotically scalar along `U`), then `U` is flat. -/
def nontrivialRelativeCommutantFlat : Prop :=
  ∀ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ cofinite →
    (∃ x : ℕ → (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2),
      (∃ C : ℝ, ∀ n, ‖x n‖ ≤ C) ∧
      (∀ a : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2,
        Tendsto (fun n => ‖x n * a - a * x n‖) (U : Filter ℕ) (𝓝 0)) ∧
      ∀ c : ℂ, ¬ Tendsto (fun n => ‖x n - c • (1 : lp (fun _ : ℕ => ℂ) 2 →L[ℂ]
        lp (fun _ : ℕ => ℂ) 2)‖) (U : Filter ℕ) (𝓝 0)) →
    IsFlat U

/--
Resolved true: for every nonprincipal ultrafilter `U` on `ℕ`, a nontrivial relative commutant
`B(H)' ∩ B(H)^U` forces `U` to be flat. Chetcuti and Zamora-Aviles quote the question of Farah,
Phillips and Steprāns ('If an ultrafilter α satisfies F_α(B(H)) ≠ ℂ, does it follow that α is
flat?') and 'give a positive answer'; their Theorem 25 states that F_α(B(H)) is non-trivial if and
only if α is flat, the converse being Farah-Phillips-Steprāns, Math. Ann. 347 (2010), Theorem 4.1.
Source: AimPL: Set theory and C* algebras, Section 1 (Ultrapowers), Problem 1.4,
http://aimpl.org/settheorycstar/1/; resolution: E. Chetcuti and B. Zamora-Aviles, On the commutant
of B(H) in its ultrapower, Israel J. Math. 255 (2023), no. 1, 423-451, arXiv:2108.02168, Theorem 25
(for every α ∈ βω \ ω, F_α(B(H)) is non-trivial if and only if α is flat) and the introduction
(positive answer to question 2 of Farah-Phillips-Steprāns); ℕ↑ = strictly increasing maps (§2),
flatness as in Proposition 10, https://doi.org/10.1007/s11856-022-2463-7.
-/
public theorem_wanted nontrivialRelativeCommutantFlat_holds : nontrivialRelativeCommutantFlat

end MathlibExt.Analysis.FlatUltrafilterRelativeCommutantAIMFunctionalAnalysisProblem20Wanted
