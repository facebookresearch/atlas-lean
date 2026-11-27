/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Competitive exclusion in the chemostat (Hsu–Hubbell–Waltman)

Species `i` with maximal growth rate `mᵢ`, half-saturation constant `aᵢ` and yield `yᵢ` compete
for one substrate in a chemostat with input concentration `S⁰` and dilution rate `D`, common to
the substrate and every species: `S' = (S⁰ - S) D - ∑ᵢ (1/yᵢ) mᵢ xᵢ S / (aᵢ + S)` and
`xᵢ' = xᵢ (mᵢ S / (aᵢ + S) - D)`. With `bᵢ = mᵢ / D` and the break-even concentration
`λᵢ = aᵢ / (bᵢ - 1)` for `bᵢ > 1`, Hsu, Hubbell and Waltman (1977, Theorem 3.3) proved: if every
species has `bᵢ > 1`, one species `i₀` has the strictly smallest break-even concentration and
`λ_{i₀} < S⁰` (their hypothesis (Hₙ)), then from positive initial data `S → λ_{i₀}`,
`x_{i₀} → y_{i₀} (S⁰ - λ_{i₀})` and every other species dies out. Independently of the
competition, a species with `bⱼ ≤ 1` or `λⱼ > S⁰` dies out (their Theorem 3.2), and when the
smallest break-even concentration equals `S⁰` every species dies out (their Theorem 3.4).
Rapaport and Veruete (2017) reprove the exclusion theorem for increasing growth rates, setting
`λⱼ = ∞` for a species whose growth rate never reaches `D` (their Definition 1); their
Proposition 1 assumes distinct break-even concentrations (their Assumption 2,
`λ₁ < λ₂ < ⋯ < λ_N`, so at most one of them is infinite), and their §3.5 extends it to ties
among losing species strictly below `S⁰`.

Recorded here: the exclusion theorem under Hsu, Hubbell and Waltman's hypothesis (Hₙ), in which
every species has `bᵢ > 1` and losing species may share a break-even concentration at any level,
and the die-out theorem. The die-out statement uses the form `λⱼ ≥ S⁰` of
Rapaport and Veruete's Lemma 1(2), which covers both Theorem 3.2 (`λⱼ > S⁰`) and Theorem 3.4
(`λ₁ = S⁰` with `λ₁` the smallest). Their Lemma 1 is stated under the assumption of distinct
break-even concentrations, but the comparison argument that proves part (2) does not use it, so
the die-out statement does not assume it. Theorem 3.5 (equal break-even concentrations) is not
formalized.

Sources: S. B. Hsu, S. Hubbell and P. Waltman, "A mathematical theory for single-nutrient
competition in continuous cultures of micro-organisms", SIAM J. Appl. Math. 32 (1977) 366–383,
doi:10.1137/0132030, system (2.1)ₙ (p. 368), hypothesis (Hₙ) and Theorems 3.2, 3.3 and 3.4
(pp. 368–369); A. Rapaport and M. Veruete, "A new proof of the competitive exclusion principle in
the chemostat", arXiv:1711.06928 (2017), Definition 1, Assumption 2, Proposition 1 (p. 3),
Lemma 1 (p. 4) and §3.5 (p. 8) (numbering of the preprint), published in Discrete Contin. Dyn.
Syst. Ser. B 24 (2019) 3755–3764, doi:10.3934/dcdsb.2018314.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Biology.Ecology.ChemostatWashoutWanted
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.ChemostatCompetitiveExclusionWanted

open Filter Topology
open ChemostatWashoutWanted (breakEven)

/-- **Forward solutions of the multispecies chemostat.** `(S, x)` solves the chemostat at every
time `t ≥ 0`: `S'(t) = (S⁰ - S(t)) D - ∑ᵢ (1/yᵢ) mᵢ xᵢ(t) S(t) / (aᵢ + S(t))` and, for every
species `i`, `xᵢ'(t) = xᵢ(t) (mᵢ S(t) / (aᵢ + S(t)) - D)`. The derivatives are two-sided
(`HasDerivAt`) at `t = 0` too, so a trajectory given only on `[0, ∞)` must be extended to negative
times with these derivatives at `0`; one that is only right-differentiable at `0` does not
qualify. A solution on an open interval containing `[0, ∞)` qualifies, and negative times matter
only through the derivatives at `0`. -/
def IsSolution {ι : Type*} [Fintype ι] (S₀ D : ℝ) (m a y : ι → ℝ) (S : ℝ → ℝ)
    (x : ℝ → ι → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    HasDerivAt S ((S₀ - S t) * D - ∑ i, 1 / y i * m i * x t i * S t / (a i + S t)) t ∧
      ∀ i, HasDerivAt (fun s => x s i) (x t i * (m i * S t / (a i + S t) - D)) t

/-- **Competitive exclusion** (Hsu, Hubbell and Waltman 1977, Theorem 3.3): let `S⁰ > 0`, `D > 0`,
and for every species `i` let `mᵢ, aᵢ, yᵢ > 0` and `mᵢ > D`. Suppose species `i₀` has break-even
concentration `λ_{i₀} < S⁰`, and every other species `j ≠ i₀` has `λ_{i₀} < λⱼ`; losing species
may share a break-even concentration, at any level. Then every solution `(S, x)` of the
chemostat on `[0, ∞)` with `S(0) > 0` and `xᵢ(0) > 0` for every species `i` satisfies, as
`t → ∞`, `S(t) → λ_{i₀}`, `x_{i₀}(t) → y_{i₀} (S⁰ - λ_{i₀})`, and `xⱼ(t) → 0` for every
`j ≠ i₀`. With `bᵢ = mᵢ / D`, and the species relabeled so that `i₀` comes first and the
break-even concentrations are nondecreasing, these are Hsu, Hubbell and Waltman's hypothesis
(Hₙ), `0 < λ₁ < λ₂ ≤ ⋯ ≤ λₙ`, `λ₁ < S⁰` and `bᵢ > 1`, and the initial conditions
`S(0) > 0`, `xᵢ(0) > 0` of their system (2.1)ₙ.

Sources: Hsu, Hubbell and Waltman (1977), system (2.1)ₙ (p. 368), hypothesis (Hₙ) and
Theorem 3.3 (p. 369). -/
public theorem_wanted competitive_exclusion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S₀ D : ℝ) (m a y : ι → ℝ) (hS₀ : 0 < S₀) (hD : 0 < D) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hy : ∀ i, 0 < y i) (i₀ : ι) (hgrow : D < m i₀)
    (hlt : breakEven D (m i₀) (a i₀) < S₀)
    (hothers : ∀ j, j ≠ i₀ → D < m j ∧ breakEven D (m i₀) (a i₀) < breakEven D (m j) (a j))
    (S : ℝ → ℝ) (x : ℝ → ι → ℝ) (hsol : IsSolution S₀ D m a y S x) (hS : 0 < S 0)
    (hx : ∀ i, 0 < x 0 i) :
    Tendsto S atTop (𝓝 (breakEven D (m i₀) (a i₀))) ∧
      Tendsto (fun t => x t i₀) atTop (𝓝 (y i₀ * (S₀ - breakEven D (m i₀) (a i₀)))) ∧
      ∀ j, j ≠ i₀ → Tendsto (fun t => x t j) atTop (𝓝 0)

/-- **Die-out of species that cannot break even** (Hsu, Hubbell and Waltman 1977, Theorems 3.2
and 3.4; Rapaport and Veruete 2017, Lemma 1(2)): let `S⁰ > 0`, `D > 0`, and for every species `i`
let `mᵢ, aᵢ, yᵢ > 0`. If species `j` has `mⱼ ≤ D`, or `mⱼ > D` and break-even concentration
`λⱼ ≥ S⁰`, then every solution `(S, x)` of the chemostat on `[0, ∞)` with `S(0) ≥ 0` and
`xᵢ(0) > 0` for every species `i` satisfies `xⱼ(t) → 0` as `t → ∞`, whatever the other species.
Hsu, Hubbell and Waltman's Theorem 3.2 covers `mⱼ ≤ D` and `λⱼ > S⁰`, and their Theorem 3.4 the
case where `λⱼ = S⁰` is the smallest break-even concentration. Rapaport and Veruete's
Lemma 1(2) gives the form `λⱼ ≥ S⁰` whatever the other species; it is stated under their
assumption of distinct break-even concentrations, but its proof, a comparison argument for `xⱼ`
alone, does not use that assumption, so the statement here does not assume it.

Sources: Hsu, Hubbell and Waltman (1977), Theorems 3.2 and 3.4; Rapaport and Veruete (2017),
Lemma 1(2) and its proof. -/
public theorem_wanted dies_out {ι : Type*} [Fintype ι] (S₀ D : ℝ) (m a y : ι → ℝ)
    (hS₀ : 0 < S₀) (hD : 0 < D) (hm : ∀ i, 0 < m i) (ha : ∀ i, 0 < a i) (hy : ∀ i, 0 < y i)
    (j : ι) (hj : m j ≤ D ∨ (D < m j ∧ S₀ ≤ breakEven D (m j) (a j)))
    (S : ℝ → ℝ) (x : ℝ → ι → ℝ) (hsol : IsSolution S₀ D m a y S x) (hS : 0 ≤ S 0)
    (hx : ∀ i, 0 < x 0 i) :
    Tendsto (fun t => x t j) atTop (𝓝 0)

end WantedExt.Biology.Ecology.ChemostatCompetitiveExclusionWanted
