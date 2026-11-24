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
`λᵢ = aᵢ / (bᵢ - 1)` for `bᵢ > 1`, Hsu, Hubbell and Waltman (1977) proved: if one species `i₀`
has `b_{i₀} > 1` and `λ_{i₀} < S⁰`, and every other species has either `bⱼ ≤ 1` or
`λ_{i₀} < λⱼ` (hypothesis H1), then from positive initial data `S → λ_{i₀}`,
`x_{i₀} → y_{i₀} (S⁰ - λ_{i₀})` and every other species dies out. Independently of the
competition, a species with `bⱼ ≤ 1` or `λⱼ ≥ S⁰` dies out (their Theorems 3.2 and 3.4).

Recorded here: the exclusion theorem and the die-out theorem. The die-out statement uses the
form `λⱼ ≥ S⁰` of Rapaport (2017, Lemma 1(2)), which covers both Theorem 3.2 (`λⱼ > S⁰`) and
Theorem 3.4 (`λ₁ = S⁰` with `λ₁` the smallest). Theorem 3.5 (equal break-even concentrations)
is not formalized.

Sources: S. B. Hsu, S. Hubbell and P. Waltman, "A mathematical theory for single-nutrient
competition in continuous cultures of micro-organisms", SIAM J. Appl. Math. 32 (1977) 366–383,
doi:10.1137/0132030, Theorems 3.1, 3.2, 3.4; A. Rapaport, "A new proof of the competitive
exclusion principle in the chemostat", arXiv:1711.06928 (2017), Lemma 1 and Proposition 1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.ChemostatCompetitiveExclusionWanted

open Filter Topology

/-- `(S, x)` solves the **multispecies chemostat** on `[0, ∞)`: for every `t ≥ 0`,
`S'(t) = (S⁰ - S(t)) D - ∑ᵢ (1/yᵢ) mᵢ xᵢ(t) S(t) / (aᵢ + S(t))` and, for every species `i`,
`xᵢ'(t) = xᵢ(t) (mᵢ S(t) / (aᵢ + S(t)) - D)`. -/
def IsSolution {ι : Type*} [Fintype ι] (S₀ D : ℝ) (m a y : ι → ℝ) (S : ℝ → ℝ)
    (x : ℝ → ι → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    HasDerivAt S ((S₀ - S t) * D - ∑ i, 1 / y i * m i * x t i * S t / (a i + S t)) t ∧
      ∀ i, HasDerivAt (fun s => x s i) (x t i * (m i * S t / (a i + S t) - D)) t

/-- The **break-even concentration** `λᵢ = aᵢ / (mᵢ / D - 1)` of a species, meaningful when
`mᵢ > D`. -/
noncomputable def breakEven (D mᵢ aᵢ : ℝ) : ℝ := aᵢ / (mᵢ / D - 1)

/-- **Competitive exclusion** (Hsu, Hubbell and Waltman 1977, Theorem 3.1): let `S⁰ > 0`,
`D > 0`, and for every species `i` let `mᵢ, aᵢ, yᵢ > 0`. Suppose species `i₀` has `m_{i₀} > D`
and break-even concentration `λ_{i₀} < S⁰`, and every other species `j ≠ i₀` has `mⱼ ≤ D` or
(`mⱼ > D` and `λ_{i₀} < λⱼ`). Then every solution `(S, x)` of the chemostat on `[0, ∞)` with
`S(0) ≥ 0` and `xᵢ(0) > 0` for every species `i` satisfies, as `t → ∞`, `S(t) → λ_{i₀}`,
`x_{i₀}(t) → y_{i₀} (S⁰ - λ_{i₀})`, and `xⱼ(t) → 0` for every `j ≠ i₀`.

Sources: Hsu, Hubbell and Waltman (1977), Theorem 3.1; Rapaport (2017), Proposition 1. -/
public theorem_wanted competitive_exclusion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S₀ D : ℝ) (m a y : ι → ℝ) (hS₀ : 0 < S₀) (hD : 0 < D) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hy : ∀ i, 0 < y i) (i₀ : ι) (hgrow : D < m i₀)
    (hlt : breakEven D (m i₀) (a i₀) < S₀)
    (hothers : ∀ j, j ≠ i₀ → m j ≤ D ∨
      (D < m j ∧ breakEven D (m i₀) (a i₀) < breakEven D (m j) (a j)))
    (S : ℝ → ℝ) (x : ℝ → ι → ℝ) (hsol : IsSolution S₀ D m a y S x) (hS : 0 ≤ S 0)
    (hx : ∀ i, 0 < x 0 i) :
    Tendsto S atTop (𝓝 (breakEven D (m i₀) (a i₀))) ∧
      Tendsto (fun t => x t i₀) atTop (𝓝 (y i₀ * (S₀ - breakEven D (m i₀) (a i₀)))) ∧
      ∀ j, j ≠ i₀ → Tendsto (fun t => x t j) atTop (𝓝 0)

/-- **Die-out of species that cannot break even** (Hsu, Hubbell and Waltman 1977, Theorems 3.2
and 3.4; Rapaport 2017, Lemma 1(2)): let `S⁰ > 0`, `D > 0`, and for every species `i` let
`mᵢ, aᵢ, yᵢ > 0`. If species `j` has `mⱼ ≤ D`, or `mⱼ > D` and break-even concentration
`λⱼ ≥ S⁰`, then every solution `(S, x)` of the chemostat on `[0, ∞)` with `S(0) ≥ 0` and
`xᵢ(0) > 0` for every species `i` satisfies `xⱼ(t) → 0` as `t → ∞`, whatever the other species.

Sources: Hsu, Hubbell and Waltman (1977), Theorems 3.2 and 3.4; Rapaport (2017), Lemma 1. -/
public theorem_wanted dies_out {ι : Type*} [Fintype ι] (S₀ D : ℝ) (m a y : ι → ℝ)
    (hS₀ : 0 < S₀) (hD : 0 < D) (hm : ∀ i, 0 < m i) (ha : ∀ i, 0 < a i) (hy : ∀ i, 0 < y i)
    (j : ι) (hj : m j ≤ D ∨ (D < m j ∧ S₀ ≤ breakEven D (m j) (a j)))
    (S : ℝ → ℝ) (x : ℝ → ι → ℝ) (hsol : IsSolution S₀ D m a y S x) (hS : 0 ≤ S 0)
    (hx : ∀ i, 0 < x 0 i) :
    Tendsto (fun t => x t j) atTop (𝓝 0)

end WantedExt.Biology.Ecology.ChemostatCompetitiveExclusionWanted
