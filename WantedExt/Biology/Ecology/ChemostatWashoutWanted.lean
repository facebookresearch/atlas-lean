/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The single-species chemostat: the washout criterion

A chemostat with input substrate concentration `S⁰`, dilution rate `D`, maximal growth rate `m`,
half-saturation constant `a` and yield `y` (all positive) and Monod uptake obeys
`S' = (S⁰ - S) D - (1/y) m S x / (a + S)` and `x' = x (m S / (a + S) - D)`. Let `b = m / D`
and, when `b > 1`, let `λ = a / (b - 1)` be the break-even concentration, where growth balances
dilution. For every solution with `S(0) ≥ 0` and `x(0) > 0`: if `b ≤ 1`, or `b > 1` and
`λ ≥ S⁰`, the organism washes out (`x → 0`, `S → S⁰`); if `b > 1` and `λ < S⁰`, then `S → λ`
and `x → y (S⁰ - λ)`. The proof uses that `S + x / y → S⁰` and reduces to one dimension.

Recorded here: the washout criterion for solutions on `[0, ∞)`. Global convergence to the positive
equilibrium (`S → λ`, `x → y (S⁰ - λ)` when `b > 1` and `λ < S⁰`) is not restated here: it is
tracked on the existing chemostat roadmap node
`blueprint/roadmap/Biology/population-dynamics/chemostat/global-convergence-of-the-chemostat.md`.
The monograph of Smith and Waltman (1995) was not read; the statement follows Hsu, Hubbell and
Waltman (1977, Theorems 3.2 and 3.4) with one species and Rapaport and Veruete (2017, Lemma 1,
with the yield rescaled to `1`). The chemostat model `Domains.Biology.Dynamics.Chemostat` writes
the same balances for the state `![x, S]` (biomass first, then substrate) with the growth rate
`μ = mmRate m a`: `isSolution_iff_hasDerivAt_vectorField` states that the two notions of
solution agree, and `breakEven_eq_steadyConc` identifies `λ`, for `D ≠ 0`, with
`steadyConc m a D`, the substrate coordinate of that model's candidate interior state
`interiorState`. That candidate is a steady state with positive biomass only for positive
parameters with `D < m S⁰ / (a + S⁰)`, that is `m > D` and `λ < S⁰`
(`equilibria_and_washout_threshold`).

Sources: H. L. Smith and P. Waltman, *The Theory of the Chemostat: Dynamics of Microbial
Competition*, Cambridge Univ. Press (1995), doi:10.1017/CBO9780511530043; S. B. Hsu, S. Hubbell
and P. Waltman, "A mathematical theory for single-nutrient competition in continuous cultures of
micro-organisms", SIAM J. Appl. Math. 32 (1977) 366–383, doi:10.1137/0132030; A. Rapaport and
M. Veruete, "A new proof of the competitive exclusion principle in the chemostat",
arXiv:1711.06928 (2017), published in Discrete Contin. Dyn. Syst. Ser. B 24 (2019) 3755–3764,
doi:10.3934/dcdsb.2018314.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.Dynamics.Chemostat
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

namespace WantedExt.Biology.Ecology.ChemostatWashoutWanted

open Filter Topology
open Domains.Biology.Dynamics.Chemostat (vectorField)
open MathlibExt.Biology.Dynamics.MichaelisMenten (mmRate)
open MathlibExt.Biology.Biophysics.SaturableElimination (steadyConc)

/-- **Forward solutions of the single-species chemostat.** `(S, x)` solves the chemostat with
input concentration `S⁰`, dilution rate `D`, maximal growth rate `m`, half-saturation constant `a`
and yield `y` at every time `t ≥ 0`: `S'(t) = (S⁰ - S(t)) D - (1/y) m S(t) x(t) / (a + S(t))` and
`x'(t) = x(t) (m S(t) / (a + S(t)) - D)`. The derivatives are two-sided (`HasDerivAt`) at `t = 0`
too, so a trajectory given only on `[0, ∞)` must be extended to negative times with these
derivatives at `0`; one that is only right-differentiable at `0` does not qualify. A solution on
an open interval containing `[0, ∞)` qualifies, and negative times matter only through the
derivatives at `0`. Equivalently, `t ↦ ![x t, S t]` has the derivative given by the chemostat
model's vector field `vectorField (mmRate m a) D S⁰ y` at every `t ≥ 0`
(`isSolution_iff_hasDerivAt_vectorField`). -/
def IsSolution (S₀ D m a y : ℝ) (S x : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    HasDerivAt S ((S₀ - S t) * D - 1 / y * m * S t * x t / (a + S t)) t ∧
      HasDerivAt x (x t * (m * S t / (a + S t) - D)) t

/-- **The single-species chemostat in the chemostat model's coordinates.** `(S, x)` solves the
single-species chemostat (`IsSolution`) exactly when, at every time `t ≥ 0`, the curve
`t ↦ ![x t, S t]` in `Fin 2 → ℝ` (biomass first, then substrate) has the two-sided derivative
`vectorField (mmRate m a) D S⁰ y` of the chemostat model `Domains.Biology.Dynamics.Chemostat`,
whose Monod growth rate is `μ(S) = m S / (a + S)`. -/
theorem isSolution_iff_hasDerivAt_vectorField (S₀ D m a y : ℝ) (S x : ℝ → ℝ) :
    IsSolution S₀ D m a y S x ↔ ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => ![x s, S s]) (vectorField (mmRate m a) D S₀ y ![x t, S t]) t := by
  refine forall₂_congr fun t _ => ?_
  rw [hasDerivAt_pi, Fin.forall_fin_two, and_comm]
  simp only [Fin.isValue, vectorField, mmRate, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact and_congr ⟨fun h => h.congr_deriv (by ring), fun h => h.congr_deriv (by ring)⟩
    ⟨fun h => h.congr_deriv (by ring), fun h => h.congr_deriv (by ring)⟩

/-- The **break-even concentration** `λ = a / (m / D - 1)`, meaningful when `m > D`. For `D ≠ 0`
the formula equals `steadyConc m a D = D a / (m - D)`, the substrate coordinate of the chemostat
model's candidate interior state `interiorState` (`breakEven_eq_steadyConc`). That candidate is
a steady state with positive biomass only for positive parameters with `D < m S⁰ / (a + S⁰)`,
that is `m > D` and `λ < S⁰` (`equilibria_and_washout_threshold`). -/
noncomputable def breakEven (D m a : ℝ) : ℝ := a / (m / D - 1)

/-- **The break-even formula is the chemostat model's candidate interior substrate level.** For
`D ≠ 0`, the break-even concentration `λ = a / (m / D - 1)` equals
`steadyConc m a D = D a / (m - D)`, the substrate coordinate of the candidate interior state
`interiorState` of the chemostat model `Domains.Biology.Dynamics.Chemostat`. This is an identity
of formulas: for `m > 0`, `a > 0` and `D < m` the Monod growth rate `m S / (a + S)` equals `D` at
`S = λ`, but the candidate is a steady state with positive biomass `y (S⁰ - λ)` only for
positive parameters with `D < m S⁰ / (a + S⁰)`, that is `m > D` and `λ < S⁰`, as
`equilibria_and_washout_threshold` states. -/
theorem breakEven_eq_steadyConc {D : ℝ} (hD : D ≠ 0) (m a : ℝ) :
    breakEven D m a = steadyConc m a D := by
  rw [breakEven, steadyConc, div_sub_one hD, div_div_eq_mul_div, mul_comm a D]

/-- **Washout** (Hsu, Hubbell and Waltman 1977, Theorems 3.2 and 3.4 with one species; Rapaport
and Veruete 2017, Lemma 1): let `S⁰, D, m, a, y > 0`, and suppose `m ≤ D`, or `m > D` and
`λ = a / (m / D - 1) ≥ S⁰`. Then every solution `(S, x)` of the chemostat on `[0, ∞)` with
`S(0) ≥ 0` and `x(0) > 0` satisfies `x(t) → 0` and `S(t) → S⁰` as `t → ∞`. Hsu, Hubbell and
Waltman's Theorem 3.2 gives `x → 0` when `m ≤ D` or `λ > S⁰`, and their Theorem 3.4 gives both
limits when `λ = S⁰`; Rapaport and Veruete's Lemma 1 gives both limits in every case.

Sources: Hsu, Hubbell and Waltman (1977), Theorems 3.2 and 3.4; Rapaport and Veruete (2017),
Lemma 1. -/
public theorem_wanted washout (S₀ D m a y : ℝ) (hS₀ : 0 < S₀) (hD : 0 < D) (hm : 0 < m)
    (ha : 0 < a) (hy : 0 < y) (hwash : m ≤ D ∨ (D < m ∧ S₀ ≤ breakEven D m a))
    (S x : ℝ → ℝ) (hsol : IsSolution S₀ D m a y S x) (hS : 0 ≤ S 0) (hx : 0 < x 0) :
    Tendsto x atTop (𝓝 0) ∧ Tendsto S atTop (𝓝 S₀)

end WantedExt.Biology.Ecology.ChemostatWashoutWanted
