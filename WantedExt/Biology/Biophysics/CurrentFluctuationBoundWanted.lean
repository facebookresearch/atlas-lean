/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dissipation bounds steady-state current fluctuations

Gingrich, Horowitz, Perunov and England (2016) consider a continuous-time Markov jump process on
a finite state space with rates `r(y, z) ≥ 0` (with `r(z, y) > 0` whenever `r(y, z) > 0`) and
stationary law `π`. For a density `p` and an edge `y < z` with positive rates they set
`j^p(y, z) = p(y) r(y, z) - p(z) r(z, y)` and `a^p(y, z) = 2 √(p(y) p(z) r(y, z) r(z, y))`; the
force is `F(y, z) = ln (π(y) r(y, z) / (π(z) r(z, y)))`, the entropy production rate along the
edge is `σ^π = j^π F`, and the total is `Σ^π = ∑_{y<z} σ^π(y, z)` (`k_B = 1`). The level-2.5
rate function of the empirical density and current is `I(p, j) = ∑_{y<z} Ψ(j, j^p, a^p)` for
conservative currents, with

  `Ψ(j, j̄, a) = j (arsinh (j/a) - arsinh (j̄/a)) - (√(a² + j²) - √(a² + j̄²))`

(Eqs. (9)–(10)); the source takes it from the literature, and contracts it to the current rate
function `I(j) = inf_p I(p, j)`. Their results: the per-edge quadratic bound (Eq. (12)) and
`σ^π = 2 j^π arsinh (j^π / a^π)`; the bound `I(j) ≤ ∑_{y<z} (j - j^π)² σ^π / (4 (j^π)²)`
(Eq. (3)); for a generalized current `j_d = ∑_{y<z} d(y, z) j(y, z)`,
`I(j_d) ≤ (j_d - j_d^π)² Σ^π / (4 (j_d^π)²)` (Eq. (4)), whose case `d = F` is Eq. (5); and the
thermodynamic uncertainty relation `Var(j_d) Σ^π / (j_d^π)² ≥ 2` for the asymptotic variance
`Var(j_d) = 1 / I''(j_d^π)` (Eq. (8)).

Here `I(p, j)` is the formula (9)–(10), and the contraction is taken over positive densities.
That this contraction is the rate function of the empirical currents is the level-2.5 large
deviation principle, which the source cites and which is not stated here. Edges with zero
stationary current are excluded by hypothesis.

Sources: T. R. Gingrich, J. M. Horowitz, N. Perunov and J. L. England, "Dissipation bounds all
steady-state current fluctuations", Phys. Rev. Lett. 116 (2016) 120601, Eqs. (3)–(5), (8)–(12)
(arXiv:1512.02212).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace WantedExt.Biology.Biophysics.CurrentFluctuationBoundWanted

open Finset Filter Topology

variable {N : ℕ}

/-- The level-2.5 edge function
`Ψ(j, j̄, a) = j (arsinh (j/a) - arsinh (j̄/a)) - (√(a² + j²) - √(a² + j̄²))` (Eq. (10)). -/
noncomputable def psi (j jbar a : ℝ) : ℝ :=
  j * (Real.arsinh (j / a) - Real.arsinh (jbar / a)) -
    (Real.sqrt (a ^ 2 + j ^ 2) - Real.sqrt (a ^ 2 + jbar ^ 2))

/-- The mean current `j^p(y, z) = p(y) r(y, z) - p(z) r(z, y)` of the density `p`. -/
def meanCurrent (r : Fin N → Fin N → ℝ) (p : Fin N → ℝ) (y z : Fin N) : ℝ :=
  p y * r y z - p z * r z y

/-- The traffic `a^p(y, z) = 2 √(p(y) p(z) r(y, z) r(z, y))` of the density `p`. -/
noncomputable def traffic (r : Fin N → Fin N → ℝ) (p : Fin N → ℝ) (y z : Fin N) : ℝ :=
  2 * Real.sqrt (p y * p z * r y z * r z y)

/-- The force `F(y, z) = ln (π(y) r(y, z) / (π(z) r(z, y)))`. -/
noncomputable def force (r : Fin N → Fin N → ℝ) (π : Fin N → ℝ) (y z : Fin N) : ℝ :=
  Real.log (π y * r y z / (π z * r z y))

/-- The edges `y < z` with positive rate. -/
noncomputable def edges (r : Fin N → Fin N → ℝ) : Finset (Fin N × Fin N) :=
  univ.filter fun e => e.1 < e.2 ∧ 0 < r e.1 e.2

/-- The total entropy production rate `Σ^π = ∑_{y<z} j^π(y, z) F(y, z)`. -/
noncomputable def entropyRate (r : Fin N → Fin N → ℝ) (π : Fin N → ℝ) : ℝ :=
  ∑ e ∈ edges r, meanCurrent r π e.1 e.2 * force r π e.1 e.2

/-- A conservative current: antisymmetric, zero off the edges of positive rate, and with zero
net flow out of every state. -/
def Conservative (r : Fin N → Fin N → ℝ) (j : Fin N → Fin N → ℝ) : Prop :=
  (∀ y z, j z y = -j y z) ∧ (∀ y z, r y z = 0 → j y z = 0) ∧ ∀ y, ∑ z, j y z = 0

/-- The level-2.5 rate function `I(p, j) = ∑_{y<z} Ψ(j(y, z), j^p(y, z), a^p(y, z))` (Eq. (9)). -/
noncomputable def levelTwoFiveRate (r : Fin N → Fin N → ℝ) (p : Fin N → ℝ)
    (j : Fin N → Fin N → ℝ) : ℝ :=
  ∑ e ∈ edges r, psi (j e.1 e.2) (meanCurrent r p e.1 e.2) (traffic r p e.1 e.2)

/-- The contracted current rate function `I(j) = inf_p I(p, j)` over positive densities `p`. -/
noncomputable def currentRate (r : Fin N → Fin N → ℝ) (j : Fin N → Fin N → ℝ) : ℝ :=
  sInf ((fun p => levelTwoFiveRate r p j) '' {p | (∀ y, 0 < p y) ∧ ∑ y, p y = 1})

/-- The generalized current `j_d = ∑_{y<z} d(y, z) j(y, z)`. -/
noncomputable def generalizedCurrent (r : Fin N → Fin N → ℝ) (d j : Fin N → Fin N → ℝ) : ℝ :=
  ∑ e ∈ edges r, d e.1 e.2 * j e.1 e.2

/-- The rate function of a generalized current, `I(j_d) = inf {I(j) | j conservative with
∑_{y<z} d(y, z) j(y, z) = j_d}`. -/
noncomputable def generalizedRate (r : Fin N → Fin N → ℝ) (d : Fin N → Fin N → ℝ) (x : ℝ) : ℝ :=
  sInf (currentRate r '' {j | Conservative r j ∧ generalizedCurrent r d j = x})

/-- The setting: rates `r ≥ 0` with `r(z, y) > 0` whenever `r(y, z) > 0`; a positive
stationary probability law `π` (`∑_y π(y) r(y, z) = π(z) ∑_y r(z, y)` for every `z`); and
nonzero stationary current `j^π(y, z) ≠ 0` on every edge `y < z` of positive rate. -/
structure Setting (r : Fin N → Fin N → ℝ) (π : Fin N → ℝ) : Prop where
  r_nonneg : ∀ y z, 0 ≤ r y z
  r_symm_pos : ∀ y z, 0 < r y z → 0 < r z y
  π_pos : ∀ y, 0 < π y
  sum_π : ∑ y, π y = 1
  stationary : ∀ z, ∑ y, π y * r y z = π z * ∑ y, r z y
  current_ne_zero : ∀ e ∈ edges r, meanCurrent r π e.1 e.2 ≠ 0

/-- **The per-edge quadratic bound** (Gingrich et al. 2016, Eq. (12)). For all real `j`, every
`j̄ ≠ 0` and every `a > 0`,
`Ψ(j, j̄, a) ≤ (j - j̄)² / (4 j̄²) · 2 j̄ arsinh (j̄ / a)`.

Source: Gingrich, Horowitz, Perunov and England (2016), Eq. (12). -/
theorem_wanted psi_le_quadratic (j jbar a : ℝ) (hjbar : jbar ≠ 0) (ha : 0 < a) :
    psi j jbar a ≤ (j - jbar) ^ 2 / (4 * jbar ^ 2) * (2 * jbar * Real.arsinh (jbar / a))

/-- **Edge entropy production** (Gingrich et al. 2016, after Eq. (12)). Let `r(y, z) > 0`,
`r(z, y) > 0`, `π(y) > 0` and `π(z) > 0`. Then
`j^π(y, z) F(y, z) = 2 j^π(y, z) arsinh (j^π(y, z) / a^π(y, z))`.

Source: Gingrich, Horowitz, Perunov and England (2016), text after Eq. (12). -/
theorem_wanted meanCurrent_mul_force (r : Fin N → Fin N → ℝ) (π : Fin N → ℝ) (y z : Fin N)
    (hyz : 0 < r y z) (hzy : 0 < r z y) (hy : 0 < π y) (hz : 0 < π z) :
    meanCurrent r π y z * force r π y z =
      2 * meanCurrent r π y z * Real.arsinh (meanCurrent r π y z / traffic r π y z)

/-- **Linear-response bound on current fluctuations** (Gingrich et al. 2016, Eq. (3)). In the
setting `Setting` (rates `r ≥ 0` with positive reverse rates on edges, a positive stationary
probability law `π`, and nonzero stationary current on every edge of positive rate), for every
conservative current `j`,
`I(j) ≤ ∑_{y<z} (j(y, z) - j^π(y, z))² σ^π(y, z) / (4 j^π(y, z)²)`, with
`σ^π = j^π F`, the sum over edges `y < z` of positive rate, and `I(j) = inf_p I(p, j)`.

Source: Gingrich, Horowitz, Perunov and England (2016), Eq. (3). -/
theorem_wanted currentRate_le (r : Fin N → Fin N → ℝ) (π : Fin N → ℝ) (h : Setting r π)
    (j : Fin N → Fin N → ℝ) (hj : Conservative r j) :
    currentRate r j ≤ ∑ e ∈ edges r, (j e.1 e.2 - meanCurrent r π e.1 e.2) ^ 2 *
      (meanCurrent r π e.1 e.2 * force r π e.1 e.2) / (4 * meanCurrent r π e.1 e.2 ^ 2)

/-- **Dissipation bounds every generalized current** (Gingrich et al. 2016, Eqs. (4)–(5)). In
the setting `Setting`, for every weight `d` with `j_d^π = ∑_{y<z} d(y, z) j^π(y, z) ≠ 0` and
every real `x`, `I(j_d = x) ≤ (x - j_d^π)² Σ^π / (4 (j_d^π)²)`. Eq. (5) is the case `d = F`.

Source: Gingrich, Horowitz, Perunov and England (2016), Eqs. (4)–(5). -/
theorem_wanted generalizedRate_le (r : Fin N → Fin N → ℝ) (π : Fin N → ℝ) (h : Setting r π)
    (d : Fin N → Fin N → ℝ) (hd : generalizedCurrent r d (meanCurrent r π) ≠ 0) (x : ℝ) :
    generalizedRate r d x ≤ (x - generalizedCurrent r d (meanCurrent r π)) ^ 2 *
      entropyRate r π / (4 * generalizedCurrent r d (meanCurrent r π) ^ 2)

/-- **Thermodynamic uncertainty relation** (Gingrich et al. 2016, Eq. (8)). In the setting
`Setting`, let `d` be a weight with `j_d^π ≠ 0`, and suppose the rate function
`x ↦ I(j_d = x)` is differentiable near `j_d^π` and its derivative has derivative `c > 0` at
`j_d^π`. Then the asymptotic variance `Var(j_d) = 1 / c` satisfies
`Var(j_d) Σ^π / (j_d^π)² ≥ 2`.

Source: Gingrich, Horowitz, Perunov and England (2016), Eq. (8). -/
theorem_wanted uncertainty_relation (r : Fin N → Fin N → ℝ) (π : Fin N → ℝ) (h : Setting r π)
    (d : Fin N → Fin N → ℝ) (hd : generalizedCurrent r d (meanCurrent r π) ≠ 0)
    (hdiff : ∀ᶠ x in 𝓝 (generalizedCurrent r d (meanCurrent r π)),
      DifferentiableAt ℝ (generalizedRate r d) x)
    (c : ℝ) (hc : 0 < c)
    (h2 : HasDerivAt (deriv (generalizedRate r d)) c (generalizedCurrent r d (meanCurrent r π))) :
    2 ≤ 1 / c * entropyRate r π / generalizedCurrent r d (meanCurrent r π) ^ 2

end WantedExt.Biology.Biophysics.CurrentFluctuationBoundWanted
