/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dissipation bounds steady-state current fluctuations

Gingrich, Horowitz, Perunov and England (2016) consider an ergodic continuous-time Markov jump
process on a finite state space, with rates `r(y, z) ≥ 0` (with `r(z, y) > 0` whenever
`r(y, z) > 0`, and any two states joined by a chain of transitions of positive rate), whose
density relaxes to a unique stationary law `π`. For a density `p` and an edge `y < z` with
positive rates they set
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
`Var(j_d) = 1 / I''(j_d^π)` (Eq. (8)). Here Eq. (8) is stated as the reciprocal-curvature bound
`I''(j_d^π) ≤ Σ^π / (2 (j_d^π)²)` on the rate function; reading `1 / I''` as the variance is the
second-order expansion of the rate function and is not stated.

Here `I(p, j)` is the formula (9)–(10), and the contraction is taken over positive densities.
That this contraction is the rate function of the empirical currents is the level-2.5 large
deviation principle, which the source cites and which is not stated here. Edges with zero
stationary current are excluded by hypothesis. The rate functions take values in `[0, ∞]`: a
non-conservative current, or a value `j_d = x` attained by no conservative current, has rate
`+∞`, as in the source.

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
public import Mathlib.Basic.ENNReal.Real

@[expose] public section

namespace WantedExt.Biology.Biophysics.CurrentFluctuationBoundWanted

open Finset Filter Topology
open scoped ENNReal

variable {N : ℕ}

/-- The level-2.5 edge function
`Ψ(j, j̄, a) = j (arsinh (j/a) - arsinh (j̄/a)) - (√(a² + j²) - √(a² + j̄²))` (Eq. (10)). -/
noncomputable def psi (j jbar a : ℝ) : ℝ :=
  j * (Real.arsinh (j / a) - Real.arsinh (jbar / a)) -
    (Real.sqrt (a ^ 2 + j ^ 2) - Real.sqrt (a ^ 2 + jbar ^ 2))

/-- The current `j^p(y, z) = p(y) r(y, z) - p(z) r(z, y)` of a function `p` on the states, for
arbitrary real `p` and `r`; when `p` is a probability density it is the mean current of `p`. -/
def meanCurrent (r : Fin N → Fin N → ℝ) (p : Fin N → ℝ) (y z : Fin N) : ℝ :=
  p y * r y z - p z * r z y

/-- The traffic `a^p(y, z) = 2 √(p(y) p(z) r(y, z) r(z, y))` of a function `p` on the states,
for arbitrary real `p` and `r` (the source takes `p` a probability density). -/
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

open Classical in
/-- The contracted current rate function `I(j) = inf_p I(p, j)`, with values in `[0, ∞]`: for a
conservative current `j` it is the infimum of `I(p, j)` over positive probability densities `p`,
and for a non-conservative current it is `+∞`, as in the source. Each `I(p, j)` is a sum of terms
`Ψ(j, j^p, a^p)` over the edges; for nonnegative rates (as in `Setting`), a positive `p` and a
conservative `j`, every term is nonnegative, since `Ψ(·, j̄, a)` is convex and nonnegative for
`a > 0`, and an edge with `a^p = 0` has zero reverse rate, where a conservative `j` vanishes. -/
noncomputable def currentRate (r : Fin N → Fin N → ℝ) (j : Fin N → Fin N → ℝ) : ℝ≥0∞ :=
  if Conservative r j then
    ⨅ (p : Fin N → ℝ) (_ : (∀ y, 0 < p y) ∧ ∑ y, p y = 1), ENNReal.ofReal (levelTwoFiveRate r p j)
  else ⊤

/-- The generalized current `j_d = ∑_{y<z} d(y, z) j(y, z)`. -/
noncomputable def generalizedCurrent (r : Fin N → Fin N → ℝ) (d j : Fin N → Fin N → ℝ) : ℝ :=
  ∑ e ∈ edges r, d e.1 e.2 * j e.1 e.2

/-- The rate function of a generalized current, `I(j_d = x) = inf {I(j) | j conservative with
∑_{y<z} d(y, z) j(y, z) = x}`, with values in `[0, ∞]`. On an infeasible value `x`, attained by no
conservative current (for example `d = 0` and `x ≠ 0`), the infimum is over the empty set and the
rate is `+∞`. In the setting `Setting r π`, where `π` is stationary, `j_d^π ≠ 0` makes every real
`x` feasible (scale the stationary current `j^π`, which stationarity makes conservative), and the
rate is then finite by `generalizedRate_le`. A nonzero `j_d^p` for a law `p` that is not
stationary gives neither: with two states, unit rates both ways, `d = 1` and `p = (3/4, 1/4)`,
`j^p ≠ 0`, yet the only conservative current is `0`, so the rate at `x = 1` is `+∞`. -/
noncomputable def generalizedRate (r : Fin N → Fin N → ℝ) (d : Fin N → Fin N → ℝ) (x : ℝ) :
    ℝ≥0∞ :=
  ⨅ (j : Fin N → Fin N → ℝ) (_ : Conservative r j ∧ generalizedCurrent r d j = x), currentRate r j

/-- The setting, the source's (p. 1, before Eq. (1)): an ergodic chain. Its rates `r ≥ 0` have
`r(z, y) > 0` whenever `r(y, z) > 0`, and any two states are joined by a chain of transitions of
positive rate (irreducibility, which with finitely many states makes the stationary law unique);
`π` is a positive stationary probability law (`∑_y π(y) r(y, z) = π(z) ∑_y r(z, y)` for every
`z`), so the unique one; and the stationary current `j^π(y, z)` is nonzero on every edge `y < z`
of positive rate. -/
structure Setting (r : Fin N → Fin N → ℝ) (π : Fin N → ℝ) : Prop where
  r_nonneg : ∀ y z, 0 ≤ r y z
  r_symm_pos : ∀ y z, 0 < r y z → 0 < r z y
  irreducible : ∀ y z, Relation.ReflTransGen (fun a b => 0 < r a b) y z
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

/-- **Edge entropy production** (Gingrich et al. 2016, after Eq. (12)). In the setting
`Setting r π` (an ergodic chain and its stationary law `π`), on every edge of positive rate,
`r(y, z) > 0`, the stationary current and the force satisfy
`j^π(y, z) F(y, z) = 2 j^π(y, z) arsinh (j^π(y, z) / a^π(y, z))`: the source's
`σ^π = 2 j^π arcsinh (j^π / a^π)` for the steady state. `Setting` gives `r(z, y) > 0`
(`r_symm_pos`) and `π(y), π(z) > 0` (`π_pos`).

Source: Gingrich, Horowitz, Perunov and England (2016), text after Eq. (12), in the setting of
p. 1. -/
theorem_wanted meanCurrent_mul_force (r : Fin N → Fin N → ℝ) (π : Fin N → ℝ) (h : Setting r π)
    (y z : Fin N) (hyz : 0 < r y z) :
    meanCurrent r π y z * force r π y z =
      2 * meanCurrent r π y z * Real.arsinh (meanCurrent r π y z / traffic r π y z)

/-- **Linear-response bound on current fluctuations** (Gingrich et al. 2016, Eq. (3)). In the
setting `Setting r π` (an ergodic chain: rates `r ≥ 0` with positive reverse rates on edges and
any two states joined by a chain of transitions of positive rate; its positive stationary
probability law `π`; and nonzero stationary current on every edge of positive rate), for every
conservative current `j`,
`I(j) ≤ ∑_{y<z} (j(y, z) - j^π(y, z))² σ^π(y, z) / (4 j^π(y, z)²)` in `[0, ∞]` (the right side is
a nonnegative real number), with `σ^π = j^π F`, the sum over edges `y < z` of positive rate, and
`I(j) = inf_p I(p, j)`.

Source: Gingrich, Horowitz, Perunov and England (2016), Eq. (3). -/
theorem_wanted currentRate_le (r : Fin N → Fin N → ℝ) (π : Fin N → ℝ) (h : Setting r π)
    (j : Fin N → Fin N → ℝ) (hj : Conservative r j) :
    currentRate r j ≤ ENNReal.ofReal (∑ e ∈ edges r, (j e.1 e.2 - meanCurrent r π e.1 e.2) ^ 2 *
      (meanCurrent r π e.1 e.2 * force r π e.1 e.2) / (4 * meanCurrent r π e.1 e.2 ^ 2))

/-- **Dissipation bounds every generalized current** (Gingrich et al. 2016, Eqs. (4)–(5)). In
the setting `Setting r π` (an ergodic chain and its stationary law `π`, as in `currentRate_le`),
for every weight `d` with `j_d^π = ∑_{y<z} d(y, z) j^π(y, z) ≠ 0` and every real `x`,
`I(j_d = x) ≤ (x - j_d^π)² Σ^π / (4 (j_d^π)²)` in `[0, ∞]` (the right side is a nonnegative real
number; in particular every `x` is feasible and `I(j_d = x)` is finite). Eq. (5) is the case
`d = F`.

Source: Gingrich, Horowitz, Perunov and England (2016), Eqs. (4)–(5). -/
theorem_wanted generalizedRate_le (r : Fin N → Fin N → ℝ) (π : Fin N → ℝ) (h : Setting r π)
    (d : Fin N → Fin N → ℝ) (hd : generalizedCurrent r d (meanCurrent r π) ≠ 0) (x : ℝ) :
    generalizedRate r d x ≤ ENNReal.ofReal ((x - generalizedCurrent r d (meanCurrent r π)) ^ 2 *
      entropyRate r π / (4 * generalizedCurrent r d (meanCurrent r π) ^ 2))

/-- **Thermodynamic uncertainty relation, curvature form** (Gingrich et al. 2016, Eq. (8)). In
the setting `Setting r π` (an ergodic chain and its stationary law `π`), let `d` be a weight with
`j_d^π ≠ 0` (so every `x` is feasible and the rate `I(j_d = x)` is finite; the real-valued rate
function is `x ↦ (I(j_d = x)).toReal`), and suppose
this real rate function is differentiable near `j_d^π` and its derivative has derivative
`c = I''(j_d^π) > 0` at `j_d^π`. Then the reciprocal curvature satisfies
`(1 / I''(j_d^π)) Σ^π / (j_d^π)² ≥ 2`, i.e. `I''(j_d^π) ≤ Σ^π / (2 (j_d^π)²)`. This is a
statement about the large-deviation rate function. The source reads `1 / I''(j_d^π)` as the
asymptotic variance `Var(j_d)` of the time-averaged current (the second-order expansion of the
rate function at its minimum), which gives the stochastic uncertainty relation
`Var(j_d) Σ^π / (j_d^π)² ≥ 2`; that identification, a consequence of the large deviation
principle, is not stated here.

Source: Gingrich, Horowitz, Perunov and England (2016), Eq. (8). -/
theorem_wanted uncertainty_relation (r : Fin N → Fin N → ℝ) (π : Fin N → ℝ) (h : Setting r π)
    (d : Fin N → Fin N → ℝ) (hd : generalizedCurrent r d (meanCurrent r π) ≠ 0)
    (hdiff : ∀ᶠ x in 𝓝 (generalizedCurrent r d (meanCurrent r π)),
      DifferentiableAt ℝ (fun y => (generalizedRate r d y).toReal) x)
    (c : ℝ) (hc : 0 < c)
    (h2 : HasDerivAt (deriv fun y => (generalizedRate r d y).toReal) c
      (generalizedCurrent r d (meanCurrent r π))) :
    2 ≤ 1 / c * entropyRate r π / generalizedCurrent r d (meanCurrent r π) ^ 2

end WantedExt.Biology.Biophysics.CurrentFluctuationBoundWanted
