/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Beverton–Holt convergence and the Cushing–Henson theorems for periodic environments

The Beverton–Holt map with inherent growth `ν > 1` and carrying capacity `K > 0` is
`x ↦ ν K x / (K + (ν - 1) x)`. With constant `K`, every positive orbit converges to `K`.
Cushing and Henson (2002) conjectured, for a `p`-periodic sequence of carrying capacities
`K_t > 0`, that (1) the equation `x_{t+1} = ν K_t x_t / (K_t + (ν - 1) x_t)` has a unique
positive `p`-periodic solution, which attracts every positive solution, and (2) its average is
strictly smaller than the average carrying capacity unless `K` is constant (the environment is
deleterious). Elaydi and Sacker proved the first conjecture and, with Kon and Kocic
independently, the second; Stević (2006) gave a short proof of the second. They are recorded
here as theorems.

Sources: J. M. Cushing and S. M. Henson, "A periodically forced Beverton–Holt equation",
J. Difference Equ. Appl. 8 (2002) 1119–1120; S. Elaydi and R. J. Sacker, "Nonautonomous
Beverton–Holt equations and the Cushing–Henson conjectures", J. Difference Equ. Appl. 11
(2005) 337–346, §3; S. Elaydi and R. J. Sacker, J. Differential Equations,
doi:10.1016/j.jde.2003.10.024; R. Kon, J. Difference Equ. Appl. 10 (2004) 791–793;
R. Kon, J. Difference Equ. Appl. 11 (2005) 423–430; V. L. Kocic, "A note on the
nonautonomous Beverton–Holt model", J. Difference Equ. Appl. 11 (2005) 415–422; S. Stević,
Discrete Dyn. Nat. Soc. (2006) Art. 37264, Theorem 1.3.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace WantedExt.Biology.Ecology.BevertonHoltCushingHensonWanted

open Finset Filter Topology

/-- The **Beverton–Holt map** `x ↦ ν K x / (K + (ν - 1) x)`. -/
noncomputable def bevertonHolt (ν K x : ℝ) : ℝ :=
  ν * K * x / (K + (ν - 1) * x)

/-- The solution of `x_{t+1} = ν K_t x_t / (K_t + (ν - 1) x_t)` with `x_0 = x₀`. -/
noncomputable def orbit (ν : ℝ) (K : ℕ → ℝ) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | t + 1 => bevertonHolt ν (K t) (orbit ν K x₀ t)

/-- **Global convergence of the autonomous Beverton–Holt equation**: for `ν > 1`, `K > 0` and
`x₀ > 0`, the solution with constant carrying capacity `K` converges to `K`.

Source: Elaydi and Sacker (2005, J. Difference Equ. Appl.), §1. -/
public theorem_wanted tendsto_orbit_const {ν K x₀ : ℝ} (hν : 1 < ν) (hK : 0 < K)
    (hx₀ : 0 < x₀) :
    Tendsto (orbit ν (fun _ => K) x₀) atTop (𝓝 K)

/-- **First Cushing–Henson theorem** (Elaydi and Sacker, J. Differential Equations). For
`ν > 1`, `p ≥ 1` and a `p`-periodic sequence of carrying capacities `K_t > 0`, there is a unique
`x₀ > 0` whose solution is `p`-periodic, and every positive solution approaches it.

Sources: Cushing and Henson (2002), Conjecture 1; Elaydi and Sacker (2005, J. Difference Equ.
Appl.), §4. -/
public theorem_wanted exists_unique_periodic_attractor {ν : ℝ} (hν : 1 < ν) {p : ℕ}
    (hp : 0 < p) {K : ℕ → ℝ} (hK : ∀ t, 0 < K t) (hKp : Function.Periodic K p) :
    ∃ x₀, 0 < x₀ ∧ Function.Periodic (orbit ν K x₀) p ∧
      (∀ y₀, 0 < y₀ → Function.Periodic (orbit ν K y₀) p → y₀ = x₀) ∧
      ∀ y₀, 0 < y₀ → Tendsto (fun t => orbit ν K y₀ t - orbit ν K x₀ t) atTop (𝓝 0)

/-- **Second Cushing–Henson theorem** (Elaydi and Sacker 2005; Kon 2004; Kocic 2005; Stević
2006, Theorem 1.3). For `ν > 1`, `p ≥ 1`, a `p`-periodic sequence of carrying capacities
`K_t > 0`, and `x₀ > 0` whose Beverton–Holt orbit is `p`-periodic, the average of that positive
`p`-periodic solution over a period is at most the average carrying capacity, and strictly
smaller whenever `K` is not constant.

Sources: Cushing and Henson (2002), Conjecture 2; Stević (2006), Theorem 1.3. -/
public theorem_wanted periodic_average_lt {ν : ℝ} (hν : 1 < ν) {p : ℕ} (hp : 0 < p)
    {K : ℕ → ℝ} (hK : ∀ t, 0 < K t) (hKp : Function.Periodic K p) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hper : Function.Periodic (orbit ν K x₀) p) :
    (∑ t ∈ range p, orbit ν K x₀ t) / p ≤ (∑ t ∈ range p, K t) / p ∧
      ((∃ s t, K s ≠ K t) → (∑ t ∈ range p, orbit ν K x₀ t) / p < (∑ t ∈ range p, K t) / p)

end WantedExt.Biology.Ecology.BevertonHoltCushingHensonWanted
