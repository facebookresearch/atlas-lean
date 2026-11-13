/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
AMR-022-7078 (Problem 7.78, Rubel): Equilibrium-free logarithmic
potentials. Is there a distinct sequence {z_n} with Σ1/|z_n| < ∞ and
Σ1/(z-z_n) ≠ 0 for all z? Resolved negatively: Clunie–Eremenko–Rossi
proved the field always has (infinitely many) zeros.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

namespace MathlibExt.Analysis.LogarithmicPotentialEquilibriumFreeWanted

/-! Source record `AMR-022-7078` (Problem 7.78). -/

/-- Charge position sequences, concretely arbitrary sequences. -/
abbrev ChargeSeq := ℕ → ℂ

/-- Distinctness of the positions. -/
def PointsDistinct (c : ChargeSeq) : Prop :=
  Function.Injective c

/-- Summability Σ1/|z_n| < ∞, with all charge positions nonzero so every
term is defined. -/
def IsSummable (c : ChargeSeq) : Prop :=
  (∀ n, c n ≠ 0) ∧ Summable (fun n => 1 / ‖c n‖)

/-- The field value Σ1/(z-z_n), via `tsum`. The sum converges (hence the
equation is exact) for summable charge sequences off the charge set; at
unsummable inputs `tsum` is a junk value. -/
noncomputable def FieldSum (c : ChargeSeq) (z : ℂ) : ℂ :=
  ∑' n, 1 / (z - c n)

/-- [AMR-022-7078] An equilibrium-free configuration exists. -/
def conjecture : Prop :=
  ∃ c : ChargeSeq, PointsDistinct c ∧ IsSummable c ∧
    ∀ z : ℂ, (∀ n, z ≠ c n) → FieldSum c z ≠ 0

/--
Resolved false: Clunie-Eremenko-Rossi proved the field always has (infinitely many) zeros under
these hypotheses (J. London Math. Soc. 47 (1993), 309-320), so no equilibrium-free configuration
exists. Source: J. Clunie, A. Eremenko and J. Rossi, On equilibrium points of logarithmic and
Newtonian potentials, J. London Math. Soc. (2) 47 (1993), 309-320. Moved from
`OpenConjectures/Analysis/LogarithmicPotentialEquilibriumFree`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Analysis.LogarithmicPotentialEquilibriumFreeWanted
