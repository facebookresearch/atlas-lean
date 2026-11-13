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
public import Mathlib.Data.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

namespace MathlibExt.Analysis.LogarithmicPotentialEquilibriumFreeWanted

/-! Source record `AMR-022-7078` (Problem 7.78). -/

/-- **Charge sequences.** A charge sequence is an arbitrary sequence $(z_n)_{n \in \mathbb{N}}$ of
complex numbers, read as the positions of the charges. -/
abbrev ChargeSeq := ℕ → ℂ

/-- **Distinct charge positions.** A charge sequence $(z_n)$ has distinct positions when its terms
are pairwise distinct: $z_m \neq z_n$ whenever $m \neq n$. -/
def PointsDistinct (c : ChargeSeq) : Prop :=
  Function.Injective c

/-- **Summable charge sequences.** A charge sequence $(z_n)$ is summable when $z_n \neq 0$ for every
$n$ and $\sum_n 1/|z_n| < \infty$. -/
def IsSummable (c : ChargeSeq) : Prop :=
  (∀ n, c n ≠ 0) ∧ Summable (fun n => 1 / ‖c n‖)

/-- **Field of a charge sequence.** For a charge sequence $(z_n)$ and a point $z \in \mathbb{C}$,
the field at $z$ is the sum $\sum_n 1/(z - z_n)$, where a term with $z_n = z$ counts as $0$ and the
sum is taken to be $0$ when the family $\bigl(1/(z - z_n)\bigr)_n$ is not summable.

The sum converges absolutely when $z_n \neq 0$ for every $n$ and $\sum_n 1/|z_n| < \infty$. -/
noncomputable def FieldSum (c : ChargeSeq) (z : ℂ) : ℂ :=
  ∑' n, 1 / (z - c n)

/-- **Equilibrium-free logarithmic potential conjecture.** The conjecture states that there exists
a charge sequence $(z_n)$ whose positions are pairwise distinct, which is summable ($z_n \neq 0$
for every $n$ and $\sum_n 1/|z_n| < \infty$), and whose field $\sum_n 1/(z - z_n)$ is nonzero at
every point $z \in \mathbb{C}$ that is not one of the $z_n$.

Source: record AMR-022-7078 (Problem 7.78, Rubel). -/
def conjecture : Prop :=
  ∃ c : ChargeSeq, PointsDistinct c ∧ IsSummable c ∧
    ∀ z : ℂ, (∀ n, z ≠ c n) → FieldSum c z ≠ 0

/--
**The equilibrium-free logarithmic potential conjecture is false.** There is no charge sequence
$(z_n)$ whose positions are pairwise distinct, which is summable ($z_n \neq 0$ for every $n$ and
$\sum_n 1/|z_n| < \infty$), and whose field $\sum_n 1/(z - z_n)$ is nonzero at every point
$z \in \mathbb{C}$ that is not one of the $z_n$.

Clunie, Eremenko and Rossi proved more: under these hypotheses the field has infinitely many
zeros.

Source: J. Clunie, A. Eremenko and J. Rossi, On equilibrium points of logarithmic and
Newtonian potentials, J. London Math. Soc. (2) 47 (1993), 309-320. Moved from
`OpenConjectures/Analysis/LogarithmicPotentialEquilibriumFree`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Analysis.LogarithmicPotentialEquilibriumFreeWanted
