/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1102
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Topology.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

open Filter
open scoped Topology

namespace MathlibExt.NumberTheory.ErdosProblem1102Wanted

/-! Source record `FC-ErdosProblem1102`, ported from FormalConjectures
`ErdosProblems/1102.lean` (`def HasPropertyP`, `HasPropertyQ`, `theorem
erdos_1102.density_zero_of_P`, `exists_sequence_with_P`, `upper_density_Q`,
`lower_density_Q_exists`) and checked against erdosproblems.com/1102. The
four growth-rate claims are separate targets (all established by van
Doorn–Tao [vDTa25]). Status: resolved true as formalized (whether
`2^n ± 1` or `n! ± 1` have property `P` remains open and is not
formalized). -/

/-- `A` has property P if shifted squarefree sets are always finite. -/
def HasPropertyP (A : Set ℕ) : Prop :=
  ∀ n ≥ 1, {a ∈ A | Squarefree (n + a)}.Finite

/-- `A` has property Q if squarefree shifts occur infinitely often above
every element. -/
def HasPropertyQ (A : Set ℕ) : Prop :=
  {n : ℕ | ∀ a ∈ A, a < n → Squarefree (n + a)}.Infinite

/-- Property-P sequences have density zero (established). -/
def densityZeroOfP : Prop :=
  ∀ (A : ℕ → ℕ) (_ : StrictMono A) (_ : HasPropertyP (Set.range A)),
    Tendsto (fun j => (A j / j : ℝ)) atTop atTop

/-- Property-P sequences exist with arbitrarily slow decay (established). -/
def arbitrarilySlowP : Prop :=
  ∀ (f : ℕ → ℕ) (_ : Tendsto f atTop atTop) (_ : ∀ n, f n ≠ 0),
    ∃ A : ℕ → ℕ, StrictMono A ∧
    HasPropertyP (Set.range A) ∧
    ∀ j : ℕ, (A j : ℝ) / j ≤ f j

/-- Property-Q sequences have upper density at most `6 / π ^ 2`
(established). -/
def upperDensityQ : Prop :=
  ∀ (A : ℕ → ℕ) (_ : StrictMono A) (_ : HasPropertyQ (Set.range A)),
    limsup (fun j : ℕ ↦ (j / A j : ℝ)) atTop ≤ 6 / Real.pi ^ 2

/-- Property-Q sequences exist with density exactly `6 / π ^ 2`
(established). -/
def sharpDensityQ : Prop :=
  ∃ A : ℕ → ℕ, StrictMono A ∧
    (∀ j, Squarefree (A j)) ∧
    HasPropertyQ (Set.range A) ∧
    Tendsto (fun j : ℕ ↦ (j / A j : ℝ)) atTop (𝓝 (6 / Real.pi ^ 2))

/--
Resolved true: All four formalized targets are proved by van Doorn and Tao (arXiv:2512.01087,
Theorems 1-3): every sequence with property P has density zero (densityZeroOfP), with the
density allowed to tend to zero arbitrarily slowly (arbitrarilySlowP); every sequence with
property Q has upper density at most 6/π^2 (upperDensityQ); and a squarefree sequence with
property Q has density exactly 6/π^2 (sharpDensityQ). erdosproblems.com/1102 (checked
2026-10-22) lists the problem as solved; whether 2^n ± 1 or n! ± 1 have property P is open there
and is not formalized (see gaps). This target holds: Theorem 1(i): if A = {a_1 < a_2 < ...} has
property P then a_j / j tends to infinity. Source: van Doorn and Tao [vDTa25] (growth rates for
P and Q), per erdosproblems.com/1102, https://www.erdosproblems.com/1102; W. van Doorn and T.
Tao, Growth rates of sequences governed by the squarefree properties of its translates,
arXiv:2512.01087 (2025), https://arxiv.org/abs/2512.01087. Moved from
`OpenConjectures/NumberTheory/ErdosProblem1102`.
-/
public theorem_wanted densityZeroOfP_holds : densityZeroOfP

/--
Resolved true: All four formalized targets are proved by van Doorn and Tao (arXiv:2512.01087,
Theorems 1-3): every sequence with property P has density zero (densityZeroOfP), with the
density allowed to tend to zero arbitrarily slowly (arbitrarilySlowP); every sequence with
property Q has upper density at most 6/π^2 (upperDensityQ); and a squarefree sequence with
property Q has density exactly 6/π^2 (sharpDensityQ). erdosproblems.com/1102 (checked
2026-10-22) lists the problem as solved; whether 2^n ± 1 or n! ± 1 have property P is open there
and is not formalized (see gaps). This target holds: Theorem 1(ii): for any f : N -> N tending
to infinity there is an infinite sequence with property P and a_j / j <= f(j) for all j. Source:
van Doorn and Tao [vDTa25] (growth rates for P and Q), per erdosproblems.com/1102,
https://www.erdosproblems.com/1102; W. van Doorn and T. Tao, Growth rates of sequences governed
by the squarefree properties of its translates, arXiv:2512.01087 (2025),
https://arxiv.org/abs/2512.01087. Moved from `OpenConjectures/NumberTheory/ErdosProblem1102`.
-/
public theorem_wanted arbitrarilySlowP_holds : arbitrarilySlowP

/--
Resolved true: All four formalized targets are proved by van Doorn and Tao (arXiv:2512.01087,
Theorems 1-3): every sequence with property P has density zero (densityZeroOfP), with the
density allowed to tend to zero arbitrarily slowly (arbitrarilySlowP); every sequence with
property Q has upper density at most 6/π^2 (upperDensityQ); and a squarefree sequence with
property Q has density exactly 6/π^2 (sharpDensityQ). erdosproblems.com/1102 (checked
2026-10-22) lists the problem as solved; whether 2^n ± 1 or n! ± 1 have property P is open there
and is not formalized (see gaps). This target holds: Theorem 2: every sequence with property Q
has upper density at most 6/pi^2. Source: van Doorn and Tao [vDTa25] (growth rates for P and Q),
per erdosproblems.com/1102, https://www.erdosproblems.com/1102; W. van Doorn and T. Tao, Growth
rates of sequences governed by the squarefree properties of its translates, arXiv:2512.01087
(2025), https://arxiv.org/abs/2512.01087. Moved from
`OpenConjectures/NumberTheory/ErdosProblem1102`.
-/
public theorem_wanted upperDensityQ_holds : upperDensityQ

/--
Resolved true: All four formalized targets are proved by van Doorn and Tao (arXiv:2512.01087,
Theorems 1-3): every sequence with property P has density zero (densityZeroOfP), with the
density allowed to tend to zero arbitrarily slowly (arbitrarilySlowP); every sequence with
property Q has upper density at most 6/π^2 (upperDensityQ); and a squarefree sequence with
property Q has density exactly 6/π^2 (sharpDensityQ). erdosproblems.com/1102 (checked
2026-10-22) lists the problem as solved; whether 2^n ± 1 or n! ± 1 have property P is open there
and is not formalized (see gaps). This target holds: Theorem 3: there is an infinite sequence of
squarefree numbers with property Q and natural density 6/pi^2, i.e. a_j / j -> pi^2/6. Source:
van Doorn and Tao [vDTa25] (growth rates for P and Q), per erdosproblems.com/1102,
https://www.erdosproblems.com/1102; W. van Doorn and T. Tao, Growth rates of sequences governed
by the squarefree properties of its translates, arXiv:2512.01087 (2025),
https://arxiv.org/abs/2512.01087. Moved from `OpenConjectures/NumberTheory/ErdosProblem1102`.
-/
public theorem_wanted sharpDensityQ_holds : sharpDensityQ

end MathlibExt.NumberTheory.ErdosProblem1102Wanted
