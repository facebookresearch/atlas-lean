/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 31
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.Data.Set.Density

@[expose] public section

open Filter
open scoped Pointwise

namespace MathlibExt.NumberTheory.ErdosProblem31Wanted

/-! Source record `FC-ErdosProblem31`, ported from FormalConjectures
`ErdosProblems/31.lean` (`theorem erdos_31`) and checked against
erdosproblems.com/31. Proved by Lorentz. -/

def conjecture : Prop :=
  ∀ A : Set ℕ, A.Infinite →
    ∃ B : Set ℕ, B.HasDensity 0 ∧ ∀ᶠ n in atTop, n ∈ A + B

/-- **Lorentz's theorem on additive complements (Erdős Problem 31).** For every infinite set
$A$ of natural numbers there is a set $B$ of natural numbers of natural density $0$ such that
every sufficiently large natural number lies in $A + B = \{a + b \mid a \in A,\ b \in B\}$.

Resolved true: Proved by Lorentz [Lo54]. Source: George G. Lorentz, On a problem of additive
number theory, Proceedings of the American Mathematical Society 5 (1954), 838–841,
https://doi.org/10.1090/s0002-9939-1954-0063389-3. Moved from
`OpenConjectures/NumberTheory/ErdosProblem31`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem31Wanted
