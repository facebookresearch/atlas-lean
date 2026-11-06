/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 822
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Basic
public import MathlibExt.Data.Set.Density

@[expose] public section

open Filter
open scoped Topology

namespace MathlibExt.NumberTheory.ErdosProblem822Wanted

/-! Source record `FC-ErdosProblem822`, ported from FormalConjectures
`ErdosProblems/822.lean` and checked against erdosproblems.com/822.
`Set.partialDensity` and `Set.lowerDensity` are reused from `MathlibExt.Data.Set.Density`. The
upstream `answer(True)` is dropped. Status: resolved true ([GIL24]). -/

/-- **Erdős Problem 822.** The statement that the set $\{n + \varphi(n) : n \in \mathbb{N}\}$,
where $\varphi$ is Euler's totient function, has positive lower density in $\mathbb{N}$. -/
def conjecture : Prop :=
  0 < (Set.range fun n => n + Nat.totient n).lowerDensity

/--
**Erdős Problem 822 is true.** The set $\{n + \varphi(n) : n \in \mathbb{N}\}$, where $\varphi$
is Euler's totient function, has positive lower density in $\mathbb{N}$.

Source: M. R.
Gabdullin, V. V. Iudelevich, and F. Luca, Numbers of the form k + f(k), Journal of Number Theory
262 (2024), 58–85, https://doi.org/10.1016/j.jnt.2024.03.010. Moved from
`OpenConjectures/NumberTheory/ErdosProblem822`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem822Wanted
