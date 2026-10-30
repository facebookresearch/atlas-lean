/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Probability.ScottishBook38Wanted

/-- Reachability by a chain of friends in a `k`-out assignment `c`: there is a
finite chain of people from `a` to `b` in which consecutive people are joined
by a friendship in either direction. -/
def KOutReachable (N : ℕ) (c : Fin N → Finset (Fin N)) (a b : Fin N) : Prop :=
  ∃ m : ℕ, ∃ p : Fin (m + 1) → Fin N,
    p 0 = a ∧ p (Fin.last m) = b ∧
      ∀ i : Fin m, p (Fin.castSucc i) ∈ c (p (Fin.succ i)) ∨
        p (Fin.succ i) ∈ c (p (Fin.castSucc i))

/-- The assignment `c` connects all `N` people: every person can reach every
other by a chain of friends. -/
def KOutConnected (N : ℕ) (c : Fin N → Finset (Fin N)) : Prop :=
  ∀ a b : Fin N, KOutReachable N c a b

/-- `P_{kN}`: the proportion of assignments in which each of the `N` people is
assigned exactly `k` others as friends (never oneself) that connect all `N`
people. -/
noncomputable def KOutConnectedProb (k N : ℕ) : ℝ :=
  (Set.ncard { c : Fin N → Finset (Fin N) |
    (∀ i, (c i).card = k ∧ i ∉ c i) ∧ KOutConnected N c } : ℝ) /
  (Set.ncard { c : Fin N → Finset (Fin N) |
    ∀ i, (c i).card = k ∧ i ∉ c i } : ℝ)

/--
Ulam, Problem 38 of the Scottish Book. Original question: `N` people are
given, each person is assigned `k` others at random as friends, friendship
need not be symmetric; what is the chance `P_{kN}` that, starting from any
person, one can reach every other person by a chain of mutual friends, and
what is the limit of `P_{kN}` as `N` tends to infinity, `0` or `1`? The
answer: the limit is `1` for `k ≥ 2` and `0` for `k = 1`. The model used
here is the `k`-out model: each person chooses an ordered `k`-set of friends,
and two people are joined when either one chose the other, so a chain of
friends is a path in the underlying undirected graph.
Source: S. Ulam, Problem 38 of the Scottish Book; the symmetric case was
solved by Erdős for `k ≥ 2`, and D. S. Jungreis gave a detailed general
solution; see the commentary in R. D. Mauldin (ed.), The Scottish Book,
2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted k_out_connectivity_threshold :
    (∀ k : ℕ, 2 ≤ k →
      Filter.Tendsto (fun N => KOutConnectedProb k N) Filter.atTop (nhds 1)) ∧
    Filter.Tendsto (fun N => KOutConnectedProb 1 N) Filter.atTop (nhds 0)

end MathlibExt.Probability.ScottishBook38Wanted
