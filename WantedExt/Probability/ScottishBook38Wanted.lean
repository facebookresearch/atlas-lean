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

/-- **Reachability by a chain of friends.** Let $c$ assign to each person $i$ among $N$ people a
set $c(i)$ of people, the friends of $i$. A person $b$ is reachable from a person $a$ if there are
$m \ge 0$ and people $p_0 = a, p_1, \dots, p_m = b$ such that for each $j < m$, $p_j$ is a friend
of $p_{j+1}$ or $p_{j+1}$ is a friend of $p_j$. -/
def KOutReachable (N : ℕ) (c : Fin N → Finset (Fin N)) (a b : Fin N) : Prop :=
  ∃ m : ℕ, ∃ p : Fin (m + 1) → Fin N,
    p 0 = a ∧ p (Fin.last m) = b ∧
      ∀ i : Fin m, p (Fin.castSucc i) ∈ c (p (Fin.succ i)) ∨
        p (Fin.succ i) ∈ c (p (Fin.castSucc i))

/-- **Assignments that connect everyone.** Let $c$ assign to each person $i$ among $N$ people a
set $c(i)$ of people, the friends of $i$. The assignment $c$ connects all $N$ people when, for
all people $a$ and $b$, there are $m \ge 0$ and people $p_0 = a, p_1, \dots, p_m = b$ such that
for each $j < m$, $p_j$ is a friend of $p_{j+1}$ or $p_{j+1}$ is a friend of $p_j$. -/
def KOutConnected (N : ℕ) (c : Fin N → Finset (Fin N)) : Prop :=
  ∀ a b : Fin N, KOutReachable N c a b

/-- **Probability that a random $k$-out assignment connects everyone.** For natural numbers $k$
and $N$, $P_{kN}$ is the number of assignments that give each of $N$ people a set of exactly $k$
friends other than themselves and connect all $N$ people, divided by the number of all
assignments that give each person a set of exactly $k$ friends other than themselves. When there
is no such assignment, $P_{kN} = 0$. -/
noncomputable def KOutConnectedProb (k N : ℕ) : ℝ :=
  (Set.ncard { c : Fin N → Finset (Fin N) |
    (∀ i, (c i).card = k ∧ i ∉ c i) ∧ KOutConnected N c } : ℝ) /
  (Set.ncard { c : Fin N → Finset (Fin N) |
    ∀ i, (c i).card = k ∧ i ∉ c i } : ℝ)

/--
**Connectivity threshold for random $k$-out friendship graphs.** For natural numbers $k$ and $N$,
let $P_{kN}$ be the proportion of the assignments giving each of $N$ people exactly $k$ friends
other than themselves that connect all $N$ people. Then $P_{kN} \to 1$ as $N \to \infty$ for
every $k \ge 2$, and $P_{1N} \to 0$ as $N \to \infty$.

Friendship need not be symmetric: two people are joined when either one chose the other, so a
chain of friends is a path in the underlying undirected graph. Ulam asked for $P_{kN}$ and for
its limit as $N \to \infty$, $0$ or $1$.

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
