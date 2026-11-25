/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Cycle.Type

@[expose] public section

namespace MetaMathlibExt

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- **Truncated-cycle successor.** Let $\sigma$ be a permutation of a finite linearly ordered
set $V$ and let $i, j \in V$. Then $j$ is the truncated-cycle successor $\sigma^{(i)}(i)$ of $i$
when $j$ is the first of the iterates $\sigma(i), \sigma^2(i), \dots$ that is at most $i$: there
is an $m > 0$ with $\sigma^m(i) = j$ and $j \le i$, and $\sigma^{m'}(i) > i$ for every $m'$ with
$0 < m' < m$. -/
def TruncatedSucc (σ : Equiv.Perm V) (i j : V) : Prop :=
  ∃ m : ℕ, 0 < m ∧ j ≤ i ∧ (σ ^ m) i = j ∧
    ∀ m' : ℕ, 0 < m' → m' < m → i < (σ ^ m') i

/-- **$k$-cyclic partition.** Let $V$ be a finite linearly ordered set, $\sigma$ a
permutation of $V$, $E$ a relation on $V$ (the directed edges of a labeled graph) and $k$ a
natural number. Then $\sigma$ is a $k$-cyclic partition for $E$ when $\sigma$ has exactly $k$
cycles, fixed points counted as cycles of length one, and for all $i, j \in V$, if $j$ is the
truncated-cycle successor of $i$ under $\sigma$ (the first of $\sigma(i), \sigma^2(i), \dots$
that is at most $i$), then $E(i, j)$ does not hold.

Source: JIS statement `jis_758fa72fca5bb19057a27c73` in Gonzales,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Gonzales/gonzales2.tex>, lines 345–346,
SHA-256 `2d78a778c999aa0af889445a63ee690bb3a5d3ac741b6beb0b777654e1f4a627`. -/
def IsKCyclicPartition (σ : Equiv.Perm V) (edge : V → V → Prop) (k : ℕ) : Prop :=
  σ.cycleType.card + (Fintype.card V - σ.support.card) = k ∧
    ∀ i j : V, TruncatedSucc σ i j → ¬ edge i j

end MetaMathlibExt

end
