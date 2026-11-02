/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Stable series of groups of linear automorphisms

Shared definition for the Kourovka Notebook entries on stable groups of automorphisms of a vector
space (Problems 2.58, 2.61 and 2.63): a set of linear automorphisms of `V` is stable when it
stabilizes a finite chain of subspaces from `0` to `V`, acting trivially on each factor.
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.DFinsupp

@[expose] public section

namespace MathlibExt.GroupTheory.StableSeriesShared

/-- **Stable sets of linear automorphisms.** Let $V$ be a vector space over a field $K$. A set $S$
of $K$-linear automorphisms of $V$ is stable when there are a natural number $m$ and subspaces
$0 = W_0 \le W_1 \le \cdots \le W_m = V$ of $V$ such that $g(w) - w \in W_i$ for every $i < m$,
every $g \in S$ and every $w \in W_{i+1}$. -/
def HasStableSeries {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (S : Set (V ≃ₗ[K] V)) : Prop :=
  ∃ (m : ℕ) (W : Fin (m + 1) → Submodule K V), W 0 = ⊥ ∧ W (Fin.last m) = ⊤ ∧
    (∀ i : Fin m, W i.castSucc ≤ W i.succ) ∧
    ∀ i : Fin m, ∀ g ∈ S, ∀ w ∈ W i.succ, g w - w ∈ W i.castSucc

end MathlibExt.GroupTheory.StableSeriesShared
