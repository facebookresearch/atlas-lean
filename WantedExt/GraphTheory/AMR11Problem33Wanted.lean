/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AMR 11 Question 33: return-probability gap for Cayley graphs
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Basic

open scoped BigOperators

@[expose] public section

namespace MathlibExt.GraphTheory.AMR11Problem33Wanted

/-! Source record `AMR-011-0033`. -/

namespace AMR11Q33

universe u

/-!
# Clause inventory for [AMR-011-0033] Some Questions — Question 33

- `k` is a natural number with `1 < k`.
- `G` is a group (Cayley graph over a group).
- `gen : Finset G` is the finite generating set.
- Symmetry: `s ∈ gen` implies `s⁻¹ ∈ gen`.
- `1 ∉ gen`.
- Generation (connectedness): every `g : G` is `l.prod` for some `l : List G`
  with all entries in `gen`.
- `k`-regularity: `gen.card = k`.
- Words of length `n` over `gen`, as `Fin n → ↥Γ.gen`.
- Word evaluation via `(List.ofFn fun i => (w i : G)).prod`.
- First-return words: product equals `1` with no shorter nonempty prefix
  product equal to `1`.
- First-return probability at time `n`: card of first-return words divided
  by `(k : ℝ) ^ n` (`0` when `n = 0`).
- Return probability: `∑' n, firstReturnProb Γ n`.
- Transient: `returnProb Γ < 1`.
- `C : ℝ` depends only on `k` and satisfies `C < 1`.
- Uniform bound: every transient graph satisfies `returnProb Γ ≤ C`.
-/

/-- **Regular Cayley graph.** For a group $G$ and a natural number $k$, the data of a $k$-regular
Cayley graph on $G$ is a finite set $S \subseteq G$ of generators such that $S$ is closed under
inverses ($s \in S$ implies $s^{-1} \in S$), the identity $1$ does not belong to $S$, every
element of $G$ is the product of a finite (possibly empty) list of elements of $S$, and $S$ has
exactly $k$ elements. -/
structure RegularCayleyGraph (G : Type u) [Group G] [DecidableEq G]
    (k : ℕ) where
  gen : Finset G
  symm_mem : ∀ s ∈ gen, s⁻¹ ∈ gen
  one_not_mem : (1 : G) ∉ gen
  connected : ∀ g : G, ∃ l : List G, (∀ s ∈ l, s ∈ gen) ∧ l.prod = g
  regular : gen.card = k

/-- **First-return probability.** Let $\Gamma$ be a $k$-regular Cayley graph on a group $G$ with
generating set $S$. For $n \ge 1$, the first-return probability of $\Gamma$ at time $n$ is the
real number obtained by dividing by $k^n$ the number of words $(s_1, \dots, s_n) \in S^n$ with
$s_1 s_2 \cdots s_n = 1$ and $s_1 \cdots s_m \ne 1$ for every $0 < m < n$; at time $n = 0$ it
is $0$.

Since $S$ has $k$ elements, this is the probability that the walk $1, s_1, s_1 s_2, \dots$ with
independent uniform steps in $S$ is back at $1$ for the first time at step $n$. -/
noncomputable def firstReturnProb {G : Type u} [Group G]
    [DecidableEq G] {k : ℕ} (Γ : RegularCayleyGraph G k) (n : ℕ) : ℝ := by
  classical
  exact if 0 < n then
    (Fintype.card
      { w : Fin n → Γ.gen //
        (List.ofFn fun i => (w i : G)).prod = 1 ∧
        ∀ (m : ℕ) (hm : m ∈ Finset.range n), 0 < m →
          (List.ofFn fun (i : Fin m) =>
            (w (Fin.castLE (Nat.le_of_lt (Finset.mem_range.mp hm)) i) : G)).prod ≠
            1 } : ℝ) / (k : ℝ) ^ n
    else 0

/-- **Return probability.** The return probability of a $k$-regular Cayley graph $\Gamma$ is the
sum $\sum_{n \ge 0} p_n$, where $p_n$ is the first-return probability of $\Gamma$ at time $n$.

It is the probability that simple random walk on $\Gamma$ started at the identity ever returns
to the identity. -/
noncomputable def returnProb {G : Type u} [Group G] [DecidableEq G]
    {k : ℕ} (Γ : RegularCayleyGraph G k) : ℝ :=
  ∑' n, firstReturnProb Γ n

/-- **Uniform return-probability gap.** The statement that for every natural number $k > 1$ there
is a real number $C < 1$ such that for every group $G$ and every $k$-regular Cayley graph
$\Gamma$ on $G$, if the return probability of $\Gamma$ is less than $1$ (that is, $\Gamma$ is
transient), then it is at most $C$. -/
def returnProbUniformGap : Prop :=
  ∀ (k : ℕ), 1 < k →
    ∃ C : ℝ, C < 1 ∧
      ∀ (G : Type u) [Group G] [DecidableEq G]
        (Γ : RegularCayleyGraph G k),
        returnProb Γ < 1 → returnProb Γ ≤ C

end AMR11Q33

/--
**Uniform return-probability gap for transient Cayley graphs.** For every natural number
$k > 1$ there is a real number $C < 1$ such that for every group $G$ and every $k$-regular Cayley
graph $\Gamma$ on $G$ whose return probability is less than $1$, the return probability of
$\Gamma$ is at most $C$.

This follows from Tessera and Tointon, Corollary 1.3: there is a universal $c > 0$ such that
simple random walk on every connected, locally finite, vertex-transitive graph is recurrent or
escapes with probability at least $c$, so $C = 1 - c$ works for every $k$.

Source: Romain Tessera and Matthew Tointon, Sharp relations between
volume growth, isoperimetry and escape probability in vertex-transitive graphs, arXiv preprint
(2020, v2 2024), arXiv:2001.01467, https://arxiv.org/abs/2001.01467. Moved from
`OpenConjectures/GraphTheory/AMR11Problem33`.
-/
public theorem_wanted returnProbUniformGap_holds : AMR11Q33.returnProbUniformGap

end MathlibExt.GraphTheory.AMR11Problem33Wanted
