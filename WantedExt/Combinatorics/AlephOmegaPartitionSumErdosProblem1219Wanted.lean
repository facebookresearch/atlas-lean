/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A partition relation for sums of increasing powers of two (Erdős Problem 1219)

Erdős Problem 1219: let `(nₖ)` be an increasing sequence of integers such that `2^{ℵ_{nₖ}}` is
strictly increasing and `2^{ℵ_{n₀}} > ℵ_ω`. Is it true that `∑ₖ 2^{ℵ_{nₖ}} → (ℵ_ω)²`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

namespace MathlibExt.Combinatorics.AlephOmegaPartitionSumErdosProblem1219Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1219, https://www.erdosproblems.com/1219 (status
PROVED). UnsolvedMath record UM-30007260 (`EP-1219`), dataset ulamai/UnsolvedMath v1.8.0.

The arrow is the Erdős-Rado partition relation for pairs with two colours: every symmetric
two-colouring of the pairs of a set of cardinality `∑ₖ 2^{ℵ_{nₖ}}` (a cardinal sum) has a
homogeneous set of cardinality `ℵ_ω`. Cardinals are in `Cardinal.{0}`. Compared with the
formal-conjectures statement `ErdosProblems/1219.lean` (equivalent; no code imported).
-/

open Cardinal

/-- **Partition relation for pairs with two colours.** For cardinals $\kappa$ and $\mu$, the
relation $\kappa \to (\mu)^2_2$ holds if for every set $X$ of cardinality $\kappa$ and every
symmetric colouring $c$ of the ordered pairs of elements of $X$ with two colours, there are a
subset $H \subseteq X$ of cardinality $\mu$ and a colour $b$ such that $c(x, y) = b$ for all
distinct $x, y \in H$. -/
def ArrowsPairs (κ μ : Cardinal.{0}) : Prop :=
  ∀ (α : Type), #α = κ → ∀ c : α → α → Bool, (∀ x y, c x y = c y x) →
    ∃ H : Set α, #H = μ ∧ ∃ b : Bool, ∀ x ∈ H, ∀ y ∈ H, x ≠ y → c x y = b

/-- **Erdős Problem 1219: a partition relation for sums of powers of two.** The statement that for
every strictly increasing sequence $n_0 < n_1 < \cdots$ of natural numbers such that the cardinals
$2^{\aleph_{n_k}}$ are strictly increasing in $k$ and $2^{\aleph_{n_0}} > \aleph_\omega$, the
partition relation $\sum_k 2^{\aleph_{n_k}} \to (\aleph_\omega)^2_2$ holds: for every set $X$ of
cardinality $\sum_k 2^{\aleph_{n_k}}$ and every symmetric colouring of the pairs of elements of $X$
with two colours, some subset of $X$ of cardinality $\aleph_\omega$ has all pairs of distinct
elements of the same colour. -/
def alephOmegaPartitionOfCardinalSum : Prop :=
  ∀ n : ℕ → ℕ, StrictMono n → StrictMono (fun k => (2 : Cardinal.{0}) ^ ℵ_ (n k)) →
    ℵ_ Ordinal.omega0 < (2 : Cardinal.{0}) ^ ℵ_ (n 0) →
      ArrowsPairs (Cardinal.sum fun k : ℕ => (2 : Cardinal.{0}) ^ ℵ_ (n k)) (ℵ_ Ordinal.omega0)

/--
**Shelah's theorem (Erdős Problem 1219).** For every strictly increasing sequence
$n_0 < n_1 < \cdots$ of natural numbers such that the cardinals $2^{\aleph_{n_k}}$ are strictly
increasing in $k$ and $2^{\aleph_{n_0}} > \aleph_\omega$, the partition relation
$\sum_k 2^{\aleph_{n_k}} \to (\aleph_\omega)^2_2$ holds: for every set $X$ of cardinality
$\sum_k 2^{\aleph_{n_k}}$ and every symmetric colouring of the pairs of elements of $X$ with two
colours, some subset of $X$ of cardinality $\aleph_\omega$ has all pairs of distinct elements of
the same colour.

Source: T. F. Bloom, Erdős Problems, Problem
#1219, https://www.erdosproblems.com/1219 (status PROVED); resolution: S. Shelah, Notes on partition
calculus, in Infinite and Finite Sets (Colloq. Keszthely, 1973), Colloq. Math. Soc. János Bolyai 10,
North-Holland (1975), 1257-1276, erdosproblems.com/1219: proved by Shelah (a problem of Erdős,
Hajnal and Rado; P. Komjáth, The Erdős-Hajnal problem list, Bull. Symb. Log. (2025), p. 2).
-/
public theorem_wanted alephOmegaPartitionOfCardinalSum_holds : alephOmegaPartitionOfCardinalSum

end MathlibExt.Combinatorics.AlephOmegaPartitionSumErdosProblem1219Wanted
