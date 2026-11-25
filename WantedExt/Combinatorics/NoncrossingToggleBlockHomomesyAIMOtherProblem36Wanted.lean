/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Block-count homomesy for toggling noncrossing partitions (AIM dynamical combinatorics, Conj. 5.8)

AIM workshop Dynamical algebraic combinatorics, pre-workshop document, §5.4, Conjecture 5.8: for a
noncrossing partition of `{1, …, n}` and `i < j`, the toggle `τ_{i,j}` splits a block at consecutive
elements `i, j`, merges a block ending at `i` with one starting at `j` when the result is
noncrossing, and otherwise does nothing; `σ` toggles successively at `(1,2), (2,3), …, (n-1,n),
(1,3), …, (n-2,n), …, (1,n)`. The number of blocks is homomesic under `σ` with average `(n + 1)/2`
on each orbit.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MathlibExt.Combinatorics.NoncrossingToggleBlockHomomesyAIMOtherProblem36Wanted

/-!
Source: AIM workshop Dynamical algebraic combinatorics, pre-workshop document,
http://aimath.org/pastworkshops/dac_preworkshop.pdf, §5.4, Conjecture 5.8. UnsolvedMath record
UM-20003229 (`AIM-OTHER-0036`), dataset ulamai/UnsolvedMath v1.8.0.

A noncrossing partition is its linear representation (Einstein et al., §1): the arcs `(i, j)`, `i <
j`, joining successive elements of a block, with no two arcs crossing or sharing a left or a right
endpoint; it has `n - #arcs` blocks. The toggle at `(i, j)` removes the arc if present and otherwise
adds it when the result is again such a representation, which is the list's split/merge rule.
Homomesy is stated through periods: whenever `σ^L P = P`, `L ≥ 1`, the block counts of `P, …,
σ^{L-1} P` sum to `L (n + 1)/2`. `n ≥ 1`: for `n = 0` the empty partition has `0` blocks. A
computation of `σ` for `n ≤ 8` reproduces the orbit sizes the document lists (`14 = 14`, `42 = 15 +
13 + 5 + 3 + 3 + 3`, …, `1430 = 1240 + 144 + 32 + 8 + 6`). The UnsolvedMath record restates `σ` as
Kreweras complementation; the document's `σ` is the toggle composite above, and the statement
follows the document. MathlibExt's `NoncrossingPartition` (finpartitions of `Fin n`) is not used
because the toggles act on arcs; the linear representations are in bijection with `NC(n)` (Einstein
et al., §1).
-/

/-- **Arc sets.** For a natural number $n$, an arc set on $n$ points is a finite set of ordered
pairs $(i, j)$, called arcs, with $i, j \in \{0, 1, \dots, n - 1\}$. -/
abbrev ArcSet (n : ℕ) := Finset (Fin n × Fin n)

/-- **Noncrossing arc sets.** An arc set $P$ on $n$ points is noncrossing when every arc
$(i, j) \in P$ has $i < j$ and any two distinct arcs $(i, j)$ and $(k, l)$ of $P$ satisfy
$i \ne k$, $j \ne l$, and not $i < k < j < l$. So distinct arcs do not cross and share
neither a left nor a right endpoint.

These arc sets are the linear representations of the noncrossing partitions of
$\{0, 1, \dots, n - 1\}$, in which the arcs join consecutive elements of each block. -/
def IsNoncrossingArcSet {n : ℕ} (P : ArcSet n) : Prop :=
  (∀ a ∈ P, a.1 < a.2) ∧
    ∀ a ∈ P, ∀ b ∈ P, a ≠ b → ¬ (a.1 < b.1 ∧ b.1 < a.2 ∧ a.2 < b.2) ∧ a.1 ≠ b.1 ∧ a.2 ≠ b.2

open Classical in
/-- **Toggle at an arc.** For an arc $a = (i, j)$ and an arc set $P$ on $n$ points, the toggle
$\tau_{i,j}$ sends $P$ to $P \setminus \{a\}$ if $a \in P$; otherwise to $P \cup \{a\}$ if
$P \cup \{a\}$ is a noncrossing arc set; and otherwise it leaves $P$ unchanged. -/
noncomputable def toggle {n : ℕ} (a : Fin n × Fin n) (P : ArcSet n) : ArcSet n :=
  if a ∈ P then P.erase a else if IsNoncrossingArcSet (insert a P) then insert a P else P

/-- **Toggle order.** For a natural number $n$, the toggle order on $n$ points is the list of all
arcs $(i, i + d)$ with $d \ge 1$, $i \ge 0$ and $i + d \le n - 1$, ordered by length
$d = 1, \dots, n - 1$ and, for each length, by increasing left endpoint $i$. In $1$-indexed form it
is $(1,2), (2,3), \dots, (n-1,n), (1,3), \dots, (n-2,n), \dots, (1,n)$. -/
def toggleOrder (n : ℕ) : List (Fin n × Fin n) :=
  (List.range n).tail.flatMap fun d =>
    (List.finRange n).filterMap fun i =>
      if h : i.val + d < n then some (i, ⟨i.val + d, h⟩) else none

/-- **Toggle composite.** The toggle composite $\sigma$ on $n$ points sends an arc set $P$ on $n$
points to the arc set obtained from $P$ by applying the toggles $\tau_{i,j}$ at the arcs
$(i, j)$ of the toggle order on $n$ points one after another, in the order of that list. -/
noncomputable def toggleComposite (n : ℕ) (P : ArcSet n) : ArcSet n :=
  (toggleOrder n).foldl (fun Q a => toggle a Q) P

/-- **Block count.** The block count of an arc set $P$ on $n$ points is $n - |P|$, where the
subtraction is truncated at $0$.

When $P$ is a noncrossing arc set, this is the number of blocks of the noncrossing partition whose
linear representation is $P$. -/
def blockCount {n : ℕ} (P : ArcSet n) : ℕ :=
  n - P.card

/-- **Block-count homomesy claim for toggling noncrossing partitions.** Let $\sigma_n$ be the
toggle composite on $n$ points and $\sigma_n^k$ its $k$-fold iterate. The claim states that for
every $n \ge 1$, every noncrossing arc set $P$ on $n$ points and every $L \ge 1$ with
$\sigma_n^L(P) = P$, twice the sum of the block counts of
$P, \sigma_n(P), \dots, \sigma_n^{L-1}(P)$ equals $L(n + 1)$. That is, the number of blocks is
homomesic under $\sigma_n$ with average $(n + 1)/2$.

Source: AIM workshop Dynamical algebraic combinatorics, pre-workshop document, §5.4,
Conjecture 5.8. -/
def noncrossingToggleBlockHomomesy : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ P : ArcSet n, IsNoncrossingArcSet P → ∀ L : ℕ, 1 ≤ L →
    (toggleComposite n)^[L] P = P →
      2 * ∑ k ∈ Finset.range L, blockCount ((toggleComposite n)^[k] P) = L * (n + 1)

/--
**Block-count homomesy for toggling noncrossing partitions.** The block-count homomesy claim
holds: with $\sigma_n$ the toggle composite on $n$ points and $\sigma_n^k$ its $k$-fold iterate,
for every $n \ge 1$, every noncrossing arc set $P$ on $n$ points and every $L \ge 1$ with
$\sigma_n^L(P) = P$, twice the sum of the block counts of
$P, \sigma_n(P), \dots, \sigma_n^{L-1}(P)$ equals $L(n + 1)$.

Source: AIM workshop Dynamical algebraic combinatorics, pre-workshop document,
http://aimath.org/pastworkshops/dac_preworkshop.pdf, §5.4, Conjecture 5.8; resolution: D. Einstein,
M. Farber, E. Gunawan, M. Joseph, M. Macauley, J. Propp and S. Rubinstein-Salzedo, Noncrossing
partitions, toggles, and homomesies, Electron. J. Combin. 23 (2016), no. 3, Paper 3.52,
arXiv:1510.06362, Theorem 4.5 and Corollary 4.7: for every partial Coxeter element w of the toggle
group (each toggle τ_{i,j} at most once) containing every τ_{i,i+1}, in particular every Coxeter
element, the block count β is (n + 1)/2-mesic on NC(n); σ toggles every arc exactly once,
https://doi.org/10.37236/5648.
-/
public theorem_wanted noncrossingToggleBlockHomomesy_holds : noncrossingToggleBlockHomomesy

end MathlibExt.Combinatorics.NoncrossingToggleBlockHomomesyAIMOtherProblem36Wanted
