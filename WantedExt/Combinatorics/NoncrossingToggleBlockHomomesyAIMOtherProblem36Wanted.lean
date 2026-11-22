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

/-- A set of arcs `(i, j)` on the points `Fin n`. -/
abbrev ArcSet (n : ℕ) := Finset (Fin n × Fin n)

/-- `P` is the linear representation of a noncrossing partition of `Fin n`: every arc `(i, j)` has
`i < j`, and no two distinct arcs cross (`i < k < j < l`), share a left endpoint or share a right
endpoint. -/
def IsNoncrossingArcSet {n : ℕ} (P : ArcSet n) : Prop :=
  (∀ a ∈ P, a.1 < a.2) ∧
    ∀ a ∈ P, ∀ b ∈ P, a ≠ b → ¬ (a.1 < b.1 ∧ b.1 < a.2 ∧ a.2 < b.2) ∧ a.1 ≠ b.1 ∧ a.2 ≠ b.2

open Classical in
/-- The toggle `τ_{i,j}` at the arc `a = (i, j)`: remove `a` if it is present, otherwise add it
when the result is again the linear representation of a noncrossing partition, and otherwise do
nothing. -/
noncomputable def toggle {n : ℕ} (a : Fin n × Fin n) (P : ArcSet n) : ArcSet n :=
  if a ∈ P then P.erase a else if IsNoncrossingArcSet (insert a P) then insert a P else P

/-- The arcs `(i, i + d)` ordered by length `d = 1, …, n - 1` and then by left endpoint: in
`1`-indexed form `(1,2), (2,3), …, (n-1,n), (1,3), …, (n-2,n), …, (1,n)`. -/
def toggleOrder (n : ℕ) : List (Fin n × Fin n) :=
  (List.range n).tail.flatMap fun d =>
    (List.finRange n).filterMap fun i =>
      if h : i.val + d < n then some (i, ⟨i.val + d, h⟩) else none

/-- The composite `σ` of the toggles in `toggleOrder n`, applied successively (first arc first). -/
noncomputable def toggleComposite (n : ℕ) (P : ArcSet n) : ArcSet n :=
  (toggleOrder n).foldl (fun Q a => toggle a Q) P

/-- The number of blocks `n - |P|` of the noncrossing partition with linear representation `P`. -/
def blockCount {n : ℕ} (P : ArcSet n) : ℕ :=
  n - P.card

/-- AIM Dynamical algebraic combinatorics, Conjecture 5.8, as a claim: for `n ≥ 1` the number of
blocks is homomesic under `σ` with average `(n + 1)/2`: whenever `σ^L P = P` with `L ≥ 1`, the
block counts of `P, σ P, …, σ^{L-1} P` sum to `L (n + 1) / 2`. -/
def noncrossingToggleBlockHomomesy : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ P : ArcSet n, IsNoncrossingArcSet P → ∀ L : ℕ, 1 ≤ L →
    (toggleComposite n)^[L] P = P →
      2 * ∑ k ∈ Finset.range L, blockCount ((toggleComposite n)^[k] P) = L * (n + 1)

/--
Resolved true: Einstein, Farber, Gunawan, Joseph, Macauley, Propp and Rubinstein-Salzedo proved that
the number of blocks is `(n + 1)/2`-mesic on noncrossing partitions under every composite of toggles
that uses each toggle at most once and contains every `τ_{i,i+1}` (Theorem 4.5), which covers the
list's `σ`. Source: AIM workshop Dynamical algebraic combinatorics, pre-workshop document,
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
