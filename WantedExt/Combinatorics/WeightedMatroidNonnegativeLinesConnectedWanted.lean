/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source record `OWR-2090-021`
# Connectivity of non-negative points through non-negative lines in weighted rank-3 matroids

Discrete Geometry (2009), Oberwolfach Reports, DOI 10.4171/owr/2008/44, pp. 2477--2556.
-/
module

public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Combinatorics.Matroid.Closure
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.WeightedMatroidNonnegativeLinesConnectedWanted

/-- `M` is simple: every set of at most two elements is independent (no loops, no parallel
pairs). -/
def IsSimpleMatroid {n : ℕ} (M : Matroid (Fin n)) : Prop := ∀ e f, M.Indep {e, f}

/-- `L` is a line of the matroid: a flat of rank `2`. -/
def IsLine {n : ℕ} (M : Matroid (Fin n)) (L : Set (Fin n)) : Prop := M.IsFlat L ∧ M.eRk L = 2

open Classical in
/-- The weight of a set of points. -/
noncomputable def weight {n : ℕ} (a : Fin n → ℝ) (S : Set (Fin n)) : ℝ :=
  ∑ i ∈ Finset.univ.filter (· ∈ S), a i

open Classical in
/-- The graph on the points of non-negative weight in which two points are adjacent when some line
of non-negative weight contains both. -/
def nonnegGraph {n : ℕ} (M : Matroid (Fin n)) (a : Fin n → ℝ) :
    SimpleGraph {i : Fin n // 0 ≤ a i} :=
  SimpleGraph.fromRel fun i j =>
    ∃ L, IsLine M L ∧ 0 ≤ weight a L ∧ (i : Fin n) ∈ L ∧ (j : Fin n) ∈ L

/-- The rank-`3` question: in a simple rank-`3` matroid on `n` points with real weights of
non-negative total, the points of non-negative weight are connected through the lines of
non-negative weight. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)) (a : Fin n → ℝ), IsSimpleMatroid M → M.eRank = 3 →
    M.E = Set.univ →
    0 ≤ ∑ i, a i → (nonnegGraph M a).Connected

-- Carried source audit `OWR-2090-021` (see the Moved/ record).

/--
Resolved true: Resolved (true) for the formalized rank-3 question: for a generic weight and t ≤
min{0, total weight}, the proper flats of weight greater than t form an (r − 3)-connected poset
(Adiprasito–Björner, arXiv:1401.7301, Theorem 2.1, settling the Mikhalkin–Ziegler conjecture);
for r = 3, a small generic perturbation with t slightly below 0 gives the connectivity of the
non-negative points through non-negative lines. Shellability in the omitted rank-r part is open
(their Open Problem 3.2). Source: K. A. Adiprasito, A. Björner, Filtered geometric lattices and
Lefschetz section theorems over the tropical semiring, arXiv:1401.7301,
https://arxiv.org/abs/1401.7301. Moved from
`OpenConjectures/Combinatorics/WeightedMatroidNonnegativeLinesConnected`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.WeightedMatroidNonnegativeLinesConnectedWanted
