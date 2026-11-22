/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Open sets of harmonic subseries triples (Erdős Problem 268)

Erdős Problem 268: let `X ⊆ ℝ³` be the set of points `(∑_{n ∈ A} 1/n, ∑_{n ∈ A} 1/(n + 1), ∑_{n ∈ A}
1/(n + 2))` as `A ⊆ ℕ` ranges over the infinite sets with `∑_{n ∈ A} 1/n < ∞`. Does `X` contain an
open set?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.HarmonicSubseriesTripleInteriorErdosProblem268Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #268, https://www.erdosproblems.com/268 (status PROVED
(LEAN)); P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory
(1980), p. 65. UnsolvedMath record UM-30006799 (`EP-268`), dataset ulamai/UnsolvedMath v1.8.0.

"Contains an open set" means a nonempty one (the empty set is open), i.e. `X` has nonempty interior
in `ℝ × ℝ × ℝ` (product topology, the Euclidean one). `A` is a set of positive integers.
formal-conjectures `ErdosProblems/268.lean` states every dimension `d` and allows `0 ∈ A` (which
only adds points); this module states the problem as posed (no code imported).
-/

/-- The point `(∑_{n ∈ A} 1/n, ∑_{n ∈ A} 1/(n + 1), ∑_{n ∈ A} 1/(n + 2))` of `ℝ³`. -/
noncomputable def harmonicTriple (A : Set ℕ) : ℝ × ℝ × ℝ :=
  (∑' n : A, (1 : ℝ) / (n : ℕ), ∑' n : A, (1 : ℝ) / ((n : ℕ) + 1),
    ∑' n : A, (1 : ℝ) / ((n : ℕ) + 2))

/-- Erdős Problem 268: the set of points `harmonicTriple A`, as `A` ranges over the infinite sets
of positive integers with `∑_{n ∈ A} 1/n < ∞`, contains a nonempty open set. -/
def harmonicTriplesHaveInterior : Prop :=
  (interior {x : ℝ × ℝ × ℝ | ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧
    Summable (fun n : A => (1 : ℝ) / (n : ℕ)) ∧ x = harmonicTriple A}).Nonempty

/--
Resolved true: Kovač constructed an explicit open ball inside `X`, and Kovač and Tao proved the
analogous statement in every dimension. erdosproblems.com/268 lists the problem as proved. Source:
T. F. Bloom, Erdős Problems, Problem #268, https://www.erdosproblems.com/268 (status PROVED (LEAN));
P. Erdős and R. L. Graham, Old and new problems and results in combinatorial number theory (1980),
p. 65; resolution: V. Kovač, On the set of points represented by harmonic subseries,
arXiv:2405.07681 (2024); V. Kovač and T. Tao, On several irrationality problems for Ahmes series,
arXiv:2406.17593 (2024), Kovač, abstract: the set of points (∑_{n∈A} 1/n, ∑_{n∈A} 1/(n+1), ∑_{n∈A}
1/(n+2)), A ranging over infinite sets of positive integers, has a non-empty interior; Kovač-Tao
extend this to all dimensions, https://arxiv.org/abs/2405.07681.
-/
public theorem_wanted harmonicTriplesHaveInterior_holds : harmonicTriplesHaveInterior

end MathlibExt.NumberTheory.HarmonicSubseriesTripleInteriorErdosProblem268Wanted
