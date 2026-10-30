/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Distinguishing sets for subdegree-finite permutation groups (Kourovka Notebook Problem 19.89)

Kourovka Notebook, Problem 19.89 (S. M. Smith), marked solved in the 21st issue: let `Ω` be
countably infinite and `G` a closed, subdegree-finite subgroup of `Sym(Ω)` (every orbit of every
point stabiliser is finite), with the topology of pointwise convergence. Conjecture: if the minimal
degree of `G` is infinite, then some subset of `Ω` has trivial setwise stabiliser in `G`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import MathlibExt.GroupTheory.Permutation.PointwiseTopology

@[expose] public section

namespace MathlibExt.GroupTheory.SubdegreeFiniteDistinguishingSetKourovka19Problem89Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.89 (S. M. Smith). UnsolvedMath record
UM-00701637 (`KOU-19.89`), dataset ulamai/UnsolvedMath v1.8.0.

Closedness uses MathlibExt's `Equiv.Perm.pointwiseTopology` (induced from `Ω → Ω` with `Ω`
discrete). The minimal degree is infinite when every non-identity element moves infinitely many
points; the setwise stabiliser of `X` is `{g ∈ G | g '' X = X}`.
-/

/-- Kourovka 19.89 (S. M. Smith), conjecture: let `Ω` be countably infinite and `G ≤ Sym(Ω)` closed
in the topology of pointwise convergence and subdegree-finite (every orbit of every point
stabilizer is finite). If the minimal degree of `G` is infinite (every non-identity element moves
infinitely many points), then some subset of `Ω` has trivial setwise stabilizer in `G`. -/
def closedSubdegreeFiniteDistinguishingSet : Prop :=
  ∀ (Ω : Type) [Countable Ω] [Infinite Ω] (G : Subgroup (Equiv.Perm Ω)),
    @IsClosed _ Equiv.Perm.pointwiseTopology (G : Set (Equiv.Perm Ω)) →
    (∀ a b : Ω, {c : Ω | ∃ g ∈ G, g a = a ∧ g b = c}.Finite) →
    (∀ g ∈ G, g ≠ 1 → {x : Ω | g x ≠ x}.Infinite) →
    ∃ X : Set Ω, ∀ g ∈ G, g '' X = X → g = 1

/--
Resolved true: Lehner (Theorem 2) proves that every locally compact permutation group on a countable
set with infinite motion has a subset with trivial setwise stabiliser, and closed subdegree-finite
groups are locally compact; this proves Smith's conjecture, which implies Tucker's Infinite Motion
Conjecture for graphs. The 21st issue of the Kourovka Notebook marks 19.89 solved. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 19.89 (S. M. Smith); resolution: F. Lehner, Asymmetric
colouring of locally compact permutation groups, Bull. London Math. Soc. 55 (2023), 1874-1879
(arXiv:2208.08844), Theorem 2: a locally compact permutation group on a countable set with infinite
motion (minimal degree) has an asymmetric 2-colouring, a subset with trivial setwise stabiliser;
Section 2: every closed, subdegree-finite permutation group is locally compact; the Kourovka
Notebook (21st issue) marks 19.89 solved: the conjecture is proved,
https://arxiv.org/abs/2208.08844.
-/
public theorem_wanted closedSubdegreeFiniteDistinguishingSet_holds :
    closedSubdegreeFiniteDistinguishingSet

end MathlibExt.GroupTheory.SubdegreeFiniteDistinguishingSetKourovka19Problem89Wanted
