/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# m-reducibility of the Cartesian square of a normal subgroup (Kourovka Notebook Problem 4.20(a))

Kourovka Notebook, Archive of Solved Problems, Problem 4.20(a) (M. K. Valiev): let `F` be a free
group, and `N` a normal subgroup of it. Is it true that the Cartesian square of `N` is `m`-reducible
to `N` (that is, there is an algorithm that from a pair of words `w₁, w₂ ∈ F` constructs a word `w ∈
F` such that `w₁ ∈ N` and `w₂ ∈ N` if and only if `w ∈ N`)? This module covers part a) only. Part
b) of Problem 4.20 (well-known problem) asks whether there exist finitely presented groups in which
the word problem has an arbitrary pre-assigned recursively enumerable `m`-degree of unsolvability;
it is not formalized here.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.Reduce
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.CartesianSquareManyOneReducibleKourovka4Problem20aWanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.20(a) (M. K.
Valiev). UnsolvedMath record UM-00700230 (`KOU-4.20`, both parts; part a) only here), dataset
ulamai/UnsolvedMath v1.8.0.

Words over a generating set `α` are lists of letters `(a, ε)` (`ε` selects `a` or `a⁻¹`); algorithms
are Mathlib's computable functions, so `α` carries a `Primcodable` structure (every free group on a
countable set of generators is covered). `m`-reducibility is Mathlib's `ManyOneReducible`.
-/

/-- Kourovka 4.20(a) (M. K. Valiev): for every free group `F` (on a countable, computably coded
set `α` of generators) and every normal subgroup `N`, the Cartesian square of `N` is
`m`-reducible to `N`: some computable map sends a pair of words `(w₁, w₂)` to a word `w` with
`w₁ ∈ N ∧ w₂ ∈ N ↔ w ∈ N`. Words are lists of letters `(a, ε)`, `ε` selecting `a` or `a⁻¹`. -/
def cartesianSquareManyOneReducible : Prop :=
  ∀ (α : Type) [Primcodable α] (N : Subgroup (FreeGroup α)), N.Normal →
    ManyOneReducible
      (fun w : List (α × Bool) × List (α × Bool) => FreeGroup.mk w.1 ∈ N ∧ FreeGroup.mk w.2 ∈ N)
      (fun w : List (α × Bool) => FreeGroup.mk w ∈ N)

/--
Resolved false: Belegradek shows that the Cartesian square of a normal subgroup of a free group need
not be `m`-reducible to it; the Kourovka Archive answers 4.20(a) "No, it is not true". Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.20(a) (M. K. Valiev);
resolution: O. V. Belegradek, m-Degrees of the word problem, Siberian Math. J. 19 (1978), 867-870,
Kourovka Archive of Solved Problems, Problem 4.20: a) No, it is not true,
https://doi.org/10.1007/BF00972790.
-/
public theorem_wanted cartesianSquareManyOneReducible_refuted : ¬ cartesianSquareManyOneReducible

end MathlibExt.GroupTheory.CartesianSquareManyOneReducibleKourovka4Problem20aWanted
