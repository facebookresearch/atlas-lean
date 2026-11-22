/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Separability of `R`-groups (Kourovka Notebook Problem 1.64)

Kourovka Notebook, Archive of Solved Problems, Problem 1.64 (P. G. Kontorovich): a torsion-free
group is said to be separable if it can be represented as the set-theoretic union of two of its
proper subsemigroups. Is every `R`-group separable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subsemigroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.RGroupSeparableKourovka1Problem64Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.64 (P. G.
Kontorovich). UnsolvedMath record UM-00700055 (`KOU-1.64`), dataset ulamai/UnsolvedMath v1.8.0.

An `R`-group is a group with unique roots: `xⁿ = yⁿ` with `n ≥ 1` implies `x = y` (such groups are
torsion-free). The group is required to be nontrivial: the trivial group is an `R`-group but is not
the union of two proper subsemigroups, so the claim would fail for a trivial reason.
-/

/-- `G` is an `R`-group: `xⁿ = yⁿ` with `n ≥ 1` implies `x = y` (roots are unique). -/
def IsRGroup (G : Type) [Group G] : Prop :=
  ∀ (x y : G) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y

/-- `G` is separable: it is the union of two proper subsemigroups. -/
def IsSeparable (G : Type) [Group G] : Prop :=
  ∃ S T : Subsemigroup G, S ≠ ⊤ ∧ T ≠ ⊤ ∧ ∀ g : G, g ∈ S ∨ g ∈ T

/-- Kourovka 1.64 (P. G. Kontorovich): every nontrivial `R`-group is separable. -/
def rGroupIsSeparable : Prop :=
  ∀ (G : Type) [Group G], Nontrivial G → IsRGroup G → IsSeparable G

/--
Resolved false: the Kourovka Archive answers 1.64 "No", citing Pride and Wiegold's nontrivial
`R`-group that is not the union of two proper subsemigroups. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 1.64 (P. G. Kontorovich); resolution: S. J. Pride and J.
Wiegold, Bull. London Math. Soc. 9 (1977), 36-37, Kourovka Archive, Problem 1.64 (No).
-/
public theorem_wanted rGroupIsSeparable_refuted : ¬ rGroupIsSeparable

end MathlibExt.GroupTheory.RGroupSeparableKourovka1Problem64Wanted
