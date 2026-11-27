/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Abelian normal subgroups of sharply 2-transitive groups (Kourovka Notebook Problem 11.52)

Kourovka Notebook, Archive of Solved Problems, Problem 11.52 (V. D. Mazurov; well-known problem):
does every sharply doubly transitive permutation group possess a non-trivial abelian normal
subgroup? (Yes for finite groups.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice

@[expose] public section

namespace MathlibExt.GroupTheory.SharplyTwoTransitiveAbelianNormalKourovka11Problem52Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.52 (V. D.
Mazurov). UnsolvedMath record UM-00700744 (`KOU-11.52`), dataset ulamai/UnsolvedMath v1.8.0.

A sharply doubly transitive group is an action of `G` on `Ω` in which any two pairs of distinct
points are related by exactly one group element. The set `Ω` must have at least two points: with
fewer there are no such pairs, and the trivial group on one point would be a trivial counterexample.
Faithfulness is automatic once `|Ω| ≥ 2`, since an element fixing two distinct points is the
identity by uniqueness.
-/

/-- **Sharply doubly transitive action.** An action of a group $G$ on a set $\Omega$ is sharply
doubly transitive when for all points $\alpha, \beta, \gamma, \delta \in \Omega$ with
$\alpha \ne \beta$ and $\gamma \ne \delta$ there is exactly one $g \in G$ with
$g \cdot \alpha = \gamma$ and $g \cdot \beta = \delta$. -/
def IsSharplyTwoTransitive (G Ω : Type*) [Group G] [MulAction G Ω] : Prop :=
  ∀ α β γ δ : Ω, α ≠ β → γ ≠ δ → ∃! g : G, g • α = γ ∧ g • β = δ

/-- **Mazurov's question on sharply 2-transitive groups (Kourovka 11.52).** The statement that every
group $G$ acting sharply doubly transitively on a set $\Omega$ with at least two points has a
nontrivial abelian normal subgroup. -/
def sharplyTwoTransitiveHasAbelianNormal : Prop :=
  ∀ (G Ω : Type) [Group G] [MulAction G Ω], Nontrivial Ω → IsSharplyTwoTransitive G Ω →
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ ∀ x ∈ N, ∀ y ∈ N, x * y = y * x

/--
**A sharply 2-transitive group without nontrivial abelian normal subgroups.** The statement of
Kourovka Problem 11.52 is false: there is a group $G$ acting sharply doubly transitively on a set
$\Omega$ with at least two points such that no nontrivial normal subgroup of $G$ is abelian.

Rips, Segev and Tent construct such a group; the Kourovka Archive answers 11.52 "No, not every".
For finite groups the answer is yes, by Frobenius's theorem.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 11.52 (V. D. Mazurov); resolution: E. Rips, Y. Segev and K. Tent, J. Eur.
Math. Soc. 19, no. 10 (2017), 2895-2910, Kourovka Archive, Problem 11.52: "No, not every",
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted sharplyTwoTransitiveHasAbelianNormal_refuted :
    ¬ sharplyTwoTransitiveHasAbelianNormal

end MathlibExt.GroupTheory.SharplyTwoTransitiveAbelianNormalKourovka11Problem52Wanted
