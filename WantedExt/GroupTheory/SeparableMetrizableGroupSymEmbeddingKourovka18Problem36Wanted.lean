/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Separable metrizable groups and Sym(ℕ) (Kourovka Notebook Problem 18.36)

Kourovka Notebook, Problem 18.36 (J. D. Dixon), marked solved in the 21st issue: is it true that
every group `G` for which there is a metric `d'` such that `(G, d')` is a separable topological
group is (abstractly) embeddable in `Sym(ℕ)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Metrizable.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.SeparableMetrizableGroupSymEmbeddingKourovka18Problem36Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.36 (J. D. Dixon). UnsolvedMath record
UM-00701465 (`KOU-18.36`), dataset ulamai/UnsolvedMath v1.8.0.

A metric making `G` a separable topological group is a topology on `G` that is metrizable, separable
and makes `G` a topological group; abstract embeddability is an injective homomorphism to
`Equiv.Perm ℕ`.
-/

/-- **Claim of Kourovka Problem 18.36.** The claim (J. D. Dixon) that every group $G$ that
admits a metrizable topology making it a separable topological group admits an injective group
homomorphism into the group $\mathrm{Sym}(\mathbb{N})$ of all permutations of the natural
numbers. -/
def separableMetrizableGroupEmbedsInSym : Prop :=
  ∀ (G : Type) [Group G],
    (∃ t : TopologicalSpace G, @IsTopologicalGroup G t _ ∧
      @TopologicalSpace.MetrizableSpace G t ∧ @TopologicalSpace.SeparableSpace G t) →
    ∃ f : G →* Equiv.Perm ℕ, Function.Injective f

/--
**Separable metrizable groups need not embed in the infinite symmetric group.** The claim of
Kourovka Problem 18.36 is false: there is a group $G$ that admits a metrizable topology
making it a separable topological group but admits no injective group homomorphism into the
group $\mathrm{Sym}(\mathbb{N})$ of all permutations of the natural numbers.

Rosendal and Solecki (2007) give an uncountable connected Polish group (a separable
completely metrizable topological group) every abstract homomorphism of which into
$\mathrm{Sym}(\mathbb{N})$ is trivial, so it has no injective one.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Problem 18.36 (J. D. Dixon); resolution: C. Rosendal and S.
Solecki, Israel J. Math. 162 (2007), 349-371, an uncountable connected Polish group whose every
abstract homomorphism into Sym(ℕ) is trivial; see also A. Kaïchouh and F. Le Maître, Bull. London
Math. Soc. 47 (2015), 996-1009 (S. Corson, letter of 5 June 2024); the Kourovka Notebook (21st
issue) marks 18.36 solved, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted separableMetrizableGroupEmbedsInSym_refuted :
    ¬ separableMetrizableGroupEmbedsInSym

end MathlibExt.GroupTheory.SeparableMetrizableGroupSymEmbeddingKourovka18Problem36Wanted
