/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Endomorphisms versus partial isomorphisms (Kourovka Notebook Problem 19.20)

Kourovka Notebook, Problem 19.20 (P. J. Cameron), marked solved in the 21st issue: for a finite
group `G`, let `End(G)` be the semigroup of endomorphisms and `PIso(G)` the semigroup of partial
isomorphisms (isomorphisms between subgroups of `G`). If `G` is abelian, then `|End(G)| =
|PIso(G)|`. Is the converse true?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.EndomorphismPartialIsomorphismCountKourovka19Problem20Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.20 (P. J. Cameron). UnsolvedMath record
UM-00701568 (`KOU-19.20`), dataset ulamai/UnsolvedMath v1.8.0.

`PIso(G)` is counted as the sigma type of triples `(H, K, H ≃* K)` of subgroups and an isomorphism
between them. As in the resolving preprint, the trivial subgroup is included (its isomorphism onto
itself counts once) and no empty partial map is added; for abelian groups of order `2`, `3` and `4`
both sides agree, as the problem states for all abelian groups.
-/

/-- **Kourovka Problem 19.20 (Cameron).** The statement that every finite group $G$ with
$|\mathrm{End}(G)| = |\mathrm{PIso}(G)|$ is abelian. Here $\mathrm{End}(G)$ is the set of
endomorphisms of $G$, and $\mathrm{PIso}(G)$ is the set of partial isomorphisms of $G$: the triples
$(H, K, f)$ of subgroups $H$, $K$ of $G$ and an isomorphism $f \colon H \to K$. -/
def endPartialIsoCountImpliesAbelian : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    Nat.card (G →* G) = Nat.card (Σ H : Subgroup G, Σ K : Subgroup G, (H ≃* K)) →
      ∀ x y : G, x * y = y * x

/--
**Equal endomorphism and partial isomorphism counts do not force commutativity.** There is a
finite non-abelian group $G$ with $|\mathrm{End}(G)| = |\mathrm{PIso}(G)|$. Here $\mathrm{End}(G)$
is the set of endomorphisms of $G$, and $\mathrm{PIso}(G)$ is the set of partial isomorphisms of
$G$: the triples $(H, K, f)$ of subgroups $H$, $K$ of $G$ and an isomorphism $f \colon H \to K$.
This answers Kourovka Problem 19.20 (P. J. Cameron) in the negative.

K. Muliarchyk's Theorem 1.1 (2026) gives a non-abelian group of order $512$ for which both counts
equal $129 \cdot 2^{24}$; the Kourovka Notebook (21st issue) answers 19.20 "No, it is not".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.20 (P. J. Cameron); resolution:
K. Muliarchyk, A nonabelian group with equally many endomorphisms and partial isomorphisms: a
computer-assisted counterexample to Kourovka Problem 19.20, preprint, 2026, Theorem 1.1: a
nonabelian group of order 512, nilpotency class two and exponent four, with |PIso(G)| = |End(G)| =
129 · 2^24 (the partial isomorphisms counted by exhaustive enumeration); the Kourovka Notebook (21st
issue) marks 19.20 solved: No, it is not,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_19.20_solution.pdf.
-/
public theorem_wanted endPartialIsoCountImpliesAbelian_refuted : ¬ endPartialIsoCountImpliesAbelian

end MathlibExt.GroupTheory.EndomorphismPartialIsomorphismCountKourovka19Problem20Wanted
