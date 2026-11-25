/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Simple groups with permuting conjugate subgroups (Kourovka Notebook Problem 10.66)

Kourovka Notebook, Archive of Solved Problems, Problem 10.66 (A. N. Fomin, V. P. Shunkov): is a
group `G` non-simple if it contains two non-trivial subgroups `A` and `B` such that `AB ≠ G` and
`AB^g = B^gA` for every `g ∈ G`? This is true if `G` is finite (O. H. Kegel).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.PermutingConjugatesSimpleGroupKourovka10Problem66Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.66 (A. N.
Fomin, V. P. Shunkov). UnsolvedMath record UM-00700681 (`KOU-10.66`), dataset ulamai/UnsolvedMath
v1.8.0.

`B^g` ranges over all conjugates `g B g⁻¹`, and products of subgroups are set products.
-/

open scoped Pointwise

/-- **Permuting conjugates and simplicity (Kourovka 10.66).** The conjecture that a group $G$
containing nontrivial subgroups $A$ and $B$ such that the product set $AB$ is not all of $G$ and
$A \cdot gBg^{-1} = gBg^{-1} \cdot A$ for every $g \in G$ is not simple. Products of subgroups are
products of subsets of $G$.

This is Kourovka Problem 10.66 (A. N. Fomin, V. P. Shunkov). -/
def permutingConjugatesNotSimple : Prop :=
  ∀ (G : Type) [Group G] (A B : Subgroup G), A ≠ ⊥ → B ≠ ⊥ → (A : Set G) * (B : Set G) ≠ Set.univ →
    (∀ g : G, (A : Set G) * (B.map (MulAut.conj g).toMonoidHom : Set G) =
      (B.map (MulAut.conj g).toMonoidHom : Set G) * (A : Set G)) →
    ¬ IsSimpleGroup G

/--
**A simple group with permuting conjugate subgroups (Kourovka 10.66 refuted).** There exist a
simple group $G$ and nontrivial subgroups $A$ and $B$ of $G$ such that the product set $AB$ is not
all of $G$ and $A \cdot gBg^{-1} = gBg^{-1} \cdot A$ for every $g \in G$, where products of
subgroups are products of subsets of $G$. So the conjecture of Kourovka Problem 10.66 is false.

Bludov's example takes a simple linearly ordered group $G$ and nontrivial proper convex subgroups
$A$ and $B$. Conjugates of convex subgroups are convex and the convex subgroups form a chain, so
$A \cdot gBg^{-1}$ and $gBg^{-1} \cdot A$ both equal the larger of $A$ and $gBg^{-1}$, and
$AB \ne G$. Such subgroups exist: a nontrivial simple ordered group is not archimedean
(archimedean ordered groups are abelian, by Hölder), so it has nontrivial proper convex subgroups.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.66 (A. N.
Fomin, V. P. Shunkov); resolution: V. V. Bludov, letter of 12 February 1997, recorded in the
Kourovka Archive, Problem 10.66, Archive answer: "No; for example, for G being any simple linearly
ordered group and A and B arbitrary proper convex subgroups of G".
-/
public theorem_wanted permutingConjugatesNotSimple_refuted : ¬ permutingConjugatesNotSimple

end MathlibExt.GroupTheory.PermutingConjugatesSimpleGroupKourovka10Problem66Wanted
