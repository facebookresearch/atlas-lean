/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Non-algebraic and non-modular complete lattices of formations (Kourovka Notebook Problem 18.92)

Kourovka Notebook, Problem 18.92 (A. N. Skiba), marked solved in the 21st issue: a non-empty set `θ`
of formations is a complete lattice of formations if the intersection of any set of formations in
`θ` belongs to `θ` and `θ` has a largest element. An element `a` of a complete lattice is compact if
`a ≤ ⋁X` implies `a ≤ ⋁X₁` for a finite `X₁ ⊆ X`, and the lattice is algebraic if every element is a
join of compact elements. (a) Is there a non-algebraic complete lattice of formations of finite
groups? (b) Is there a non-modular complete lattice of formations of finite groups?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92

@[expose] public section

namespace MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.92 (A. N. Skiba). UnsolvedMath record
UM-00701521 (`KOU-18.92`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of groups are isomorphism-closed predicates on groups in `Type` (`GroupClass`, as in the
WantedExt module for Kourovka 12.97); a formation consists of finite groups, contains the trivial
group, and is closed under quotients and finite subdirect products (`G ⧸ N₁, G ⧸ N₂ ∈ X → G ⧸ (N₁ ⊓
N₂) ∈ X`). Intersections of nonempty subsets of `θ` lie in `θ` (the empty intersection is replaced
by the largest element). Order is inclusion; joins are least upper bounds inside `θ` and meets are
intersections, as in the problem's definition. The resolution is an AI-generated solution confirmed
by A. N. Skiba.
-/

/-- **Non-algebraic complete lattices of formations exist.** There is a set $\Theta$ of classes of
groups that is a complete lattice of formations of finite groups and is not algebraic; that is,
Kourovka Problem 18.92(a) has a positive answer.

The Kourovka Notebook (21st issue) answers 18.92(a) "Yes", by an AI-generated solution confirmed by
A. N. Skiba (Kinyon–Urban, 2026): for a set $S$ of primes let $\mathfrak{F}_S$ be the class of
finite groups whose order has all its prime divisors in $S$; the classes $\mathfrak{F}_S$ with $S$
finite, together with the class of all finite groups, form a complete lattice of formations whose
only compact element is the bottom.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Problem 18.92 (A. N. Skiba); resolution: M. Kinyon and J.
Urban, Results on problems from the Kourovka Notebook, preprint, version 4, 19 September 2026,
Section 3.29 (Problem 18.92): with F_S the finite groups whose order has all prime divisors in S,
{F_S : S finite} ∪ {F_P} is not algebraic and the formations with prime sets ∅, {2}, {2, 3}, {5}, P
form a pentagon N_5; an AI solution confirmed by A. N. Skiba, accepted in the Kourovka Notebook
(21st issue),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka-mathematics.pdf.
-/
public theorem_wanted nonAlgebraicCompleteLatticeOfFormations_holds :
    nonAlgebraicCompleteLatticeOfFormations

end MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92Wanted
