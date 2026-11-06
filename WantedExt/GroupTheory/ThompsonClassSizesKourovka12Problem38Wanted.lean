/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Thompson's conjecture on conjugacy class sizes (Kourovka Notebook Problem 12.38)

Kourovka Notebook, Archive of Solved Problems, Problem 12.38 (J. G. Thompson; A. S. Kondratiev, W.
J. Shi): let `N(G)` be the set of sizes of the conjugacy classes of a finite group `G`. If `G` is a
finite non-abelian simple group, `H` a finite group with trivial centre and `N(G) = N(H)`, are `G`
and `H` isomorphic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.ThompsonClassSizesKourovka12Problem38Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.38 (J. G.
Thompson; A. S. Kondratiev, W. J. Shi). UnsolvedMath record UM-00700857 (`KOU-12.38`), dataset
ulamai/UnsolvedMath v1.8.0.

`N(G)` is the set of the cardinalities of the conjugacy classes `{y | x ~ y}`; non-abelian is `∃ a
b, a b ≠ b a`, and trivial centre is `Subgroup.center H = ⊥`.
-/

/-- **The set of conjugacy class sizes.** For a group $G$, $N(G)$ is the set of natural numbers
$|\{y \in G : y \text{ is conjugate to } x\}|$ for $x \in G$, that is, the set of sizes of the
conjugacy classes of $G$, where an infinite class counts as size $0$. -/
def classSizes (G : Type*) [Group G] : Set ℕ :=
  Set.range fun x : G => Nat.card {y : G // IsConj x y}

/-- **Thompson's conjecture on conjugacy class sizes.** Write $N(G)$ for the set of sizes of the
conjugacy classes of a group $G$. Thompson's conjecture is the statement that for all finite
groups $G$ and $H$, if $G$ is simple and non-abelian, $H$ has trivial centre, and
$N(G) = N(H)$, then $G$ and $H$ are isomorphic.

This is Kourovka Notebook Problem 12.38 (J. G. Thompson). -/
def simpleGroupRecognizedByClassSizes : Prop :=
  ∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H], IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → Subgroup.center H = ⊥ → classSizes G = classSizes H →
    Nonempty (G ≃* H)

/--
**Thompson's conjecture on conjugacy class sizes is true.** For all finite groups $G$ and $H$, if
$G$ is simple and non-abelian, $H$ has trivial centre, and $G$ and $H$ have the same set of
conjugacy class sizes, then $G$ and $H$ are isomorphic.

Resolved true: the Kourovka Archive answers 12.38 "Yes, it is true" (Thompson's conjecture); the
final step is I. B. Gorshkov (Commun. Algebra 47 (2019)), completing a case-by-case proof over the
finite simple groups by many authors.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.38 (J. G.
Thompson; A. S. Kondratiev, W. J. Shi); resolution: I. B. Gorshkov, Commun. Algebra 47 (2019),
no. 12, 5192-5206 (final step), Kourovka Archive, Problem 12.38: Yes, it is true; earlier steps
by many authors cited there.
-/
public theorem_wanted simpleGroupRecognizedByClassSizes_holds : simpleGroupRecognizedByClassSizes

end MathlibExt.GroupTheory.ThompsonClassSizesKourovka12Problem38Wanted
