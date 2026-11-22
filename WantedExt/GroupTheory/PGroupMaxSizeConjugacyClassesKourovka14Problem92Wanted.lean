/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite `p`-groups with `p - 1` conjugacy classes of maximum size (Kourovka Notebook Problem 14.92)

Kourovka Notebook, Archive of Solved Problems, Problem 14.92 (G. Fernández-Alcober): every finite
`p`-group has at least `p - 1` conjugacy classes of maximum size (I. D. Macdonald), who found groups
of order `2ⁿ` with just one. Are there any examples with exactly `p - 1` conjugacy classes of
maximum size for odd `p`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.PGroupMaxSizeConjugacyClassesKourovka14Problem92Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.92 (G.
Fernández-Alcober). UnsolvedMath record UM-00701076 (`KOU-14.92`), dataset ulamai/UnsolvedMath
v1.8.0.

The question is read existentially (some odd prime `p` and some finite `p`-group), which is what the
Archive answer "Yes, there are, for `p = 3`" settles; nothing is claimed for every odd `p`. The size
of a class is the cardinality of its carrier. For `p = 2` the trivial group would be an example,
which is why the problem asks about odd `p`.
-/

/-- The number of conjugacy classes of maximum size of a finite group `G`. -/
noncomputable def numMaxSizeConjClasses (G : Type*) [Group G] : ℕ :=
  Nat.card {c : ConjClasses G // ∀ d : ConjClasses G, Nat.card d.carrier ≤ Nat.card c.carrier}

/-- Kourovka 14.92 (G. Fernández-Alcober): for some odd prime `p` there is a finite `p`-group with
exactly `p - 1` conjugacy classes of maximum size. -/
def oddPGroupWithPredMaxSizeConjClasses : Prop :=
  ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧
    numMaxSizeConjClasses G = p - 1

/--
Resolved true: the Kourovka Archive answers 14.92 "Yes, there are, for `p = 3`" (Jaikin-Zapirain,
Newman and O'Brien): some finite `3`-group has exactly `2` conjugacy classes of maximum size.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.92 (G.
Fernández-Alcober); resolution: A. Jaikin-Zapirain, M. F. Newman and E. A. O'Brien, p-groups having
the minimal number of conjugacy classes of maximal size, Israel J. Math. 172 (2009), no. 1, 119-123,
abstract (a 3-group with exactly p - 1 = 2 conjugacy classes of the largest size); Kourovka Archive,
Problem 14.92 (answer: Yes, there are, for p = 3),
http://verso.mat.uam.es/~andrei.jaikin/preprints/articulos.htm.
-/
public theorem_wanted oddPGroupWithPredMaxSizeConjClasses_holds :
    oddPGroupWithPredMaxSizeConjClasses

end MathlibExt.GroupTheory.PGroupMaxSizeConjugacyClassesKourovka14Problem92Wanted
