/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Order

@[expose] public section

namespace MathlibExt.Combinatorics.ScottishBook9Wanted

/--
Let `E` be a family of sets, each finite with at most `n` elements, such that
any `n + 1` of them have an element in common. Then there is an element common
to every set in `E`. The hypothesis is read with repetitions allowed: it
quantifies over all tuples `Fin (n + 1) → ι` of members, not only over
tuples of distinct members. Under the distinct-members reading the claim
would be false when the family has at most `n` members (the hypothesis is
then vacuous), so the repetition reading is the intended one. Source:
S. Mazur and W. Orlicz, Problem 9 of the Scottish Book, stated as a theorem
by Ulam in the Scottish Book typescript; see also the 2026 survey "90+ years
of the Scottish Book" (arXiv:2603.27867), which records that Ulam solved
Problem 9.
-/
theorem_wanted finiteSetsCommonElement :
    ∀ (n : ℕ) {α : Type} [Nonempty α] (ι : Type) (E : ι → Finset α),
      (∀ i, (E i).card ≤ n) →
      (∀ s : Fin (n + 1) → ι, (⋂ i, (E (s i) : Set α)).Nonempty) →
      (⋂ i, (E i : Set α)).Nonempty

end MathlibExt.Combinatorics.ScottishBook9Wanted
