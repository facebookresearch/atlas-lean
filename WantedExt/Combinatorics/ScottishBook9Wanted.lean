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
**Scottish Book Problem 9 (a common element of small finite sets).** Let $n$ be a natural
number, let $\alpha$ be a nonempty set, and let $(E_i)_{i \in I}$ be a family of finite subsets
of $\alpha$, indexed by an arbitrary set $I$, with $|E_i| \le n$ for every $i \in I$. Suppose
that for all indices $i_0, i_1, \dots, i_n \in I$, not necessarily distinct, the sets
$E_{i_0}, E_{i_1}, \dots, E_{i_n}$ have an element in common. Then some element of $\alpha$
lies in every $E_i$.

The hypothesis is read with repetitions allowed: it quantifies over all choices of $n + 1$
indices, not only over $n + 1$ distinct members. Under the distinct-members reading the claim
would be false when the family has at most $n$ members (the hypothesis is then vacuous), so the
repetition reading is the intended one.

Source:
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
