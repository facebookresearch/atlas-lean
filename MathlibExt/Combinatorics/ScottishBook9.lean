/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Scottish Book Problem 9

A family of sets of size at most `n` has a common element if every `n + 1` members do.
-/

public section

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
theorem finiteSetsCommonElement :
    ∀ (n : ℕ) {α : Type} [Nonempty α] (ι : Type) (E : ι → Finset α),
      (∀ i, (E i).card ≤ n) →
      (∀ s : Fin (n + 1) → ι, (⋂ i, (E (s i) : Set α)).Nonempty) →
      (⋂ i, (E i : Set α)).Nonempty := by
  classical
  intro n α _ ι E hcard hinter
  simp only [Set.nonempty_def, Set.mem_iInter, Finset.mem_coe] at hinter ⊢
  by_contra! h
  -- Each point has an index witnessing its absence.
  choose miss hmiss using h
  let base := miss (Classical.ofNonempty : α)
  -- Reserve one of the last n slots for each element of the base set.
  let slot := (E base).equivFin.toEmbedding.trans (Fin.castLEEmb (hcard base))
  let rest := Function.extend slot (fun x : E base ↦ miss x) (fun _ ↦ base)
  obtain ⟨x, hx⟩ := hinter (Fin.cons base rest)
  have hxBase : x ∈ E base := by simpa using hx 0
  -- The slot reserved for x selects a set that omits x.
  exact hmiss x (by simpa [rest, slot.injective.extend_apply] using hx (slot ⟨x, hxBase⟩).succ)

end MathlibExt.Combinatorics.ScottishBook9Wanted
