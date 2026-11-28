/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.LogicProgramming.LeastHerbrandModel
import Mathlib.Algebra.Ring.Parity

/-!
# Tests for the least Herbrand model

The two-clause program `p ← q`, `q ←` with its least model `{p, q}` and the iterates of `T_P`;
the program `p ←`, `q ← p`, `r ← r`, whose operator has a fixed point larger than the least one;
and the infinite program `0 ←`, `n + 2 ← n` over `ℕ`, whose least model, the even numbers, is
reached only after infinitely many iterations of `T_P`.
-/

namespace CSLibExtTest.Languages.LogicProgramming.LeastHerbrandModel

open Cslib.LogicProgramming

/-- Three propositional atoms. -/
private inductive Atom
  | p
  | q
  | r

open Atom

/-- The two-clause program `p ← q`, `q ←`. -/
private def twoClause : Set (DefiniteClause Atom) :=
  {⟨p, [q]⟩, ⟨q, []⟩}

/-- One application of `T_P` to the empty interpretation derives the fact `q`. -/
example : (immediateConsequence twoClause)^[1] ∅ = {q} := by
  ext a
  cases a <;> simp [twoClause, immediateConsequence]

/-- Two applications of `T_P` to the empty interpretation derive `p` and `q`. -/
example : (immediateConsequence twoClause)^[2] ∅ = {p, q} := by
  ext a
  cases a <;> simp [twoClause, immediateConsequence]

/-- `{p, q}` is a fixed point of `T_P`, so the iterates from the third on are all `{p, q}`. -/
example : immediateConsequence twoClause {p, q} = {p, q} := by
  ext a
  cases a <;> simp [twoClause, immediateConsequence]

/-- The least Herbrand model of `p ← q`, `q ←` is `{p, q}`. -/
example : leastModel twoClause = {p, q} := by
  refine (leastModel_characterization twoClause).2.1.unique ⟨?_, fun I hI ↦ ?_⟩
  · intro c hc hb
    rcases hc with rfl | rfl <;> simp
  · have hq : q ∈ I := hI ⟨q, []⟩ (by simp [twoClause]) (by simp)
    have hp : p ∈ I := hI ⟨p, [q]⟩ (by simp [twoClause]) (by simpa using hq)
    simp [Set.insert_subset_iff, hp, hq]

/-- The least Herbrand model is the union of the iterates: `p` is derived in two steps. -/
example : p ∈ leastModel twoClause := by
  rw [(leastModel_characterization twoClause).2.2.2, Set.mem_iUnion]
  exact ⟨2, by simp [twoClause, immediateConsequence]⟩

/-- The program `p ←`, `q ← p`, `r ← r`. -/
private def loop : Set (DefiniteClause Atom) :=
  {⟨p, []⟩, ⟨q, [p]⟩, ⟨r, [r]⟩}

/-- `{p, q, r}` is a fixed point of `T_P` for `p ←`, `q ← p`, `r ← r`. -/
example : immediateConsequence loop {p, q, r} = {p, q, r} := by
  ext a
  cases a <;> simp [loop, immediateConsequence]

/-- The least fixed point of `T_P` for `p ←`, `q ← p`, `r ← r` is `{p, q}`, smaller than the fixed
point `{p, q, r}`: the clause `r ← r` alone does not derive `r`. -/
example : OrderHom.lfp (immediateConsequence loop) = {p, q} := by
  rw [← (leastModel_characterization loop).2.2.1]
  refine (leastModel_characterization loop).2.1.unique ⟨?_, fun I hI ↦ ?_⟩
  · intro c hc hb
    rcases hc with rfl | rfl | rfl <;> simp_all
  · have hp : p ∈ I := hI ⟨p, []⟩ (by simp [loop]) (by simp)
    have hq : q ∈ I := hI ⟨q, [p]⟩ (by simp [loop]) (by simpa using hp)
    simp [Set.insert_subset_iff, hp, hq]

/-- The infinite program `0 ←` and `n + 2 ← n` for every `n : ℕ`. -/
private def evens : Set (DefiniteClause ℕ) :=
  {c | c = ⟨0, []⟩ ∨ ∃ n, c = ⟨n + 2, [n]⟩}

/-- The least Herbrand model of `0 ←`, `n + 2 ← n` is the set of even numbers. -/
private theorem leastModel_evens : leastModel evens = {n | Even n} := by
  refine (leastModel_characterization evens).2.1.unique ⟨?_, fun I hI ↦ ?_⟩
  · rintro c (rfl | ⟨n, rfl⟩) hb
    · exact Even.zero
    · exact (hb n (by simp)).add even_two
  · rintro _ ⟨k, rfl⟩
    induction k with
    | zero => exact hI ⟨0, []⟩ (Or.inl rfl) (by simp)
    | succ k ih =>
      have h := hI ⟨k + k + 2, [k + k]⟩ (Or.inr ⟨k + k, rfl⟩) (by simpa using ih)
      rwa [show k + 1 + (k + 1) = k + k + 2 by omega]

/-- For `0 ←`, `n + 2 ← n`, the `n`-th iterate of `T_P` on the empty interpretation contains only
numbers below `2 n`. -/
private theorem evens_iterate_subset (n : ℕ) :
    (immediateConsequence evens)^[n] ∅ ⊆ {m | m < 2 * n} := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rintro _ ⟨c, (rfl | ⟨k, rfl⟩), rfl, hb⟩
    · simp
    · have := ih (hb k (by simp))
      simp only [Set.mem_ofPred_eq] at this ⊢
      omega

/-- No finite iterate of `T_P` reaches the least Herbrand model of `0 ←`, `n + 2 ← n`: the even
number `2 n` is missing from the `n`-th iterate, so the union over all iterates is needed. -/
example (n : ℕ) : (immediateConsequence evens)^[n] ∅ ≠ leastModel evens := by
  intro h
  have h2n : 2 * n ∈ leastModel evens := leastModel_evens ▸ even_two_mul n
  exact lt_irrefl (2 * n) (evens_iterate_subset n (h ▸ h2n))

end CSLibExtTest.Languages.LogicProgramming.LeastHerbrandModel
