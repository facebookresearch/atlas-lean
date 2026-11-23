/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# Ehrenfeucht–Fraïssé games on finite binary relations

Positions of the Ehrenfeucht–Fraïssé game between two finite structures that each carry one
binary relation, given as Boolean adjacency functions `R : Fin n → Fin n → Bool` and
`S : Fin m → Fin m → Bool`. A position is the list of pairs `(a, b)` played so far.

* `PartialIso R S ps`: the pairs of `ps` form a partial isomorphism: two pairs agree in the
  first coordinate exactly when they agree in the second, and `R` and `S` take the same value
  on corresponding pairs.
* `DuplicatorWin R S k ps`: Duplicator wins the `k`-round game from the position `ps`. In each
  round Spoiler picks an element of either structure and Duplicator answers with an element of
  the other one; after the last round the position must be a partial isomorphism.
* `DuplicatorWin.symm`: swapping the two structures, and the coordinates of every pair,
  preserves a win.
* `DuplicatorWin.mono`: a win in `k + 1` rounds gives a win in `k` rounds.

The Ehrenfeucht–Fraïssé theorem, which relates these games to first-order sentences of bounded
quantifier rank, is not formalized here.

## References

* L. Libkin, *Elements of Finite Model Theory*, Springer, 2004, Chapter 3.
-/

@[expose] public section

namespace MathlibExt.Logic.BackAndForth

/-- The pairs of the position `ps` form a partial isomorphism between the relations
`R : Fin n → Fin n → Bool` and `S : Fin m → Fin m → Bool`: two pairs agree in the first
coordinate exactly when they agree in the second, so the pairs match elements injectively in
both directions, and `R` and `S` take the same value on corresponding pairs. -/
def PartialIso {n m : ℕ} (R : Fin n → Fin n → Bool)
    (S : Fin m → Fin m → Bool) (ps : List (Fin n × Fin m)) : Prop :=
  (∀ p ∈ ps, ∀ q ∈ ps, (p.1 = q.1 ↔ p.2 = q.2)) ∧
  (∀ p ∈ ps, ∀ q ∈ ps, R p.1 q.1 = S p.2 q.2)

/-- Duplicator wins the `k`-round Ehrenfeucht–Fraïssé game between `R` and `S` from the
position `ps`. With no rounds left the position must be a partial isomorphism. With `k + 1`
rounds left, for every element Spoiler picks in either structure, Duplicator has an answer in
the other structure from which Duplicator wins the remaining `k` rounds. -/
def DuplicatorWin {n m : ℕ} (R : Fin n → Fin n → Bool)
    (S : Fin m → Fin m → Bool) : ℕ → List (Fin n × Fin m) → Prop
  | 0, ps => PartialIso R S ps
  | k + 1, ps =>
      (∀ a : Fin n, ∃ b : Fin m, DuplicatorWin R S k ((a, b) :: ps)) ∧
      (∀ b : Fin m, ∃ a : Fin n, DuplicatorWin R S k ((a, b) :: ps))

private theorem DuplicatorWin_symm_aux {n m : ℕ} (R : Fin n → Fin n → Bool)
    (S : Fin m → Fin m → Bool) (k : ℕ) :
    ∀ (ps : List (Fin n × Fin m)),
      DuplicatorWin R S k ps → DuplicatorWin S R k (ps.map Prod.swap) := by
  induction k with
  | zero =>
      intro ps h
      change PartialIso S R (ps.map Prod.swap)
      obtain ⟨hinj, hrel⟩ := h
      constructor
      · intro p' hp' q' hq'
        rw [List.mem_map] at hp' hq'
        obtain ⟨p, hpmem, rfl⟩ := hp'
        obtain ⟨q, hqmem, rfl⟩ := hq'
        simp only [Prod.fst_swap, Prod.snd_swap]
        exact (hinj p hpmem q hqmem).symm
      · intro p' hp' q' hq'
        rw [List.mem_map] at hp' hq'
        obtain ⟨p, hpmem, rfl⟩ := hp'
        obtain ⟨q, hqmem, rfl⟩ := hq'
        simp only [Prod.fst_swap, Prod.snd_swap]
        exact (hrel p hpmem q hqmem).symm
  | succ k ih =>
      intro ps h
      obtain ⟨hf, hb⟩ := h
      change (∀ b : Fin m, ∃ a : Fin n, DuplicatorWin S R k ((b, a) :: ps.map Prod.swap)) ∧
        (∀ a : Fin n, ∃ b : Fin m, DuplicatorWin S R k ((b, a) :: ps.map Prod.swap))
      constructor
      · intro b
        obtain ⟨a, ha⟩ := hb b
        refine ⟨a, ?_⟩
        have h' := ih ((a, b) :: ps) ha
        rw [List.map_cons] at h'
        exact h'
      · intro a
        obtain ⟨b, hb'⟩ := hf a
        refine ⟨b, ?_⟩
        have h' := ih ((a, b) :: ps) hb'
        rw [List.map_cons] at h'
        exact h'

private theorem DuplicatorWin_mono_aux {n m : ℕ} (R : Fin n → Fin n → Bool)
    (S : Fin m → Fin m → Bool) (k : ℕ) :
    ∀ (ps : List (Fin n × Fin m)),
      DuplicatorWin R S (k + 1) ps → DuplicatorWin R S k ps := by
  induction k with
  | zero =>
      intro ps h
      change PartialIso R S ps
      obtain ⟨hf, _hb⟩ := h
      constructor
      · intro p hp q hq
        obtain ⟨b, hb⟩ := hf p.1
        exact hb.1 _ (List.mem_cons.mpr (Or.inr hp)) _ (List.mem_cons.mpr (Or.inr hq))
      · intro p hp q hq
        obtain ⟨b, hb⟩ := hf p.1
        exact hb.2 _ (List.mem_cons.mpr (Or.inr hp)) _ (List.mem_cons.mpr (Or.inr hq))
  | succ k ih =>
      intro ps h
      obtain ⟨hf, hb⟩ := h
      change (∀ a : Fin n, ∃ b : Fin m, DuplicatorWin R S k ((a, b) :: ps)) ∧
        (∀ b : Fin m, ∃ a : Fin n, DuplicatorWin R S k ((a, b) :: ps))
      constructor
      · intro a
        obtain ⟨b, hb'⟩ := hf a
        exact ⟨b, ih ((a, b) :: ps) hb'⟩
      · intro b
        obtain ⟨a, ha'⟩ := hb b
        exact ⟨a, ih ((a, b) :: ps) ha'⟩

/-- Swapping the two structures, and the coordinates of every pair of the position, preserves a
win. -/
theorem DuplicatorWin.symm {n m : ℕ} (R : Fin n → Fin n → Bool)
    (S : Fin m → Fin m → Bool) {k : ℕ} {ps : List (Fin n × Fin m)}
    (h : DuplicatorWin R S k ps) :
    DuplicatorWin S R k (ps.map Prod.swap) := by
  exact DuplicatorWin_symm_aux R S k ps h

/-- A win in `k + 1` rounds from a position gives a win in `k` rounds from the same
position. -/
theorem DuplicatorWin.mono {n m : ℕ} (R : Fin n → Fin n → Bool)
    (S : Fin m → Fin m → Bool) {k : ℕ} {ps : List (Fin n × Fin m)}
    (h : DuplicatorWin R S (k + 1) ps) :
    DuplicatorWin R S k ps := by
  exact DuplicatorWin_mono_aux R S k ps h

end MathlibExt.Logic.BackAndForth
