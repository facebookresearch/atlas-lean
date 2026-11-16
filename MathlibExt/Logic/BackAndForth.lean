/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# Back-and-forth relations

Positions in an Ehrenfeucht-Fraisse game on binary
relations, partial isomorphisms, and the Duplicator-win
relation. The win relation is symmetric and monotone in
the number of rounds. First-order agreement is not
included here.
-/

@[expose] public section

/-- Back-and-forth (EF game) relation core (MOD-30).
Structures are binary relations on `Fin n` / `Fin m` given
as adjacency functions, with equality. A position is a list
of matched pairs. `PartialIso R S ps`: the pairs form a
partial isomorphism (injective both ways, preserves and
reflects `R`). -/
def PartialIso {n m : ℕ} (R : Fin n → Fin n → Bool)
    (S : Fin m → Fin m → Bool) (ps : List (Fin n × Fin m)) : Prop :=
  (∀ p ∈ ps, ∀ q ∈ ps, (p.1 = q.1 ↔ p.2 = q.2)) ∧
  (∀ p ∈ ps, ∀ q ∈ ps, R p.1 q.1 = S p.2 q.2)

/-- Duplicator wins the `k`-round game from position `ps`:
at zero rounds the position must be a partial isomorphism;
at each further round every Spoiler move on either side
has a reply keeping the win. -/
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
      show PartialIso S R (ps.map Prod.swap)
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
      show (∀ b : Fin m, ∃ a : Fin n, DuplicatorWin S R k ((b, a) :: ps.map Prod.swap)) ∧
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
      show PartialIso R S ps
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
      show (∀ a : Fin n, ∃ b : Fin m, DuplicatorWin R S k ((a, b) :: ps)) ∧
        (∀ b : Fin m, ∃ a : Fin n, DuplicatorWin R S k ((a, b) :: ps))
      constructor
      · intro a
        obtain ⟨b, hb'⟩ := hf a
        exact ⟨b, ih ((a, b) :: ps) hb'⟩
      · intro b
        obtain ⟨a, ha'⟩ := hb b
        exact ⟨a, ih ((a, b) :: ps) ha'⟩

/-- Winning is symmetric in the two structures. -/
theorem DuplicatorWin.symm {n m : ℕ} (R : Fin n → Fin n → Bool)
    (S : Fin m → Fin m → Bool) {k : ℕ} {ps : List (Fin n × Fin m)}
    (h : DuplicatorWin R S k ps) :
    DuplicatorWin S R k (ps.map Prod.swap) := by
  exact DuplicatorWin_symm_aux R S k ps h

/-- Winning more rounds implies winning fewer. -/
theorem DuplicatorWin.mono {n m : ℕ} (R : Fin n → Fin n → Bool)
    (S : Fin m → Fin m → Bool) {k : ℕ} {ps : List (Fin n × Fin m)}
    (h : DuplicatorWin R S (k + 1) ps) :
    DuplicatorWin R S k ps := by
  exact DuplicatorWin_mono_aux R S k ps h

end
