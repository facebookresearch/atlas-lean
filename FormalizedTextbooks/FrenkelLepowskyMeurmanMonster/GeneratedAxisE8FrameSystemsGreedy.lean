/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsExtension

/-! Greedy independent bases of genuine sixteen-element binary subspaces. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The binary subspace spanned by a finite list of intrinsic vectors. -/
def generatedAxisE8FrameListSpan (l : List (Fin 8 → ZMod 2)) :
    Submodule (ZMod 2) (Fin 8 → ZMod 2) := Submodule.span (ZMod 2) {v | v ∈ l}

/-- A list in a fixed subspace whose entries are successive least-label independent vectors. -/
def generatedAxisE8FrameGreedyIn (W : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (l : List (Fin 8 → ZMod 2)) : Prop :=
  (∀ v ∈ l, v ∈ W) ∧ ∀ i : Fin l.length,
    l[i] ∉ generatedAxisE8FrameListSpan (l.take i.val) ∧
    ∀ v ∈ W, v ∉ generatedAxisE8FrameListSpan (l.take i.val) →
      generatedAxisE8FrameLabel l[i] ≤ generatedAxisE8FrameLabel v

/-- Appending a vector adjoins exactly its singleton span. -/
theorem generatedAxisE8FrameListSpan_append (l : List (Fin 8 → ZMod 2)) (v : Fin 8 → ZMod 2) :
    generatedAxisE8FrameListSpan (l ++ [v]) =
      generatedAxisE8FrameListSpan l ⊔ Submodule.span (ZMod 2) {v} := by
  have he : {w | w ∈ l ++ [v]} = {w | w ∈ l} ∪ {v} := by ext w; simp [or_comm]
  simp only [generatedAxisE8FrameListSpan, he, Submodule.span_union]

/-- A greedy list spans a subspace of the original genuine binary subspace. -/
theorem generatedAxisE8FrameGreedyIn_span_le
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (l : List (Fin 8 → ZMod 2))
    (hl : generatedAxisE8FrameGreedyIn W l) : generatedAxisE8FrameListSpan l ≤ W :=
  Submodule.span_le.mpr hl.1

/-- Appending a least-label vector outside the span preserves the full greedy property. -/
theorem generatedAxisE8FrameGreedyIn_append
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (l : List (Fin 8 → ZMod 2))
    (hl : generatedAxisE8FrameGreedyIn W l) (v : Fin 8 → ZMod 2)
    (hv : v ∈ W) (hs : v ∉ generatedAxisE8FrameListSpan l)
    (hmin : ∀ w ∈ W, w ∉ generatedAxisE8FrameListSpan l →
      generatedAxisE8FrameLabel v ≤ generatedAxisE8FrameLabel w) :
    generatedAxisE8FrameGreedyIn W (l ++ [v]) := by
  refine ⟨?_, ?_⟩
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hl.1 w hw
    · have he : w = v := List.mem_singleton.mp hw
      exact he ▸ hv
  · intro i
    by_cases hi : i.val < l.length
    · have hg : (l ++ [v])[i] = l[i.val]'hi := (List.getElem_append_left' hi [v]).symm
      have ht : (l ++ [v]).take i.val = l.take i.val :=
        List.take_append_of_le_length (Nat.le_of_lt hi)
      rw [hg, ht]
      exact hl.2 ⟨i.val, hi⟩
    · have he : i.val = l.length := by have := i.isLt; simp only [List.length_append,
        List.length_singleton] at this; omega
      have hg : (l ++ [v])[i] = v := by simp [he]
      rw [hg, he, List.take_append_length]
      exact ⟨hs, hmin⟩

/-- A sixteen-element binary space admits a greedy independent prefix of every length up to four. -/
theorem generatedAxisE8Frame_greedy_prefix
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (hW : Nat.card W = 16) :
    ∀ n : ℕ, n ≤ 4 → ∃ l : List (Fin 8 → ZMod 2), l.length = n ∧
      generatedAxisE8FrameGreedyIn W l ∧ Nat.card (generatedAxisE8FrameListSpan l) = 2 ^ n := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨[], rfl, ?_, ?_⟩
    · simp [generatedAxisE8FrameGreedyIn]
    · simp [generatedAxisE8FrameListSpan]
  | succ n ih =>
    intro hn
    obtain ⟨l, hlen, hl, hc⟩ := ih (by omega)
    have hp : 2 ^ n < 16 := by
      have hn3 : n ≤ 3 := by omega
      interval_cases n <;> norm_num
    have hlt : Nat.card (generatedAxisE8FrameListSpan l) < Nat.card W := by rw [hc, hW]; exact hp
    obtain ⟨v, hv, hs, hm⟩ := generatedAxisE8Frame_minimum_outside W
      (generatedAxisE8FrameListSpan l) (generatedAxisE8FrameGreedyIn_span_le W l hl) hlt
    refine ⟨l ++ [v], by simp [hlen], generatedAxisE8FrameGreedyIn_append W l hl v hv hs hm, ?_⟩
    rw [generatedAxisE8FrameListSpan_append, generatedAxisE8Frame_subspace_adjoin_card _ v hs, hc]
    simp [pow_succ, mul_comm]

/-- A genuine sixteen-element binary subspace has a full four-vector greedy basis. -/
theorem generatedAxisE8Frame_greedy_basis
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (hW : Nat.card W = 16) :
    ∃ l : List (Fin 8 → ZMod 2), l.length = 4 ∧
      generatedAxisE8FrameGreedyIn W l ∧ generatedAxisE8FrameListSpan l = W := by
  obtain ⟨l, hl, hg, hc⟩ := generatedAxisE8Frame_greedy_prefix W hW 4 (by omega)
  refine ⟨l, hl, hg, ?_⟩
  have hle := generatedAxisE8FrameGreedyIn_span_le W l hg
  have hinj : Function.Injective (Submodule.inclusion hle) := Submodule.inclusion_injective hle
  have hbij : Function.Bijective (Submodule.inclusion hle) :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, by rw [hc, hW]; decide⟩
  apply le_antisymm hle
  intro v hv
  obtain ⟨w, hw⟩ := hbij.2 ⟨v, hv⟩
  have he : w.val = v := congrArg Subtype.val hw
  exact he ▸ w.property

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
