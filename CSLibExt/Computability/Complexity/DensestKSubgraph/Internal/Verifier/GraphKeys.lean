/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Certificate
public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.Intern

/-! # Dictionary invariants for the DENSEST k-SUBGRAPH verifier -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.GraphKeys

open MetaMathlibExt BitstringEncoding
open MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph

/- Normalize an unordered edge to a key ordered by its endpoint values. -/
def key (e : ℕ × ℕ) : ℕ × ℕ := (min e.1 e.2, max e.1 e.2)

private theorem key_swap (e : ℕ × ℕ) : key e.swap = key e := by
  cases e
  simp [key, min_comm, max_comm]

private theorem key_eq_iff (e f : ℕ × ℕ) : key e = key f ↔ e = f ∨ e = f.swap := by
  constructor
  · rcases e with ⟨a, b⟩
    rcases f with ⟨u, v⟩
    intro he
    rcases le_total a b with h₁ | h₁ <;> rcases le_total u v with h₂ | h₂
    · simpa [key, min_eq_left h₁, max_eq_right h₁, min_eq_left h₂, max_eq_right h₂] using
        Or.inl (b := (a, b) = (u, v).swap) he
    · simp only [key, min_eq_left h₁, max_eq_right h₁, min_eq_right h₂, max_eq_left h₂] at he
      exact Or.inr he
    · simp only [key, min_eq_right h₁, max_eq_left h₁, min_eq_left h₂, max_eq_right h₂] at he
      exact Or.inr (congrArg Prod.swap he)
    · simp only [key, min_eq_right h₁, max_eq_left h₁, min_eq_right h₂, max_eq_left h₂] at he
      exact Or.inl (congrArg Prod.swap he)
  · rintro (rfl | rfl)
    · rfl
    · exact key_swap f

/- The binary keys detect same-direction and reversed duplicate edges alike. -/
theorem wellFormed_iff_keys (i : DensestKSubgraphInstance) :
    WellFormed i ↔ (i.2.1.map key).Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 := by
  constructor
  · rintro ⟨hnd, hw⟩
    refine ⟨(List.nodup_map_iff_inj_on hnd).2 ?_, fun e he => ⟨(hw e he).1,
      (hw e he).2.1, (hw e he).2.2.1⟩⟩
    intro e he f hf heq
    rcases (key_eq_iff e f).mp heq with h | h
    · exact h
    · apply False.elim ((hw f hf).2.2.2 ?_)
      rw [h] at he
      exact he
  · rintro ⟨hnd, hv⟩
    have hinj := List.inj_on_of_nodup_map hnd
    refine ⟨hnd.of_map _, fun e he => ⟨(hv e he).1, (hv e he).2.1, (hv e he).2.2, ?_⟩⟩
    intro hr
    have h := hinj he hr (key_swap e).symm
    exact (hv e he).2.2 (congrArg Prod.fst h)

/- Inserting only an absent key leaves the list free of duplicate entries. -/
def insertKey {α : Type} [DecidableEq α] (xs : List α) (x : α) : List α :=
  if x ∈ xs then xs else xs ++ [x]

private theorem nodup_insertKey {α : Type} [DecidableEq α] {xs : List α} (h : xs.Nodup) (x : α) :
    (insertKey xs x).Nodup := by
  by_cases hx : x ∈ xs
  · simpa [insertKey, hx] using h
  · simp only [insertKey, hx, ↓reduceIte, List.nodup_append, List.nodup_singleton, h, true_and]
    intro a ha b hb e
    obtain rfl := List.mem_singleton.mp hb
    exact hx (e ▸ ha)

private theorem mem_insertKey {α : Type} [DecidableEq α] (xs : List α) (x y : α) :
    y ∈ insertKey xs x ↔ y = x ∨ y ∈ xs := by
  by_cases h : x ∈ xs <;> simp [insertKey, h, or_comm]; grind

/- Track distinct vertices by inserting both endpoints of each selected edge. -/
def vertexKeys (es : List (ℕ × ℕ)) : List ℕ :=
  es.foldl (fun xs e => insertKey (insertKey xs e.1) e.2) []

private theorem vertex_fold (es : List (ℕ × ℕ)) (xs : List ℕ) (hn : xs.Nodup) :
    let vs := es.foldl (fun xs e => insertKey (insertKey xs e.1) e.2) xs
    vs.Nodup ∧ ∀ y, y ∈ vs ↔ y ∈ xs ∨ ∃ e ∈ es, e.1 = y ∨ e.2 = y := by
  induction es generalizing xs with
  | nil => simp [hn]
  | cons e es ih =>
    obtain ⟨hnd, hm⟩ := ih _ (nodup_insertKey (nodup_insertKey hn e.1) e.2)
    constructor
    · exact hnd
    · intro y
      simp only [List.foldl_cons, hm, mem_insertKey, List.mem_cons]
      grind

/- The number of dictionary entries is exactly the number of distinct required vertices. -/
theorem vertexKeys_length (es : List (ℕ × ℕ)) : (vertexKeys es).length = (endpoints es).card := by
  obtain ⟨hn, hm⟩ := vertex_fold es [] List.nodup_nil
  change (vertexKeys es).Nodup at hn
  have he : (vertexKeys es).toFinset = endpoints es := by
    ext y
    rw [List.mem_toFinset, vertexKeys, hm]
    simp only [List.not_mem_nil, false_or, endpoints, Finset.mem_union, List.mem_toFinset,
      List.mem_map]
    grind
  rw [← he, List.toFinset_card_of_nodup hn]

/- The abstract membership behind lookup is unchanged by an injective canonical encoding. -/
theorem mem_encoded_keys {α : Type} [BitstringEncoding α] (a : α) (xs : List α) :
    bitEncode a ∈ xs.map bitEncode ↔ a ∈ xs := by
  constructor
  · intro h
    obtain ⟨b, hb, e⟩ := List.mem_map.mp h
    have hba := congrArg (bitDecode (α := α)) e
    simp only [bitDecode_bitEncode, Option.some.injEq] at hba
    exact hba ▸ hb
  · exact List.mem_map_of_mem (f := bitEncode)

end Cslib.Complexity.DensestKSubgraph.Internal.GraphKeys
