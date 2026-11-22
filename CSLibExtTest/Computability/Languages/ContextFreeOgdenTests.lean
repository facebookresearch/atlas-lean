/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Ogden

/-!
# Tests for Ogden's lemma

* `marks` on concrete marked words.
* Ogden's lemma with every letter marked gives the pumping lemma (with `|vxy| ≤ n` and
  `vy ≠ []`).
* Ogden's lemma instantiated on a concrete context-free language (the statement elaborates at a
  concrete alphabet).
-/

@[expose] public section

namespace Cslib.Language.OgdenTests

example : marks [('a', true), ('b', false), ('c', true)] = 2 := by decide
example : marks [('a', false), ('b', false)] = 0 := by decide

/-- Marking every letter recovers the pumping lemma. -/
example {T : Type*} {L : Language T} (hL : L.IsContextFree) :
    ∃ n : ℕ, ∀ w ∈ L, n ≤ w.length → ∃ u v x y z : List T, w = u ++ v ++ x ++ y ++ z ∧
      v ++ y ≠ [] ∧ (v ++ x ++ y).length ≤ n ∧
      ∀ i : ℕ, u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++ z ∈ L := by
  obtain ⟨n, -, hn⟩ := IsContextFree.ogden hL
  refine ⟨n, fun w hw hlen => ?_⟩
  have hall : marks (w.map fun a => (a, true)) = w.length := by
    simp [marks, List.countP_map, Function.comp_def]
  obtain ⟨u, v, x, y, z, hsplit, hpos, hle, hpump⟩ :=
    hn (w.map fun a => (a, true)) (by simpa [List.map_map, Function.comp_def] using hw)
      (by omega)
  have hmarked : ∀ p ∈ v ++ x ++ y, p.2 = true := by
    intro p hp
    have hp' : p ∈ w.map fun a => (a, true) := by
      rw [hsplit]
      simp only [List.mem_append] at hp ⊢
      tauto
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hp'
    rfl
  have hlen' : marks (v ++ x ++ y) = (v ++ x ++ y).length :=
    List.countP_eq_length.2 fun p hp => by simpa using hmarked p hp
  refine ⟨u.map Prod.fst, v.map Prod.fst, x.map Prod.fst, y.map Prod.fst, z.map Prod.fst,
    ?_, ?_, ?_, fun i => by simpa [List.map_flatten, List.map_replicate] using hpump i⟩
  · simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) hsplit
  · intro hvy
    rw [← List.map_append, List.map_eq_nil_iff] at hvy
    rw [hvy] at hpos
    simp at hpos
  · rw [← List.map_append, ← List.map_append, List.length_map, ← hlen']
    exact hle

/-- Ogden's lemma for the context-free language `{"ab"}`. -/
example : ∃ n : ℕ, 0 < n ∧ ∀ w : List (Char × Bool),
    w.map Prod.fst ∈ ({['a', 'b']} : Language Char) →
    n ≤ marks w → ∃ u v x y z : List (Char × Bool), w = u ++ v ++ x ++ y ++ z ∧
      0 < marks (v ++ y) ∧ marks (v ++ x ++ y) ≤ n ∧
      ∀ i : ℕ, (u ++ (List.replicate i v).flatten ++ x ++ (List.replicate i y).flatten ++
        z).map Prod.fst ∈ ({['a', 'b']} : Language Char) :=
  IsContextFree.ogden (IsContextFree.singleton_word _)

end Cslib.Language.OgdenTests
