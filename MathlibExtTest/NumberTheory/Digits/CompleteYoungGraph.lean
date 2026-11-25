/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.CompleteYoungGraph

namespace MetaMathlibExt

private instance {g k : ℕ} (u : Option (Fin k × Fin k)) (v : Fin k × Fin k)
    (d : Fin g × Fin g) : Decidable (IsYoungCarryEdge u v d) := by
  unfold IsYoungCarryEdge
  dsimp only
  infer_instance

-- At the start the zero label is forbidden; at ordinary [0,0] it is a loop.
example : IsYoungCarryEdge (g := 5) (k := 2) (some (0, 0)) (0, 0) (0, 0) :=
  by decide

example : ¬ IsYoungCarryEdge (g := 5) (k := 2) none (0, 0) (0, 0) := by decide

-- Sloane's K₂ example. This checks the retained nodes, both loops, both
-- directions between the nodes, and the single allowed target from the start.
example : IsCompleteYoungGraph 5 2 2 := by
  unfold IsCompleteYoungGraph
  extract_lets adj reaches pivot retained ordinary
  let z : Fin 2 × Fin 2 := (0, 0)
  let a : Fin 2 × Fin 2 := (1, 1)
  have hz : adj (some a) (some z) := ⟨(3, 1), by decide⟩
  have ha : adj none (some a) := ⟨(1, 3), by decide⟩
  have reach_a : reaches none (some a) := Relation.ReflTransGen.single ha
  have mem_a : a ∈ ordinary := ⟨reach_a, Or.inl (Or.inl rfl)⟩
  have mem_z : z ∈ ordinary := ⟨reach_a.tail hz, Or.inl (Or.inl rfl)⟩
  have closed : ∀ u : Option (Fin 2 × Fin 2), ∀ v : Fin 2 × Fin 2,
      (u = none ∨ u = some (0, 0) ∨ u = some (1, 1)) →
      (∃ d : Fin 5 × Fin 5, IsYoungCarryEdge u v d) →
      v = (0, 0) ∨ v = (1, 1) := by decide
  have hordinary : ordinary = {z, a} := by
    ext v
    constructor
    · intro hv
      have hreach : reaches none (some v) := hv.1
      have hinv : ∀ w, reaches none w → w = none ∨ w = some z ∨ w = some a := by
        intro w hw
        induction hw with
        | refl => exact Or.inl rfl
        | @tail b c _ e ih =>
          cases c with
          | none => exact Or.inl rfl
          | some v =>
            exact Or.inr (by simpa only [Option.some.injEq] using closed b v ih e)
      simpa using hinv (some v) hreach
    · intro hv
      rcases (show v = z ∨ v = a by simpa using hv) with h | h
      · subst v; exact mem_z
      · subst v; exact mem_a
  refine ⟨by decide, by decide, ⟨.refl, Or.inr ⟨some a, Or.inl rfl, reach_a⟩⟩,
    ?_, z, mem_z, rfl, rfl, ?_, ?_⟩
  · rw [hordinary]
    exact Set.ncard_pair (by decide)
  · intro u hu v hv
    simp only [hordinary, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    all_goals dsimp only [z, a]
    · exact ⟨(0, 0), by decide, by decide⟩
    · exact ⟨(1, 3), by decide, by decide⟩
    · exact ⟨(3, 1), by decide, by decide⟩
    · exact ⟨(4, 4), by decide, by decide⟩
  · have h : ∀ v : Fin 2 × Fin 2, (v = (0, 0) ∨ v = (1, 1)) →
        ((∃ d : Fin 5 × Fin 5, IsYoungCarryEdge none v d) ↔ v ≠ (0, 0)) :=
      by decide
    simpa [hordinary, z, a] using h

-- In the (3,2) 1089 graph, the reachable carry pair [0,1] precedes a
-- pivot but has no loop, so no choice of the order makes the graph complete.
example (m : ℕ) : ¬ IsCompleteYoungGraph 3 2 m := by
  unfold IsCompleteYoungGraph
  extract_lets adj reaches pivot retained ordinary
  let v : Fin 2 × Fin 2 := (0, 1)
  have first : adj none (some v) := ⟨(1, 2), by decide⟩
  have next : adj (some v) (some (1, 1)) := ⟨(0, 1), by decide⟩
  have hv : v ∈ ordinary := ⟨.single first,
    Or.inr ⟨some (1, 1), Or.inl rfl, .single next⟩⟩
  rintro ⟨_, _, _, _, _, _, _, _, hcomplete, _⟩
  obtain ⟨d, hd, _⟩ := hcomplete v hv v hv
  have noLoop :
      ¬ ∃ d : Fin 3 × Fin 3, IsYoungCarryEdge (k := 2) (some (0, 1)) (0, 1) d :=
    by decide
  exact noLoop ⟨d, hd⟩

end MetaMathlibExt
