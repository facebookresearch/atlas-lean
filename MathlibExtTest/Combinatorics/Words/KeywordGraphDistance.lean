/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.KeywordGraphDistance

namespace MetaMathlibExt.keywordGraph_edist_eq_of_intertwining

-- Flipping 00 at the first position produces 11 in one step.
example (b : Fin 2 → Bool) (f : Equiv.Perm (Fin 2 → Bool)) (σ : Equiv.Perm (Fin 2))
    (hf : ∀ (u : Fin 2 → Bool) (i : Fin 2),
      f (keywordSimpleMap (fun _ : Fin 2 => false) i u) = keywordSimpleMap b (σ i) (f u)) :
    (keywordGraph b 2).edist (f (fun _ => false)) (f (fun _ => true)) = 1 := by
  let zeroWord : Fin 2 → Bool := fun _ => false
  rw [← keywordGraph_edist_eq_of_intertwining zeroWord b f σ hf]
  apply SimpleGraph.edist_eq_one_iff_adj.mpr
  refine (keywordGraph_adj ..).mpr ⟨by decide, Or.inl ⟨0, ?_⟩⟩
  have ha : KeywordApplicable zeroWord 0 zeroWord := ⟨by decide, Or.inl (fun _ => rfl)⟩
  funext j
  rw [keywordSimpleMap_apply_of_applicable zeroWord 0 zeroWord ha]
  simp [zeroWord, show j.val ≤ 1 by omega]

-- No length-three keyword fits in a two-letter word, and distinct words have infinite distance.
example (a b : Fin 3 → Bool) (f : Equiv.Perm (Fin 2 → Bool)) (σ : Equiv.Perm (Fin 2))
    (u v : Fin 2 → Bool) (hne : u ≠ v) : (keywordGraph b 2).edist (f u) (f v) = ⊤ := by
  have fixed (c : Fin 3 → Bool) (i : ℕ) (x : Fin 2 → Bool) : keywordSimpleMap c i x = x :=
    keywordSimpleMap_of_not_applicable c i x (fun ⟨h, _⟩ => by omega)
  rw [← keywordGraph_edist_eq_of_intertwining a b f σ (fun x i => by rw [fixed, fixed])]
  have empty : keywordGraph a 2 = ⊥ := by
    apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
    intro x y
    simp [keywordGraph_adj, fixed, eq_comm]
  rw [empty]
  exact SimpleGraph.edist_bot_of_ne hne

end MetaMathlibExt.keywordGraph_edist_eq_of_intertwining
