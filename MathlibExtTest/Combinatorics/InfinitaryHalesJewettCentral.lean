/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.InfinitaryHalesJewettCentral

open MetaMathlibExt

-- On a singleton alphabet, two increasing stages can both be evaluated at the unique letter.
example {D : Set (FreeSemigroup Unit)} (hD : IsCentralSet D) :
    ∃ w : ℕ → FreeSemigroup (Unit ⊕ Fin 1),
      (∀ k, Sum.inr 0 ∈ (w k).head :: (w k).tail) ∧
      FreeSemigroup.map (Sum.elim id (fun _ => ())) (w 0) *
        FreeSemigroup.map (Sum.elim id (fun _ => ())) (w 1) ∈ D := by
  let A : ℕ → Finset Unit := fun _ => {()}
  obtain ⟨w, hvar, hprod⟩ := exists_variableWords_prod_mem_of_isCentralSet A
    (fun _ _ _ => le_rfl) (fun x => ⟨0, by cases x; simp [A]⟩) 1 hD
  refine ⟨w, fun k => hvar k 0, ?_⟩
  have hm : StrictMono (fun i : Fin 2 => (i : ℕ)) := fun _ _ h => h
  simpa using hprod 1 (fun i => (i : ℕ)) (fun _ _ => ()) hm (fun _ _ => by simp [A])

-- The theorem also applies to words with no variables.
example {D : Set (FreeSemigroup Unit)} (hD : IsCentralSet D) :
    ∃ w : FreeSemigroup (Unit ⊕ Fin 0),
      FreeSemigroup.map (Sum.elim id (fun _ => ())) w ∈ D := by
  let A : ℕ → Finset Unit := fun _ => {()}
  obtain ⟨w, _, hprod⟩ := exists_variableWords_prod_mem_of_isCentralSet A
    (fun _ _ _ => le_rfl) (fun x => ⟨0, by cases x; simp [A]⟩) 0 hD
  refine ⟨w 0, ?_⟩
  have hm : StrictMono (fun i : Fin 1 => (i : ℕ)) := fun _ _ h => h
  simpa using hprod 0 (fun i => (i : ℕ)) (fun _ _ => ()) hm (fun _ i => i.elim0)
