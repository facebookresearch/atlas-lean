/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.InversionSequenceWilf201210
import Mathlib.Tactic.FinCases

open MetaMathlibExt

namespace MetaMathlibExt.invSeq_wilf_010_100_101_120_201_210

private theorem avoids_of_triples {n : ℕ} (e : Fin n → ℕ) (p : Fin 3 → ℕ)
    (h : ∀ i j k, i < j → j < k →
      ¬ ∀ a b : Fin 3, ![e i, e j, e k] a < ![e i, e j, e k] b ↔ p a < p b) :
    ¬ InvSeqContainsPattern e p := by
  rintro ⟨f, hf⟩
  apply h (f 0) (f 1) (f 2) (f.strictMono (by decide)) (f.strictMono (by decide))
  have hv (a : Fin 3) : ![e (f 0), e (f 1), e (f 2)] a = e (f a) := by
    fin_cases a <;> rfl
  simpa only [hv] using hf

-- The decreasing tail avoids the six patterns including 201, but contains 210.
example :
    let e : Fin 6 → ℕ := ![0, 0, 0, 3, 2, 1]
    (∀ i, e i ≤ i) ∧
      (∀ p ∈ ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
          : Set (Fin 3 → ℕ)),
        ¬ InvSeqContainsPattern e p) ∧ InvSeqContainsPattern e ![2, 1, 0] := by
  dsimp only
  refine ⟨by decide, ?_, ?_⟩
  · simp only [Set.forall_mem_insert, Set.forall_mem_singleton]
    repeat' constructor
    all_goals apply avoids_of_triples; decide
  · let f : Fin 3 → Fin 6 := ![3, 4, 5]
    exact ⟨OrderEmbedding.ofStrictMono f (by decide), by decide⟩

-- Reversing the same tail gives an avoider of the six patterns including 210.
example :
    let e : Fin 6 → ℕ := ![0, 0, 0, 3, 1, 2]
    (∀ i, e i ≤ i) ∧
      (∀ p ∈ ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0]}
          : Set (Fin 3 → ℕ)),
        ¬ InvSeqContainsPattern e p) ∧ InvSeqContainsPattern e ![2, 0, 1] := by
  dsimp only
  refine ⟨by decide, ?_, ?_⟩
  · simp only [Set.forall_mem_insert, Set.forall_mem_singleton]
    repeat' constructor
    all_goals apply avoids_of_triples; decide
  · let f : Fin 3 → Fin 6 := ![3, 4, 5]
    exact ⟨OrderEmbedding.ofStrictMono f (by decide), by decide⟩

-- The additional restriction matters: the three entries 2, 1, 3 form 102.
example :
    let e : Fin 5 → ℕ := ![0, 0, 2, 1, 3]
    (∀ i, e i ≤ i) ∧
      (∀ p ∈ ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 2, 0], ![2, 0, 1]} : Set (Fin 3 → ℕ)),
        ¬ InvSeqContainsPattern e p) ∧ InvSeqContainsPattern e ![1, 0, 2] := by
  dsimp only
  refine ⟨by decide, ?_, ?_⟩
  · simp only [Set.forall_mem_insert, Set.forall_mem_singleton]
    repeat' constructor
    all_goals apply avoids_of_triples; decide
  · let f : Fin 3 → Fin 5 := ![2, 3, 4]
    exact ⟨OrderEmbedding.ofStrictMono f (by decide), by decide⟩

-- Specialize the public equality of counting functions at the first nonempty size.
example :
    invSeqAvoidCount ({![0, 1, 0], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1]}
      : Set (Fin 3 → ℕ)) 1 = 1 := by
  rw [invSeq_wilf_010_100_101_102_120_201_210, invSeqAvoidCount_one]

end MetaMathlibExt.invSeq_wilf_010_100_101_120_201_210
