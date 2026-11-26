/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import all CSLibExt.Computability.Complexity.KeyTheorems.BakerGillSolovay

namespace MetaMathlibExt.Complexity.KeyTheorems.BakerGillSolovay

open Cslib.Complexity.Classes Polynomial

example :
    (∃ O : List Bool → Bool, PWithOracle O ≠ NPWithOracle O) ∧
      (∃ O : List Bool → Bool, PWithOracle O = NPWithOracle O) :=
  baker_gill_solovay

example :
    ∃ A B : List Bool → Bool, A ≠ B ∧
      PWithOracle A ≠ NPWithOracle A ∧ PWithOracle B = NPWithOracle B := by
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := baker_gill_solovay
  exact ⟨A, B, fun h => hA (h.symm ▸ hB), hA, hB⟩

-- The oracle model: one query about the encoded input, read back from the history, decides the
-- oracle's answer, so for every oracle `O` the language `x ↦ O ⟨x, []⟩` lies in `P^O`.
example (O : List Bool → Bool) : (fun x => O (query [] (x, []))) ∈ PWithOracle O := by
  refine ⟨1, C 6 * X + C 1, query [], lastAnswer, query_poly [], lastAnswer_poly, fun x => ?_⟩
  have hq : (query [] (x, [])).length ≤ (C 6 * X + C 1 : ℕ[X]).eval x.length := by
    rw [length_query]
    simp [show BitstringEncoding.bitEncode ([] : History) = [] from rfl]
  have hlast := lastAnswer_append x [] (query [] (x, [])) (O (query [] (x, [])))
  rw [List.nil_append] at hlast
  simp only [eval_one, evalOracle, ite_eq_left hq, List.nil_append, hlast]

-- The diagonal language asks for a witness address that the oracle accepts; the oracle that
-- accepts nothing gives the empty language, and accepting one short witness puts `x` in it.
example : witnessLanguage (fun _ => false) = fun _ => false := by
  funext x
  simp [witnessLanguage]

example (x w : List Bool) (hw : w.length ≤ x.length + 1) :
    witnessLanguage (fun q => decide (q = witnessAddress x w)) x = true := by
  simp only [witnessLanguage, decide_eq_true_eq]
  exact ⟨w, hw, by simp⟩

end MetaMathlibExt.Complexity.KeyTheorems.BakerGillSolovay
