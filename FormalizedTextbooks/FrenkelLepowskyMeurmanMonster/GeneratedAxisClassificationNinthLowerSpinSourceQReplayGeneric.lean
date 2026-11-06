/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayData

/-! Bounded single-primitive full-Q certificates replay the identical complete source word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every certified chronological prefix equals the full original Q action of that prefix. -/
theorem generatedNinth_lower_spin_source_q_replay_generic (i : Fin 11) (j : Fin 24)
    (hbase : generatedNinthLowerSpinSourceQReplayBaseCondition i j)
    (hletters : ∀ n : Fin 378, generatedNinthLowerSpinSourceQReplayLetterCondition i n)
    (hsteps : ∀ n : Fin 378, generatedNinthLowerSpinSourceQReplayStepCondition i n j)
    (hfinish : generatedNinthLowerSpinSourceQReplayFinishCondition i j) :
    generatedNinthLowerSpinSourceQEvaluation i (qCoordinateGenerator j) =
      generatedNinthLowerSpinQImage i j := by
  have hlength := generatedNinth_lower_spin_source_q_replay_length i
  have hp : ∀ n : ℕ, ∀ hn : n ≤ (generatedNinthLowerSpinSourceWord i).length,
      ((generatedNinthLowerSpinSourceWord i).reverse.take n).foldl
          (fun q l => generatedNinthLowerSpinPrimitiveQEvaluation l q) (qCoordinateGenerator j) =
        generatedNinthLowerSpinSourceQReplayPrefix i ⟨n, by omega⟩ j := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact hbase.symm
    | succ n ih =>
      intro hn
      have hnl : n < (generatedNinthLowerSpinSourceWord i).length := by omega
      have hnr : n < (generatedNinthLowerSpinSourceWord i).reverse.length := by
        simpa only [List.length_reverse] using hnl
      have hl := hletters ⟨n, by omega⟩ hnl
      rw [List.getElem?_eq_getElem hnr] at hl
      have hletter := Option.some.inj hl
      rw [List.take_succ_eq_append_getElem hnr, List.foldl_append,
        List.foldl_cons, List.foldl_nil, ih (by omega), hletter]
      exact hsteps ⟨n, by omega⟩ hnl
  rw [generatedNinthLowerSpinSourceQEvaluation, List.foldr_eq_foldl_reverse]
  have hf := hp (generatedNinthLowerSpinSourceWord i).length (Nat.le_refl _)
  have ht : (generatedNinthLowerSpinSourceWord i).reverse.take
      (generatedNinthLowerSpinSourceWord i).length =
        (generatedNinthLowerSpinSourceWord i).reverse := by
    rw [← (show (generatedNinthLowerSpinSourceWord i).reverse.length =
      (generatedNinthLowerSpinSourceWord i).length from List.length_reverse), List.take_length]
  rw [ht] at hf
  exact hf.trans hfinish

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
