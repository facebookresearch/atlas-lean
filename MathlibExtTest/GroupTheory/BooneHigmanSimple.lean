/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.GroupTheory.BooneHigmanSimple
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.SpecificGroups.Cyclic

open MathlibExt.GroupTheory.BooneHigmanSimpleWanted.GroupTheory.BooneHigmanSimpleProblem
open MathlibExt.GroupTheory.WordProblemSolvableShared

-- A presentation of the group of order two has a decider that returns both answers.
example : ∃ n : ℕ, ∃ f : List (Fin n × Bool) → Bool,
    Computable f ∧ f [] = true ∧ ∃ w, f w = false := by
  let G := Multiplicative (ZMod 2)
  have : IsSimpleGroup G := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isSimpleGroup_of_prime_card (p := 2) (by simp [G, Nat.card_eq_fintype_card])
  obtain ⟨n, φ, hsurj, hker⟩ := Group.IsFinitelyPresented.out (G := G)
  have hdec : WordProblemSolvable φ := boone_higman_simple φ (_hsurj := hsurj) (_hker := hker)
  obtain ⟨f, hf, hcorrect⟩ := ComputablePred.computable_iff.mp hdec
  refine ⟨n, f, hf, ?_, ?_⟩
  · simpa [← FreeGroup.one_eq_mk] using congrFun hcorrect []
  · obtain ⟨a, ha⟩ := exists_ne (1 : G)
    obtain ⟨g, hg⟩ := hsurj a
    refine ⟨g.toWord, ?_⟩
    simpa [FreeGroup.mk_toWord, hg, ha] using congrFun hcorrect g.toWord
