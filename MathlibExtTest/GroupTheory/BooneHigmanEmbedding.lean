/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.GroupTheory.BooneHigmanEmbedding
import Mathlib.GroupTheory.SpecificGroups.Cyclic

open MathlibExt.GroupTheory.BooneHigmanEmbeddingWanted.GroupTheory.BooneHigmanEmbedding
open MathlibExt.GroupTheory.WordProblemSolvableShared

-- With no generators the source group can be trivial, even though the simple group is nontrivial.
example {H K : Type*} [Group H] [Group K] [IsSimpleGroup H] [Group.IsFinitelyPresented K]
    (g : H →* K) (hg : Function.Injective g) :
    WordProblemSolvable (1 : FreeGroup (Fin 0) →* Unit) :=
  boone_higman_embedding (1 : Unit →* H) (fun _ _ _ => Subsingleton.elim ..) g hg 1
    (fun _ => ⟨1, Subsingleton.elim ..⟩)

-- Embed the simple group of order two in a proper direct factor of the ambient group.
-- The decider rejects the nontrivial generator and accepts its square.
example : ∃ d : List (Fin 2 × Bool) → Bool,
    Computable d ∧ d [(1, true)] = false ∧ d [(1, true), (1, true)] = true := by
  let C := Multiplicative (ZMod 2)
  have : IsSimpleGroup C := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isSimpleGroup_of_prime_card (p := 2) (by simp [C, Nat.card_eq_fintype_card])
  let φ : FreeGroup (Fin 2) →* C := FreeGroup.lift fun i => Multiplicative.ofAdd (i : ZMod 2)
  have hφ : Function.Surjective φ := FreeGroup.lift_surjective_of_surjective fun x => ⟨x, rfl⟩
  have hdec := boone_higman_embedding (MonoidHom.id C) Function.injective_id (MonoidHom.inl C C)
    (fun _ _ h => congrArg Prod.fst h) φ (hsurj := hφ)
  obtain ⟨d, hd, hcorrect⟩ := ComputablePred.computable_iff.mp hdec
  refine ⟨d, hd, ?_, ?_⟩
  · have h : φ (FreeGroup.mk [(1, true)]) ≠ 1 := by decide
    simpa [h] using congrFun hcorrect [(1, true)]
  · have h : φ (FreeGroup.mk [(1, true), (1, true)]) = 1 := by decide
    simpa [h] using congrFun hcorrect [(1, true), (1, true)]
