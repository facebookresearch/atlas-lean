/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SigmaSubnormalJoinConjugateKourovka19Problem84

open MathlibExt.GroupTheory.KourovkaNotebookShared
open MathlibExt.GroupTheory.SigmaSubnormalJoinConjugateKourovka19Problem84Wanted

-- Extract a finite witness together with both subgroup-chain conditions.
example : ∃ (I : Type) (σ : I → Set ℕ), IsPrimePartition σ ∧
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (A : Subgroup G),
      (∀ x : G, IsSigmaSubnormal σ (A.subgroupOf (A ⊔ A.map (MulAut.conj x).toMonoidHom))) ∧
        ¬ IsSigmaSubnormal σ A := by
  classical
  by_contra h
  apply sigmaSubnormalFromJoinsWithConjugates_refuted
  intro I σ hσ G _ _ A hjoin
  by_contra hA
  exact h ⟨I, σ, hσ, G, inferInstance, inferInstance, A, hjoin, hA⟩
