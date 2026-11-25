/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.CompleteLocalRingReconstruction

open IsLocalRing MathlibExt.Algebra.CompleteLocalRingReconstructionWanted

-- Extract witnesses in different universes, retaining every quotient and both completeness proofs.
example :
    ∃ (A : Type) (B : Type 1) (_ : CommRing A) (_ : CommRing B) (_ : IsLocalRing A)
      (_ : IsLocalRing B) (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : IsAdicComplete (maximalIdeal B) B),
      (∀ n : ℕ, Nonempty (A ⧸ maximalIdeal A ^ n ≃+* B ⧸ maximalIdeal B ^ n)) ∧
        IsEmpty (A ≃+* B) := by
  classical
  by_contra h
  apply conjecture_refuted.{0, 1}
  intro A B _ _ _ _ _ _ _ _ hjets
  by_contra hAB
  exact h ⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hjets, ⟨fun e ↦ hAB ⟨e⟩⟩⟩
