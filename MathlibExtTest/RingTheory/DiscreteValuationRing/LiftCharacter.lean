/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.LiftCharacter

#check @IsDiscreteValuationRing.exists_algHom_residue_eq

open scoped TensorProduct

-- The character `χ` factors through the lift: `χ` is `χ'` followed by `O → k`.
example {O H : Type*} (K : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CommRing H] [Algebra O H] [Module.Free O H]
    [Module.Finite O H]
    (hsplit : ∀ Q : Ideal (K ⊗[O] H), Q.IsMaximal →
      Function.Surjective (Algebra.ofId K ((K ⊗[O] H) ⧸ Q)))
    (χ : H →ₐ[O] IsLocalRing.ResidueField O) :
    ∃ χ' : H →ₐ[O] O, (Algebra.ofId O (IsLocalRing.ResidueField O)).comp χ' = χ := by
  obtain ⟨χ', h, -⟩ := IsDiscreteValuationRing.exists_algHom_residue_eq K hsplit χ
  exact ⟨χ', AlgHom.ext fun x => by simpa [IsLocalRing.ResidueField.algebraMap_eq] using h x⟩
