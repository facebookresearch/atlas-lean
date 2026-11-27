/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.Localization

@[expose] public section

universe u v

/-- Consumer with the original binders. -/
example {C : Type u} [CommRing C] (𝔪 : Ideal C) [𝔪.IsMaximal] :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪))
          (Localization.AtPrime 𝔪) ≃+* AdicCompletion 𝔪 C,
      ∀ c : C, e (algebraMap (Localization.AtPrime 𝔪) _
          (algebraMap C (Localization.AtPrime 𝔪) c)) =
        algebraMap C (AdicCompletion 𝔪 C) c :=
  Ideal.IsMaximal.exists_adicCompletion_localization_ringEquiv 𝔪

/-- Higher-universe consumer. -/
example {C : Type v} [CommRing C] (𝔪 : Ideal C) [𝔪.IsMaximal] :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪))
          (Localization.AtPrime 𝔪) ≃+* AdicCompletion 𝔪 C,
      ∀ c : C, e (algebraMap (Localization.AtPrime 𝔪) _
          (algebraMap C (Localization.AtPrime 𝔪) c)) =
        algebraMap C (AdicCompletion 𝔪 C) c :=
  Ideal.IsMaximal.exists_adicCompletion_localization_ringEquiv 𝔪

/-- Boundary use: the compatibility identity at a chosen element. -/
example {C : Type*} [CommRing C] (𝔪 : Ideal C) [𝔪.IsMaximal] (c : C) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪))
          (Localization.AtPrime 𝔪) ≃+* AdicCompletion 𝔪 C,
      e (algebraMap (Localization.AtPrime 𝔪) _
          (algebraMap C (Localization.AtPrime 𝔪) c)) =
        algebraMap C (AdicCompletion 𝔪 C) c := by
  obtain ⟨e, he⟩ := Ideal.IsMaximal.exists_adicCompletion_localization_ringEquiv 𝔪
  exact ⟨e, he c⟩
