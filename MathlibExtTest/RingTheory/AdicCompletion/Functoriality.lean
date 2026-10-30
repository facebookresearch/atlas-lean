/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.Functoriality

@[expose] public section

universe u v

example {B : Type*} [CommRing B] (𝔪 : Ideal B) {S : Type*} [CommRing S] (J : Ideal S)
    [IsAdicComplete J S] (ev : B →+* S)
    (hcont : ∀ k : ℕ, ∃ n : ℕ, 𝔪 ^ n ≤ (J ^ k).comap ev) :
    ∃ ψ : AdicCompletion 𝔪 B →+* S, ψ.comp (algebraMap B (AdicCompletion 𝔪 B)) = ev :=
  AdicCompletion.exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap 𝔪 J ev hcont

example {R : Type u} [CommRing R] {S : Type v} [CommRing S] (I : Ideal R) (e : R ≃+* S) :
    ∃ ê : AdicCompletion I R ≃+* AdicCompletion (I.map e) S,
      ∀ r : R, ê (algebraMap R (AdicCompletion I R) r) =
        algebraMap S (AdicCompletion (I.map e) S) (e r) :=
  AdicCompletion.exists_ringEquiv_map_of_ringEquiv I e

example {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) :
    ∃ ê : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ r : R, ê (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
        algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (e r) :=
  IsLocalRing.exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv e
