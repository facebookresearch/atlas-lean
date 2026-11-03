/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.AdicCompletion.LocalRing

@[expose] public section

example (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal R

example {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) :
    (I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).comap
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) = I :=
  IsLocalRing.comap_map_adicCompletion_eq I

open AdicCompletion IsLocalRing

section Quotients

variable {A k : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing k] [Algebra k A]

example (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    quotientMaximalIdealPowAlgHom k n (Ideal.Quotient.mk _ x) =
      evalₐ (maximalIdeal A) n x :=
  quotientMaximalIdealPowAlgHom_mk k n x

example (x : AdicCompletion (maximalIdeal A) A) :
    quotientMaximalIdealPowAlgEquiv k 0 (Ideal.Quotient.mk _ x) =
      evalₐ (maximalIdeal A) 0 x :=
  quotientMaximalIdealPowAlgEquiv_mk k 0 x

example (a : A) :
    quotientMaximalIdealPowAlgEquiv k 1
        (Ideal.Quotient.mk _ (algebraMap A (AdicCompletion (maximalIdeal A) A) a)) =
      Ideal.Quotient.mk _ a :=
  quotientMaximalIdealPowAlgEquiv_mk_algebraMap k 1 a

example (a : A) :
    quotientMaximalIdealPowAlgEquiv A 1
        (Ideal.Quotient.mk _ (algebraMap A (AdicCompletion (maximalIdeal A) A) a)) =
      Ideal.Quotient.mk _ a :=
  quotientMaximalIdealPowAlgEquiv_mk_algebraMap A 1 a

example (r : k)
    (x : AdicCompletion (maximalIdeal A) A ⧸
      maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ 1) :
    quotientMaximalIdealPowAlgEquiv k 1 (r • x) =
      r • quotientMaximalIdealPowAlgEquiv k 1 x := by
  exact map_smul (quotientMaximalIdealPowAlgEquiv k 1) r x

example {x : AdicCompletion (maximalIdeal A) A}
    (hx : x ∈ (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A))) :
    IsUnit (1 + x) :=
  isUnit_one_add_of_mem_map (maximalIdeal A) (IsNoetherian.noetherian _) hx

example {u x : AdicCompletion (maximalIdeal A) A} (hu : IsUnit u)
    (hx : x ∈ (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A))) :
    IsUnit (u + x) :=
  isUnit_add_of_mem_map (maximalIdeal A) (IsNoetherian.noetherian _) hu hx

end Quotients

section Transport

variable {A k B : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing k] [Algebra k A] [CommRing B] [IsLocalRing B] [Algebra k B]
  (Φ : AdicCompletion (maximalIdeal A) A ≃ₐ[k] B)

example (x : AdicCompletion (maximalIdeal A) A) :
    IsUnit (Φ x) ↔ IsUnit x :=
  isUnit_map_iff Φ.toAlgHom x

example (a : A) :
    quotientMaximalIdealPowAlgEquivOfAlgEquiv Φ 0
        (Ideal.Quotient.mk _ (Φ (algebraMap A _ a))) = Ideal.Quotient.mk _ a :=
  quotientMaximalIdealPowAlgEquivOfAlgEquiv_mk Φ 0 a

example (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    quotientMaximalIdealPowAlgEquivOfAlgEquiv Φ n (Ideal.Quotient.mk _ (Φ x)) =
      quotientMaximalIdealPowAlgEquiv k n (Ideal.Quotient.mk _ x) := by
  rw [quotientMaximalIdealPowAlgEquivOfAlgEquiv, AlgEquiv.trans_apply,
    ← Ideal.quotientEquivAlg_mk
      (J := maximalIdeal B ^ n) (f := Φ)
      (hIJ := by rw [Ideal.map_pow, map_maximalIdeal_algEquiv]),
    AlgEquiv.symm_apply_apply]

end Transport
