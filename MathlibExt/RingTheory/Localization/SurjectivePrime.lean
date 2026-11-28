/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Kernels under prime localization

Let `φ : A →+* B` be a surjective homomorphism of commutative semirings and let `p` be a prime
ideal of `B`. Its inverse image `q = φ⁻¹(p)` is prime, and `φ` maps the complement of `q` onto
the complement of `p`.

The induced map `A_q → B_p` has kernel equal to the ideal generated in `A_q` by the image of
`ker φ` under the localization map `A → A_q`.

Reference for ring localizations: Atiyah and Macdonald, *Introduction to Commutative Algebra*,
Chapter 3.
-/

@[expose] public section

set_option autoImplicit false

namespace Localization

universe u v

/-- Let `A,B` be commutative semirings, `φ : A →+* B` a surjective homomorphism, and `p : Ideal B`
a prime ideal. Put `q = p.comap φ`. The induced prime-localization homomorphism `φ_loc :
Localization.AtPrime q → Localization.AtPrime p` satisfies `RingHom.ker φ_loc = (RingHom.ker
φ).map (algebraMap A (Localization.AtPrime q))`. -/
theorem ker_localRingHom_eq_map_ker_of_surjective
    {A : Type u} {B : Type v} [CommSemiring A] [CommSemiring B]
    (φ : A →+* B) (hφ : Function.Surjective φ)
    (p : Ideal B) [p.IsPrime] :
    RingHom.ker
        (Localization.localRingHom (p.comap φ) p φ rfl) =
      (RingHom.ker φ).map
        (algebraMap A (Localization.AtPrime (p.comap φ))) := by
  let _ : (p.comap φ).IsPrime := Ideal.IsPrime.comap φ
  have hsub : Submonoid.map φ (p.comap φ).primeCompl = p.primeCompl :=
    p.map_primeCompl_comap_of_surjective φ hφ
  exact IsLocalization.ker_map
    (S := Localization.AtPrime (p.comap φ))
    (Q := Localization.AtPrime p) φ hsub

end Localization
