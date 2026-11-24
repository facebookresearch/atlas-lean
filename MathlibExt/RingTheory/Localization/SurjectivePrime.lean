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
# Kernels of maps between prime localizations

A surjective homomorphism of commutative semirings maps the complement of
the inverse-image prime ideal onto the complement of the target prime.  The
general localization-kernel theorem therefore identifies the kernel of the
induced local-ring homomorphism with the extension of the original kernel.

The source and target semirings may live in independent universes.  This
file introduces no algebraic-geometry specialization or additional wrapper.

## Main declaration

* `Localization.ker_localRingHom_eq_map_ker_of_surjective`
-/

@[expose] public section

set_option autoImplicit false

namespace Localization

universe u v

/-- The map on prime localizations induced by a surjective homomorphism of
commutative semirings has kernel equal to the extension of the original
kernel. -/
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
