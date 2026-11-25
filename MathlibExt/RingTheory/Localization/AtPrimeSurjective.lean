/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Surjectivity after localization at corresponding primes

A surjective ring map induces a surjective map between the local rings at
a target prime and its inverse image. Lifting the numerator and denominator
of a target fraction gives a preimage; the lifted denominator lies outside
the inverse-image prime.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Localization

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The canonical local ring map of an actual quotient map is surjective,
with the target prime and its original inverse image retained. -/
theorem localRingHom_surjective
    (f : R →+* S) (hf : Function.Surjective f) (p : Ideal S) [p.IsPrime] :
    Function.Surjective (localRingHom (p.comap f) p f rfl) := by
  intro z
  obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
  obtain ⟨a, ha⟩ := hf s
  obtain ⟨b, hb⟩ := hf t.val
  have hbt : b ∈ (p.comap f).primeCompl := by
    change f b ∉ p
    rw [hb]
    exact t.property
  refine ⟨IsLocalization.mk' (Localization.AtPrime (p.comap f)) a ⟨b, hbt⟩, ?_⟩
  rw [localRingHom_mk', ha]
  congr 1
  exact Subtype.ext hb

end Localization
