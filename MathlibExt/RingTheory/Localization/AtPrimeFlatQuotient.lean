/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.RingTheory.Localization.AtPrimeSurjective
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Local isomorphisms of flat quotient maps

The local ring map induced by a flat surjective ring map at a target prime
is surjective. Local flatness makes it faithfully flat and hence injective.
This gives the local diagonal comparison for étale graph resolutions.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Localization

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The actual canonical local ring map of a flat quotient is bijective,
with its original target prime and inverse-image prime retained. -/
theorem localRingHom_bijective_of_flat_of_surjective
    (f : R →+* S) (hf : Function.Surjective f) (hflat : f.Flat)
    (p : Ideal S) [p.IsPrime] :
    Function.Bijective (localRingHom (p.comap f) p f rfl) := by
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := hflat
  let q := p.comap f
  let : p.LiesOver q := ⟨rfl⟩
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime p) :=
    Localization.AtPrime.algebraOfLiesOver q p
  let : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime p)) := by
    change IsLocalHom (localRingHom q p f rfl)
    exact isLocalHom_localRingHom q p f rfl
  let : Module.FaithfullyFlat (Localization.AtPrime q) (Localization.AtPrime p) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨?_, localRingHom_surjective f hf p⟩
  exact FaithfulSMul.algebraMap_injective (Localization.AtPrime q) (Localization.AtPrime p)

end Localization
