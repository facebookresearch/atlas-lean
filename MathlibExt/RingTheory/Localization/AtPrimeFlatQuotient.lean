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
# Canonical local isomorphisms of flat surjections

Let f:R→S be a flat surjective homomorphism of commutative rings in independent universes. For a
prime p of S and q=f⁻¹(p), the canonical local homomorphism R_q→S_p is surjective. It is a flat
local map and therefore faithfully flat, giving injectivity as well.

Thus the canonical target-prime local map is bijective. No global locality or Noetherian
condition on R,S is imposed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Localization

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Let R,S be commutative rings in independent universes u,v, f:R→S a flat surjective ring
homomorphism and p⊂S a prime ideal. Put q=f⁻¹(p). The canonical local homomorphism R_q→S_p
induced by f is bijective. Surjectivity localizes, and flatness together with the
local-homomorphism property gives faithful flatness and hence injectivity. -/
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
