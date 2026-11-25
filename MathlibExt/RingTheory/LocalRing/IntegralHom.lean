/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Integral homomorphisms from a local base ring

An integral homomorphism from a local ring to a nontrivial ring reflects
units even when its kernel is nonzero. Its quotient by the actual kernel
is a nontrivial quotient of the local ring, and the induced integral
inclusion reflects units by the canonical stock theorem.

This supplies the genuine local scalar map for residue-weighted lengths
of Artinian quotients; those quotients are not assumed faithful over the
original one-dimensional base ring.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u v

namespace RingHom.IsIntegral

/-- An actual integral homomorphism from a local ring to a nontrivial ring reflects units. -/
theorem isLocalHom_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Nontrivial S]
    {f : R →+* S} (hf : f.IsIntegral) : IsLocalHom f := by
  let _ : Nontrivial (R ⧸ (RingHom.ker f)) := (RingHom.kerLift f).domain_nontrivial
  let _ : IsLocalHom (Ideal.Quotient.mk (RingHom.ker f)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let _ : IsLocalHom (RingHom.kerLift f) := hf.kerLift.isLocalHom (RingHom.kerLift_injective f)
  have h : (RingHom.kerLift f).comp (Ideal.Quotient.mk (RingHom.ker f)) = f := by
    ext x
    rfl
  rw [← h]
  infer_instance

end RingHom.IsIntegral
