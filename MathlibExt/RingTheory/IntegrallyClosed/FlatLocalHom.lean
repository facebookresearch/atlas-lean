/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom.lean` and
`P2M/Sol/S_IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Algebra.Group.Units.Hom

import MathlibExt.RingTheory.IntegrallyClosed.FaithfullyFlat

/-!
# Integrally closed rings under flat local homomorphisms

A domain and integrally closed target of a flat local homomorphism from a
local ring forces the source to be a domain and integrally closed, by
faithful flatness.
-/

@[expose] public section

universe u v

/-- A flat local homomorphism from a local ring to a domain and integrally
closed local ring forces the source to be a domain and integrally closed.
The flatness is stated with the `Flat` class of Mathlib 4.35, where the
FLT source used the older `RingHom.Flat` spelling. -/
theorem IsIntegrallyClosed.isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Flat R S]
    [IsLocalHom (algebraMap R S)] :
    IsDomain R ∧ IsIntegrallyClosed R := by
  have hff : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (algebraMap R S) :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hff).injective
  have : IsDomain R := hinj.isDomain _
  exact ⟨inferInstance, IsIntegrallyClosed.of_faithfullyFlat (B := S)⟩
