/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_quotient_of_ne_top.lean` and
`P2M/Sol/S_IsLocalRing_quotient_of_ne_top.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Quotients of local rings

A quotient of a local ring by a proper ideal is local: the quotient map is
surjective, and locality descends along surjective ring homomorphisms.
-/

@[expose] public section

/-- A quotient of a local ring by a proper ideal is local. Mathlib uses this
fact inline (via `IsLocalRing.of_surjective'`), but does not package it as a
standalone lemma. -/
theorem IsLocalRing.quotient_of_ne_top {A : Type*} [CommRing A] [IsLocalRing A]
    (I : Ideal A) (hI : I ≠ ⊤) : IsLocalRing (A ⧸ I) :=
  haveI := Ideal.Quotient.nontrivial_iff.mpr hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
