/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed.lean` and
`P2M/Sol/S_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed.lean`
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

import MathlibExt.Algebra.Etale.AlgHomCount
import Mathlib.FieldTheory.Perfect

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Algebra homomorphisms into an algebraically closed field

A finite reduced algebra over an algebraically closed field has as many
algebra homomorphisms to the field as its dimension: the algebra is the
product of its residue fields at maximal ideals, each a copy of the field,
and homomorphisms correspond bijectively to maximal ideals.
-/

@[expose] public section

/-- A finite reduced algebra over an algebraically closed field has
`finrank` many algebra homomorphisms to the field. -/
theorem AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed
    (K B : Type*) [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B]
    [Module.Finite K B] [IsReduced B] :
    Nat.card (B →ₐ[K] K) = Module.finrank K B := by
  classical
  let : IsArtinianRing B := IsArtinianRing.of_finite K B
  let (I : MaximalSpectrum B) : Field (B ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  let (I : MaximalSpectrum B) : Module.Finite K (B ⧸ I.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K I.asIdeal)
  let (I : MaximalSpectrum B) : Algebra.IsAlgebraic K (B ⧸ I.asIdeal) :=
    Algebra.IsAlgebraic.of_finite K _
  let : Algebra.Etale K B := (Algebra.Etale.iff_exists_algEquiv_prod K B).mpr
    ⟨MaximalSpectrum B, inferInstance, (fun I => B ⧸ I.asIdeal), inferInstance,
      inferInstance, (IsArtinianRing.equivPi B).restrictScalars K,
      fun _ => ⟨inferInstance, Algebra.IsAlgebraic.isSeparable_of_perfectField⟩⟩
  exact Algebra.Etale.natCard_algHom_eq_finrank_of_isAlgClosed K B
