/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le.lean` and
`P2M/Sol/S_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le.lean`
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

public import MathlibExt.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.Topology.KrullDimension

/-!
# Krull dimension of adic completions

A Noetherian local ring of Krull dimension at least two has an adic
completion of Krull dimension at least two, by faithful flatness and
going-down.
-/

@[expose] public section

/-- A Noetherian local ring of Krull dimension at least two has an adic
completion of Krull dimension at least two. -/
theorem IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (h : 2 ≤ ringKrullDim R) :
    2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  have : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal R
  have h2 : (2 : ℕ) ≤ Order.krullDim (PrimeSpectrum R) := by
    change ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R
    exact h
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp h2
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := AdicCompletion (IsLocalRing.maximalIdeal R) R) l.last
  have : Q.asIdeal.LiesOver l.last.asIdeal := ⟨by rw [← hQ]; rfl⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q.asIdeal
  have hthis := Order.le_krullDim_iff.mpr ⟨L, hL.trans hl⟩
  exact hthis
