/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff.lean`
and
`P2M/Sol/S_CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

@[expose] public section

/-- A ring homomorphism induces a map between localizations away from
an element and its image, compatibly with the localization maps. -/
theorem exists_ringHom_away_comp_eq
    {B B' : Type*} [CommRing B] [CommRing B'] (f : B →+* B') (g : B) :
    ∃ fg : Localization.Away g →+* Localization.Away (f g),
      fg.comp (algebraMap B (Localization.Away g)) =
        (algebraMap B' (Localization.Away (f g))).comp f := by
  have hle : Submonoid.powers g ≤ (Submonoid.powers (f g)).comap f := by
    rintro x ⟨n, rfl⟩
    exact ⟨n, by simp [map_pow]⟩
  exact ⟨IsLocalization.map (Localization.Away (f g)) f hle,
    IsLocalization.map_comp hle⟩

/-- An element avoids a prime of the target exactly when it avoids the
comap prime of the source. -/
theorem primeSpectrum_not_mem_comap_asIdeal_iff
    {B B' : Type*} [CommRing B] [CommRing B'] (f : B →+* B') (g : B)
    (x' : PrimeSpectrum B') :
    f g ∉ x'.asIdeal ↔ g ∉ (PrimeSpectrum.comap f x').asIdeal := by
  simp [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
