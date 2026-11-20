/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Localization.AwayPrimeAvoidance

@[expose] public section

universe u

/-- Source consumer, generalized to a higher universe. -/
example {B B' : Type u} [CommRing B] [CommRing B'] (f : B →+* B') (g : B) :
    (∃ fg : Localization.Away g →+* Localization.Away (f g),
        fg.comp (algebraMap B (Localization.Away g)) =
          (algebraMap B' (Localization.Away (f g))).comp f) ∧
      ∀ x' : PrimeSpectrum B', f g ∉ x'.asIdeal ↔
        g ∉ (PrimeSpectrum.comap f x').asIdeal :=
  exists_ringHom_away_comp_eq_and_not_mem_iff f g

/-- Boundary: the induced map for the identity and `g = 1` is explicit. -/
example : ∃ fg : Localization.Away (1 : ℤ) →+* Localization.Away (1 : ℤ),
    fg.comp (algebraMap ℤ (Localization.Away (1 : ℤ))) =
      (algebraMap ℤ (Localization.Away (1 : ℤ))).comp (RingHom.id ℤ) :=
  (exists_ringHom_away_comp_eq_and_not_mem_iff (RingHom.id ℤ) 1).1
