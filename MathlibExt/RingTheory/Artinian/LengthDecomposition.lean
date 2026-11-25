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

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Scalar length in the actual Artinian localization decomposition

The canonical prime-localization product equivalence of an Artinian
algebra decomposes its length over any commutative base ring. The factors
retain their actual nilpotents and scalar action. This is the common
length calculation for finite-field fiber degrees and for local divisor
multiplicities over a non-field base ring.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

universe u v

namespace IsArtinianRing

/-- The actual prime-localization product decomposes scalar length over every commutative base ring. -/
theorem length_eq_sum_primeSpectrum
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [IsArtinianRing A] :
    letI : Fintype (PrimeSpectrum A) := Fintype.ofFinite (PrimeSpectrum A)
    Module.length R A = ∑ m : PrimeSpectrum A,
      Module.length R (Localization.AtPrime m.asIdeal) := by
  classical
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite (PrimeSpectrum A)
  have h := ((PrimeSpectrum.toPiLocalizationEquiv A).restrictScalars R).toLinearEquiv.length_eq
  rw [Module.length_pi_of_fintype] at h
  exact h

end IsArtinianRing
