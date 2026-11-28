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
# Scalar length in the prime-localization decomposition

Let A be a commutative Artinian algebra over any commutative ring R. Its prime spectrum is
finite, and the canonical algebra equivalence A ≅ ∏_{p∈Spec A} A_p decomposes A into its prime
localizations, with the original R-action on every factor.

Module length is additive on this finite product, so ℓ_R(A) = Σ_p ℓ_R(A_p) in ℕ∞. The equality
allows infinite scalar length and retains the nilpotent structure of each factor. The base and
algebra universes are independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

universe u v

namespace IsArtinianRing

/-- Prime-localization sum for scalar length of an Artinian algebra.

For a commutative Artinian R-algebra A, with R any commutative ring, ℓ_R(A) = Σ_{p∈Spec A}
ℓ_R(A_p). The finite sum is taken over the prime spectrum, and the equality is in ℕ∞. It
follows from the canonical prime-localization product equivalence, restricted to the R-module
structure. -/
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
