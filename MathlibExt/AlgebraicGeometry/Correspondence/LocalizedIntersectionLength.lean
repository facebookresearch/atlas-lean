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

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Quotient length at a minimal prime over an ideal

For a prime p minimal over I, the radical of the localized ideal in R_p is its maximal ideal.
Thus the local quotient has Krull dimension at most zero. If R is noetherian, that quotient is
Artinian and noetherian, hence has finite module length over R_p.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace AlgebraicGeometry.FiniteCorrespondenceIntersection

universe u

variable (R : Type u) [CommRing R]

/-- The localized quotient has zero-dimensional support.

For p minimal over I, the quotient R_p/I R_p has Krull dimension at most zero. -/
theorem localizedIntersectionQuotient_krullDimLE_zero
    (I p : Ideal R) [p.IsPrime] (hp : p ∈ I.minimalPrimes) :
    Ring.KrullDimLE 0
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) := by
  let L := Localization.AtPrime p
  let J := I.map (algebraMap R L)
  have hrad : J.radical = IsLocalRing.maximalIdeal L :=
    (IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes L p I hp).trans
      (IsLocalization.AtPrime.map_eq_maximalIdeal p L)
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro q hq
  have hle : IsLocalRing.maximalIdeal L ≤ q := by
    rw [← hrad]
    exact hq.isPrime.radical_le_iff.mpr hq.le
  have hmax : (IsLocalRing.maximalIdeal L).IsMaximal := inferInstance
  have heq : IsLocalRing.maximalIdeal L = q := hmax.eq_of_le hq.isPrime.ne_top hle
  rw [← heq]
  exact hmax

/-- Finite localized quotient length at a minimal prime.

For noetherian R and p minimal over I, the module R_p/I R_p has finite length. -/
theorem localizedIntersectionQuotient_length_ne_top
    [IsNoetherianRing R]
    (I p : Ideal R) [p.IsPrime] (hp : p ∈ I.minimalPrimes) :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≠ ⊤ := by
  let L := Localization.AtPrime p
  let J := I.map (algebraMap R L)
  let _ : Ring.KrullDimLE 0 (L ⧸ J) :=
    localizedIntersectionQuotient_krullDimLE_zero R I p hp
  let _ : IsArtinianRing (L ⧸ J) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  rw [Module.length_eq_of_surjective (R := L ⧸ J) (S := L)
    (M := L ⧸ J) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end AlgebraicGeometry.FiniteCorrespondenceIntersection
