/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.GlobalSemistableSkeleton

/-!
# Tests for strata whose generic point lies in the stratum

A stratum of a semistable special fibre is an irreducible component of a locally closed locus,
and is generally not closed: the closure of a point is closed, so a generic point taken in the
ambient space would force the stratum to be closed. The stratum records therefore take the
generic point in the locus, with the subspace topology. On the affine line `Spec ℚ[T]`, the open
stratum `T ≠ 0` is not closed, yet the zero ideal is a generic point of it in the subspace
topology.
-/

open Polynomial PrimeSpectrum

noncomputable section

namespace MathlibExtTest.SemistableStrata

/-- The affine line over `ℚ`. -/
private abbrev Line := PrimeSpectrum ℚ[X]

/-- The open stratum `T ≠ 0` of the line. -/
private abbrev openStratum : Set Line := (basicOpen (X : ℚ[X]) : Set Line)

/-- The generic point of the line, the zero ideal. -/
private def zeroPoint : Line := ⟨⊥, Ideal.isPrime_bot⟩

/-- The origin `T = 0` of the line. -/
private def origin : Line :=
  ⟨Ideal.span {X}, (Ideal.span_singleton_prime X_ne_zero).mpr prime_X⟩

private theorem zeroPoint_mem : zeroPoint ∈ openStratum := by
  change zeroPoint ∈ basicOpen (X : ℚ[X])
  rw [mem_basicOpen]
  change X ∉ (⊥ : Ideal ℚ[X])
  simp [X_ne_zero]

private theorem origin_not_mem : origin ∉ openStratum := by
  change origin ∉ basicOpen (X : ℚ[X])
  rw [mem_basicOpen, not_not]
  exact Ideal.subset_span (Set.mem_singleton X)

/-- A generic point in the ambient space forces closedness: the closure of a point is closed. -/
example {T : Type*} [TopologicalSpace T] {x : T} {S : Set T} (h : IsGenericPoint x S) :
    IsClosed S :=
  h.isClosed

/-- The open stratum is not closed in the line, so it has no generic point in the line. -/
example : ¬ IsClosed openStratum := by
  intro h
  have hsub : closure {zeroPoint} ⊆ openStratum :=
    h.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr zeroPoint_mem)
  have huniv : closure ({zeroPoint} : Set Line) = Set.univ := by
    rw [PrimeSpectrum.closure_singleton]
    exact zeroLocus_bot
  exact origin_not_mem (hsub (huniv ▸ Set.mem_univ origin))

/-- In the subspace topology of the open stratum, the zero ideal is a generic point of the
whole stratum. -/
example : IsGenericPoint (⟨zeroPoint, zeroPoint_mem⟩ : openStratum) Set.univ := by
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.mem_univ, iff_true]
  rw [← Topology.IsInducing.subtypeVal.specializes_iff, ← le_iff_specializes]
  change (⊥ : Ideal ℚ[X]) ≤ (y : Line).asIdeal
  exact bot_le

end MathlibExtTest.SemistableStrata
