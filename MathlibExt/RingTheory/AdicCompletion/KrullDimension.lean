/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le.lean`,
`P2M/Sol/S_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le.lean`,
`Theorems/Thm_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq.lean` and
`P2M/Sol/S_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq.lean`
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
public import MathlibExt.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Topology.KrullDimension

/-!
# Krull dimension of adic completions

A Noetherian local ring and its maximal-ideal adic completion have the same
Krull dimension. The completion's dimension is at most the ring's: take a
system of parameters of the ring, as many elements as its dimension spanning
an ideal primary to the maximal ideal. A power of the completion's maximal
ideal lies in the ideal spanned by their images, so that maximal ideal is a
minimal prime over it, and Krull's height theorem bounds its height, which is
the dimension of the completion, by the number of elements. The completion's
dimension is at least the ring's: faithful flatness gives a prime of the
completion over the top of a chain of primes of the ring, and going-down lifts
the chain to one of the same length in the completion. In particular, a
Noetherian local ring of Krull dimension at least two has an adic completion
of Krull dimension at least two.
-/

@[expose] public section

/-- The Krull dimension of a Noetherian local ring equals the Krull
dimension of its maximal-ideal adic completion. -/
theorem IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) = ringKrullDim R := by
  classical
  have : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  have : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine le_antisymm ?_ ?_
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      (R := AdicCompletion (IsLocalRing.maximalIdeal R) R),
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)]
    refine WithBot.coe_le_coe.2 ?_
    obtain ⟨s, hmin, hcard⟩ :=
      Ideal.exists_finset_card_eq_height_of_isNoetherianRing (IsLocalRing.maximalIdeal R)
    rw [← hcard]
    have hsle : Ideal.span (s : Set R) ≤ IsLocalRing.maximalIdeal R := hmin.1.2
    have hrad : IsLocalRing.maximalIdeal R ≤ (Ideal.span (s : Set R)).radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf ?_
      rintro P ⟨hsP, hP⟩
      exact hmin.2 ⟨hP, hsP⟩ (IsLocalRing.le_maximalIdeal hP.ne_top)
    obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg (Ideal.span (s : Set R))
      (IsNoetherian.noetherian _)
    have hN' : IsLocalRing.maximalIdeal R ^ (N + 1) ≤ Ideal.span (s : Set R) :=
      (Ideal.pow_le_pow_right (Nat.le_succ N)).trans ((Ideal.pow_right_mono hrad N).trans hN)
    let s' : Finset (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
      s.image (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    have hspan : Ideal.span (s' : Set (AdicCompletion (IsLocalRing.maximalIdeal R) R)) =
        (Ideal.span (s : Set R)).map
          (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) := by
      rw [Ideal.map_span, Finset.coe_image]
    have hpow : IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^
        (N + 1) ≤ Ideal.span (s' : Set (AdicCompletion (IsLocalRing.maximalIdeal R) R)) := by
      rw [hspan, AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
      exact Ideal.map_mono hN'
    have hmin' : IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ∈
        (Ideal.span (s' : Set (AdicCompletion (IsLocalRing.maximalIdeal R) R))).minimalPrimes := by
      refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal _).isPrime, ?_⟩, fun q hq _ => ?_⟩
      · rw [hspan, AdicCompletion.maximalIdeal_eq_map]
        exact Ideal.map_mono hsle
      · have := hq.1
        exact (Ideal.IsPrime.pow_le_iff (Nat.succ_ne_zero N)).1 (hpow.trans hq.2)
    exact (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin').trans
      (Nat.cast_le.2 Finset.card_image_le)
  · refine (iSup_le fun l => ?_ : Order.krullDim (PrimeSpectrum R) ≤ _)
    obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (A := R) (B := AdicCompletion (IsLocalRing.maximalIdeal R) R) l.last
    have : Q.asIdeal.LiesOver l.last.asIdeal := ⟨by rw [← hQ]; rfl⟩
    obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q.asIdeal
    rw [← hL]
    exact Order.LTSeries.length_le_krullDim L

/-- A Noetherian local ring of Krull dimension at least two has an adic
completion of Krull dimension at least two. -/
theorem IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (h : 2 ≤ ringKrullDim R) :
    2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  h.trans_eq (IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq R).symm
