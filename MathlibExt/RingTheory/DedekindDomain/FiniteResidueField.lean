/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers.lean`
and
`P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers.lean`
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

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Finiteness of the residue field of adic completion integers

At a place of a Dedekind domain with finite residue field, the residue
field of the adic completion integers is finite: the map from the base
ring to the residue field is surjective, and it factors through the finite
quotient by the place.
-/

@[expose] public section

universe u v

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

/-- The residue field of the adic completion integers at a place with finite
residue field is finite. -/
theorem finite_residueField_adicCompletionIntegers (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  classical
  have hv : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Integers
      (v.adicCompletionIntegers K) :=
    Valuation.valuationSubring.integers _
  have step1 : ∀ k : K, v.valuation K k ≤ 1 → ∃ r : R,
      v.valuation K (k - algebraMap R K r) < 1 := by
    intro k hk
    have hkmem : k ∈ (v.valuation K).valuationSubring := hk
    rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hkmem
    obtain ⟨a, s, hs, rfl⟩ :
        ∃ (a s : R) (_ : s ∈ v.asIdeal.primeCompl),
          k = algebraMap R K a * (algebraMap R K s)⁻¹ := hkmem
    have hs' : s ∉ v.asIdeal := hs
    haveI := v.isMaximal
    letI := Ideal.Quotient.field v.asIdeal
    obtain ⟨t, ht⟩ : ∃ t : R, s * t - 1 ∈ v.asIdeal := by
      have hs0 : (Ideal.Quotient.mk v.asIdeal s) ≠ 0 := by
        rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk v.asIdeal s)⁻¹)
      refine ⟨t, ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, ht, mul_inv_cancel₀ hs0,
        sub_self]
    refine ⟨a * t, ?_⟩
    have hvs : v.valuation K (algebraMap R K s) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 hs'
    have hs0K : algebraMap R K s ≠ 0 := by
      intro h; rw [h, map_zero] at hvs; exact zero_ne_one hvs
    have hrw : algebraMap R K a * (algebraMap R K s)⁻¹ - algebraMap R K (a * t) =
        algebraMap R K a * (algebraMap R K s)⁻¹ * (1 - algebraMap R K (s * t)) := by
      rw [map_mul, map_mul]; field_simp
    rw [hrw, map_mul, map_mul, map_inv₀, hvs, inv_one, mul_one]
    calc v.valuation K (algebraMap R K a) * v.valuation K (1 - algebraMap R K (s * t))
        ≤ 1 * v.valuation K (1 - algebraMap R K (s * t)) := by
          gcongr; exact v.valuation_le_one a
      _ < 1 := by
          have ht' : 1 - s * t ∈ v.asIdeal := by
            rw [← neg_sub]; exact v.asIdeal.neg_mem ht
          rw [one_mul, ← map_one (algebraMap R K), ← map_sub,
            IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
          exact ht'
  let ψ : R →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    (IsLocalRing.residue (v.adicCompletionIntegers K)).comp
      (algebraMap R (v.adicCompletionIntegers K))
  have hψ : Function.Surjective ψ := by
    intro xbar
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
    have hopen : IsOpen {y : v.adicCompletion K | Valued.v (y - x) < 1} := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      rw [Valued.mem_nhds]
      refine ⟨1, fun z hz => ?_⟩
      have hz' : Valued.v (z - y) < 1 := by
        have h := hz
        simp only [Set.mem_ofPred_eq, Units.val_one] at h
        exact (Valuation.restrict_lt_one_iff Valued.v).1 h
      change Valued.v (z - x) < 1
      calc Valued.v (z - x) = Valued.v (z - y + (y - x)) := by rw [sub_add_sub_cancel]
        _ ≤ max (Valued.v (z - y)) (Valued.v (y - x)) := Valuation.map_add _ _ _
        _ < 1 := max_lt hz' hy
    obtain ⟨k, hk⟩ :=
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v).exists_mem_open hopen
        ⟨x, by simp⟩
    have hk' : Valued.v (algebraMap K (v.adicCompletion K) k - (x : v.adicCompletion K)) < 1 := hk
    have hcoeK : ∀ k : K, Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
      fun k => IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    have hkv : Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k := hcoeK k
    have hk1 : v.valuation K k ≤ 1 := by
      rw [← hkv]
      calc Valued.v (algebraMap K (v.adicCompletion K) k)
          = Valued.v (algebraMap K (v.adicCompletion K) k - x + x) := by rw [sub_add_cancel]
        _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) k - x))
            (Valued.v (x : v.adicCompletion K)) := Valuation.map_add _ _ _
        _ ≤ 1 := max_le hk'.le x.2
    obtain ⟨r, hr⟩ := step1 k hk1
    refine ⟨r, ?_⟩
    change IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) =
      IsLocalRing.residue _ x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]
    apply ne_of_lt
    have hcoe : (((algebraMap R (v.adicCompletionIntegers K) r - x : v.adicCompletionIntegers K) :
        v.adicCompletion K)) =
        algebraMap K (v.adicCompletion K) (algebraMap R K r) - (x : v.adicCompletion K) := by
      rw [AddSubgroupClass.coe_sub,
        IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
      rfl
    change Valued.v (((algebraMap R (v.adicCompletionIntegers K) r - x :
        v.adicCompletionIntegers K) : v.adicCompletion K)) < 1
    rw [hcoe]
    have hrk : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) -
        algebraMap K (v.adicCompletion K) k) < 1 := by
      rw [← map_sub, hcoeK, ← neg_sub, Valuation.map_neg]
      exact hr
    calc Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) - (x : v.adicCompletion K))
        = Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) -
            algebraMap K (v.adicCompletion K) k +
            (algebraMap K (v.adicCompletion K) k - x)) := by rw [sub_add_sub_cancel]
      _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) -
            algebraMap K (v.adicCompletion K) k))
            (Valued.v (algebraMap K (v.adicCompletion K) k - x)) := Valuation.map_add _ _ _
      _ < 1 := max_lt hrk hk'
  haveI : Finite (R ⧸ v.asIdeal) := inferInstance
  have hker : ∀ r ∈ v.asIdeal, ψ r = 0 := by
    intro r hr
    change IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) = 0
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      hv.isUnit_iff_valuation_eq_one]
    apply ne_of_lt
    change Valued.v ((algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) :
        v.adicCompletion K) < 1
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    change Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) < 1
    have h1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) =
        v.valuation K (algebraMap R K r) :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [h1, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hr
  let ψbar : R ⧸ v.asIdeal →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    Ideal.Quotient.lift v.asIdeal ψ hker
  refine Finite.of_surjective ψbar fun y => ?_
  obtain ⟨r, rfl⟩ := hψ y
  exact ⟨Ideal.Quotient.mk _ r, rfl⟩

end IsDedekindDomain.HeightOneSpectrum
