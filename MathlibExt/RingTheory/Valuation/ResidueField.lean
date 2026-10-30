/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_exists_root_mem_of_monic.lean`,
`P2M/Sol/S_ValuationSubring_exists_root_mem_of_monic.lean`,
`Theorems/Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed.lean` and
`P2M/Sol/S_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Roots in valuation subrings and algebraically closed residue fields

A monic polynomial over a valuation subring of an algebraically closed field
with a root in the field has a root in the subring, and the residue field of
such a valuation subring is algebraically closed.
-/

@[expose] public section

/-- A monic polynomial over a valuation subring of an algebraically closed
field, of nonzero degree, has a root in the subring: take a root in the field,
it is integral over the subring, and valuation subrings are integrally closed. -/
theorem ValuationSubring.exists_root_mem_of_monic {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) (f : Polynomial A) (hf : f.Monic) (hd : f.natDegree ≠ 0) :
    ∃ x : A, Polynomial.aeval (x : K) f = 0 := by
  have hdeg : (f.map (algebraMap A K)).degree ≠ 0 := by
    rw [hf.degree_map]
    intro h
    exact hd (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr h.le)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap A K)) hdeg
  have hint : IsIntegral A x := by
    refine ⟨f, hf, ?_⟩
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  have hyx : (y : K) = x := hy
  rw [Polynomial.aeval_def, hyx]
  rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx

/-- The residue field of a valuation subring of an algebraically closed field
is algebraically closed: lift a monic irreducible polynomial to the valuation
subring, take a root there, and reduce it back. -/
theorem ValuationSubring.isAlgClosed_residueField {L : Type*} [Field L] [IsAlgClosed L]
    (A : ValuationSubring L) : IsAlgClosed (IsLocalRing.ResidueField ↥A) := by
  have : IsIntegrallyClosed ↥A := inferInstance
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue ↥A) := IsLocalRing.residue_surjective
  obtain ⟨q, hq, hdeg, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts p).mpr fun n => hsurj (p.coeff n)) hp
  have hdegL : (q.map (algebraMap (↥A) L)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (IsFractionRing.injective (↥A) L), hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdegL
  have hint : IsIntegral (↥A) x := ⟨q, hmon, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (K := L)).mp hint
  refine ⟨IsLocalRing.residue ↥A a, ?_⟩
  have hqa : q.eval a = 0 := by
    apply IsFractionRing.injective ↥A L
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ha]
    exact hx
  change p.IsRoot (IsLocalRing.residue ↥A a)
  rw [← hq, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply, hqa, map_zero]
