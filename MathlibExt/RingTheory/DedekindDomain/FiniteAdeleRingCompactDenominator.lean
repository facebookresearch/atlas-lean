/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_`
`mul_apply_mem_adicCompletionIntegers_of_isCompact.lean`
and
`P2M/Sol/S_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_`
`mul_apply_mem_adicCompletionIntegers_of_isCompact.lean`
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

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

@[expose] public section

open IsDedekindDomain

namespace IsDedekindDomain.FiniteAdeleRing

private theorem algebraMap_mul_apply {R K : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (r : R) (y : FiniteAdeleRing R K)
    (v : HeightOneSpectrum R) :
    (algebraMap R (FiniteAdeleRing R K) r * y) v =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) * y v := rfl

/-- A single nonzero denominator clears every finite adèle in a compact set:
for a compact set of finite adèles there is a nonzero `s` in the Dedekind
domain such that multiplying by `s` lands in the ring of integers at every
place, simultaneously for every point of the compact set. -/
public theorem exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {C : Set (FiniteAdeleRing R K)} (hC : IsCompact C) :
    ∃ s : R, s ≠ 0 ∧ ∀ y ∈ C, ∀ v : HeightOneSpectrum R,
      (algebraMap R (FiniteAdeleRing R K) s * y) v
        ∈ HeightOneSpectrum.adicCompletionIntegers K v := by
  classical
  let U : R → Set (FiniteAdeleRing R K) := fun s =>
    {y | ∀ v : HeightOneSpectrum R,
      (algebraMap R (FiniteAdeleRing R K) s * y) v ∈ HeightOneSpectrum.adicCompletionIntegers K v}
  have hopen : ∀ s ∈ {s : R | s ≠ 0}, IsOpen (U s) := by
    intro s _
    have hU : U s = (fun y => algebraMap R (FiniteAdeleRing R K) s * y) ⁻¹'
        {y : FiniteAdeleRing R K | ∀ v : HeightOneSpectrum R,
          y v ∈ HeightOneSpectrum.adicCompletionIntegers K v} := by
      ext y
      simp only [U, Set.mem_preimage, Set.mem_setOf_eq]
    rw [hU]
    apply IsOpen.preimage (continuous_const_mul _)
    exact RestrictedProduct.isOpen_forall_mem
      (fun v => Valued.isOpen_valuationSubring _)
  have hcover : C ⊆ ⋃ s ∈ {s : R | s ≠ 0}, U s := by
    intro y _
    have hS : {v : HeightOneSpectrum R | y v ∉ HeightOneSpectrum.adicCompletionIntegers K v}.Finite :=
      Filter.eventually_cofinite.mp y.cofinite_mem_adicCompletionIntegers
    choose b hb hmem using fun v => HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers
      (K := K) v (y v)
    refine Set.mem_iUnion₂.mpr ⟨∏ w ∈ hS.toFinset, b w,
      Finset.prod_ne_zero_iff.mpr fun w _ => nonZeroDivisors.ne_zero (hb w), ?_⟩
    intro v
    by_cases hv : v ∈ hS.toFinset
    · rw [algebraMap_mul_apply, ← Finset.prod_erase_mul _ _ hv, map_mul, map_mul, mul_assoc]
      refine mul_mem (HeightOneSpectrum.coe_algebraMap_mem (R := R) (K := K) (v := v) _) ?_
      rw [mul_comm]
      exact hmem v
    · have hyv : y v ∈ HeightOneSpectrum.adicCompletionIntegers K v := by
        simpa [Set.Finite.mem_toFinset] using hv
      rw [algebraMap_mul_apply]
      exact mul_mem (HeightOneSpectrum.coe_algebraMap_mem (R := R) (K := K) (v := v) _) hyv
  obtain ⟨T, hTsub, hTfin, hCT⟩ := hC.elim_finite_subcover_image hopen hcover
  refine ⟨∏ s ∈ hTfin.toFinset, s,
    Finset.prod_ne_zero_iff.mpr fun s hs => hTsub (hTfin.mem_toFinset.mp hs), fun y hy v => ?_⟩
  obtain ⟨s, hsT, hys⟩ := Set.mem_iUnion₂.mp (hCT hy)
  rw [← Finset.prod_erase_mul _ _ (hTfin.mem_toFinset.mpr hsT), map_mul, mul_assoc,
    algebraMap_mul_apply]
  exact mul_mem (HeightOneSpectrum.coe_algebraMap_mem (R := R) (K := K) (v := v) _) (hys v)

end IsDedekindDomain.FiniteAdeleRing
