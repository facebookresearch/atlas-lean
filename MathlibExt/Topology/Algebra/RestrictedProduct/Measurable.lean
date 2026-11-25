/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_RestrictedProduct_measurable_iff_forall_measurable_apply.lean`
and
`P2M/Sol/S_RestrictedProduct_measurable_iff_forall_measurable_apply.lean`
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

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

@[expose] public section

open Filter Topology
open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} {A : (i : ι) → Set (R i)}
  [∀ i, TopologicalSpace (R i)]

/-- The piece of the restricted product supported in a finite set `T`:
the elements whose coordinates outside `T` lie in the restricted sets. -/
private def piece (T : Finset ι) : Set (Πʳ i, [R i, A i]) :=
  {y | ∀ i, i ∉ T → y i ∈ A i}

private theorem le_principal_compl (T : Finset ι) :
    (cofinite : Filter ι) ≤ 𝓟 ((↑T : Set ι)ᶜ) :=
  le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite

private theorem piece_eq_range (T : Finset ι) :
    piece (R := R) (A := A) T =
      Set.range (inclusion R A (le_principal_compl T)) := by
  rw [range_inclusion]
  ext y
  simp only [piece, Set.mem_setOf_eq, eventually_principal, Set.mem_compl_iff,
    Finset.mem_coe]

private theorem iUnion_piece :
    (⋃ T : Finset ι, piece (R := R) (A := A) T) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  have hy : ({i | y i ∈ A i}ᶜ).Finite := by
    have h := y.eventually
    rwa [eventually_cofinite] at h
  refine Set.mem_iUnion.mpr ⟨hy.toFinset, fun i hi => ?_⟩
  by_contra h
  exact hi (hy.mem_toFinset.mpr h)

private theorem exists_isOpen_inter_piece_eq {W : Set (Πʳ i, [R i, A i])}
    (hW : IsOpen W) (T : Finset ι) :
    ∃ V : Set (Π i, R i), IsOpen V ∧
      W ∩ piece T = {y | y ∈ piece T ∧ (⇑y : Π i, R i) ∈ V} := by
  have hS := le_principal_compl (ι := ι) T
  have hV : IsOpen (inclusion R A hS ⁻¹' W) :=
    hW.preimage (continuous_inclusion hS)
  obtain ⟨V, hVo, hVeq⟩ :=
    (isEmbedding_coe_of_principal (R := R) (A := A)
      (S := ((↑T : Set ι)ᶜ))).isInducing.isOpen_iff.mp hV
  refine ⟨V, hVo, ?_⟩
  ext y
  constructor
  · rintro ⟨hyW, hyP⟩
    refine ⟨hyP, ?_⟩
    have hy' : y ∈ Set.range (inclusion R A hS) := by
      rw [← piece_eq_range]; exact hyP
    obtain ⟨z, rfl⟩ := hy'
    have hz : z ∈ inclusion R A hS ⁻¹' W := hyW
    rw [← hVeq] at hz
    exact hz
  · rintro ⟨hyP, hyV⟩
    refine ⟨?_, hyP⟩
    have hy' : y ∈ Set.range (inclusion R A hS) := by
      rw [← piece_eq_range]; exact hyP
    obtain ⟨z, rfl⟩ := hy'
    have hz : z ∈ ((↑) : Πʳ i, [R i, A i]_[𝓟 ((↑T : Set ι)ᶜ)] →
        Π i, R i) ⁻¹' V := hyV
    rw [hVeq] at hz
    exact hz

variable [Countable ι] [∀ i, SecondCountableTopology (R i)]
  [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
  [MeasurableSpace (Πʳ i, [R i, A i])] [BorelSpace (Πʳ i, [R i, A i])]

private theorem measurable_of_forall_measurable_apply (hA : ∀ i, MeasurableSet (A i))
    {X : Type*} [MeasurableSpace X] {f : X → Πʳ i, [R i, A i]}
    (hf : ∀ i, Measurable fun x => f x i) : Measurable f := by
  have hcoe : Measurable fun x => ((⇑(f x)) : Π i, R i) :=
    measurable_pi_iff.mpr hf
  refine measurable_of_isOpen fun W hW => ?_
  have hWeq : W = ⋃ T : Finset ι, W ∩ piece T := by
    rw [← Set.inter_iUnion, iUnion_piece, Set.inter_univ]
  rw [hWeq, Set.preimage_iUnion]
  refine MeasurableSet.iUnion fun T => ?_
  obtain ⟨V, hVo, hVeq⟩ := exists_isOpen_inter_piece_eq hW T
  rw [hVeq]
  have h1 : MeasurableSet {x : X | f x ∈ piece (R := R) (A := A) T} := by
    have heq : {x : X | f x ∈ piece (R := R) (A := A) T} =
        ⋂ i, {x | i ∉ T → f x i ∈ A i} := by
      ext x; simp [piece]
    rw [heq]
    refine MeasurableSet.iInter fun i => ?_
    by_cases hi : i ∈ T
    · have huniv : {x : X | i ∉ T → f x i ∈ A i} = Set.univ := by
        ext x; simp [hi]
      rw [huniv]; exact MeasurableSet.univ
    · have hpre : {x : X | i ∉ T → f x i ∈ A i} = (fun x => f x i) ⁻¹' A i := by
        ext x; simp [hi]
      rw [hpre]; exact hf i (hA i)
  have h2 : MeasurableSet ((fun x => ((⇑(f x)) : Π i, R i)) ⁻¹' V) :=
    hcoe hVo.measurableSet
  exact h1.inter h2

/-- A map into a restricted product over a countable index set, with
second-countable Borel factors and measurable restricted sets, is measurable
if and only if every coordinate map is measurable. The restricted product
carries an assumed Borel σ-algebra. -/
public theorem measurable_iff_forall_measurable_apply
    (hA : ∀ i, MeasurableSet (A i))
    {X : Type*} [MeasurableSpace X] (f : X → Πʳ i, [R i, A i]) :
    Measurable f ↔ ∀ i, Measurable fun x => f x i :=
  ⟨fun hf i => (continuous_eval i).measurable.comp hf,
    fun hf => measurable_of_forall_measurable_apply hA hf⟩

end RestrictedProduct
