/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Field_nonempty_ringHom_complex_of_countable.lean`
and
`P2M/Sol/S_Field_nonempty_ringHom_complex_of_countable.lean`
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
framework; the statement and proof are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.SetTheory.Cardinal.Continuum

@[expose] public section

universe u

open Cardinal

namespace Field

/-- Every countable field of characteristic zero embeds in `ℂ`: embed a
transcendence basis over `ℚ` into one of `ℂ` (possible by cardinality),
then extend through the algebraic part by algebraic closedness. -/
public theorem nonempty_ringHom_complex_of_countable (K : Type u)
    [Field K] [CharZero K] [Countable K] : Nonempty (K →+* ℂ) := by
  classical
  haveI : FaithfulSMul ℚ K :=
    (faithfulSMul_iff_algebraMap_injective ℚ K).2 (algebraMap ℚ K).injective
  haveI : FaithfulSMul ℚ ℂ :=
    (faithfulSMul_iff_algebraMap_injective ℚ ℂ).2 (algebraMap ℚ ℂ).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hct : #ℂ = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
      (R := ℚ) _ ht mk_le_aleph0
      (by rw [mk_complex]; exact aleph0_lt_continuum)
  have h1 : Cardinal.lift.{0} #s ≤ Cardinal.lift.{u} #t := by
    rw [← hct, mk_complex, lift_continuum]
    calc Cardinal.lift.{0} #s ≤ Cardinal.lift.{0} ℵ₀ := lift_le.2 mk_le_aleph0
      _ = ℵ₀ := lift_aleph0
      _ ≤ 𝔠 := aleph0_le_continuum
  obtain ⟨e⟩ := Cardinal.lift_mk_le'.1 h1
  have hind : AlgebraicIndependent ℚ (fun i : s => ((e i : t) : ℂ)) :=
    ht.1.comp e e.injective
  set A := Algebra.adjoin ℚ (Set.range ((↑) : s → K)) with hA
  let g : A →ₐ[ℚ] ℂ :=
    (MvPolynomial.aeval (fun i : s => ((e i : t) : ℂ))).comp
      hs.1.aevalEquiv.symm.toAlgHom
  have hg : Function.Injective g :=
    (algebraicIndependent_iff_injective_aeval.1 hind).comp
      hs.1.aevalEquiv.symm.injective
  haveI : Algebra.IsAlgebraic A K := hs.isAlgebraic
  letI : Algebra A ℂ := g.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree A ℂ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hg
  haveI : Module.IsTorsionFree A K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
  exact ⟨(IsAlgClosed.lift (R := A) (S := K) (M := ℂ)).toRingHom⟩

end Field
