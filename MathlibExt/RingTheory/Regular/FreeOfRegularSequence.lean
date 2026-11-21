/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_free_of_isRegular_of_span_eq_maximalIdeal.lean`
and
`P2M/Sol/S_Module_free_of_isRegular_of_span_eq_maximalIdeal.lean`
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

public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

@[expose] public section

open RingTheory.Sequence

namespace Module

private theorem map_mk_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A] (I : Ideal A)
    (hI : I ≠ ⊤) [IsLocalRing (A ⧸ I)] :
    (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk I) =
      IsLocalRing.maximalIdeal (A ⧸ I) := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj
      (IsLocalRing.maximalIdeal.isMaximal A) with h | h
  · exfalso
    have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk I)) h
    rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_top, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr (IsLocalRing.le_maximalIdeal hI)] at h2
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top h2
  · exact IsLocalRing.eq_maximalIdeal h

private theorem free_of_isWeaklyRegular_aux (n : ℕ) :
    ∀ (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (rs : List A),
      rs.length = n → Ideal.ofList rs = IsLocalRing.maximalIdeal A →
      ∀ (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M],
        RingTheory.Sequence.IsWeaklyRegular M rs → Module.Free A M := by
  induction n with
  | zero =>
    intro A _ _ _ rs hlen hspan M _ _ _ _
    obtain rfl : rs = [] := List.eq_nil_of_length_eq_zero hlen
    rw [Ideal.ofList_nil] at hspan
    have hF : IsField A := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hspan.symm
    letI := hF.toField
    infer_instance
  | succ n ih =>
    intro A _ _ _ rs hlen hspan M _ _ _ hM
    cases rs with
    | nil => simp at hlen
    | cons r rs' =>
      rw [RingTheory.Sequence.isWeaklyRegular_cons_iff'] at hM
      obtain ⟨hr, hM'⟩ := hM
      have hr𝔪 : r ∈ IsLocalRing.maximalIdeal A := hspan ▸ Ideal.subset_span (by simp)
      have hne : Ideal.span {r} ≠ ⊤ :=
        fun h => (IsLocalRing.mem_maximalIdeal r).mp hr𝔪 (Ideal.span_singleton_eq_top.mp h)
      haveI : Nontrivial (A ⧸ Ideal.span {r}) := Ideal.Quotient.nontrivial_iff.mpr hne
      haveI : IsLocalRing (A ⧸ Ideal.span {r}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      have hspan' : Ideal.ofList (rs'.map (Ideal.Quotient.mk (Ideal.span {r}))) =
          IsLocalRing.maximalIdeal (A ⧸ Ideal.span {r}) := by
        rw [← Ideal.map_ofList, ← map_mk_maximalIdeal _ hne, ← hspan, Ideal.ofList_cons,
          Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]
      haveI : Module.Finite (A ⧸ Ideal.span {r}) (QuotSMulTop r M) :=
        Module.Finite.of_restrictScalars_finite A _ _
      haveI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
      have hfree := ih (A ⧸ Ideal.span {r}) _ (by simpa using hlen) hspan'
        (QuotSMulTop r M) hM'
      have hbot : (⊥ : Ideal A) ≠ ⊤ := by
        intro h
        have h1 : (1 : A) ∈ (⊥ : Ideal A) := h ▸ Submodule.mem_top
        rw [Ideal.mem_bot] at h1
        exact one_ne_zero h1
      have hmem : r ∈ (⊥ : Ideal A).jacobson :=
        (IsLocalRing.jacobson_eq_maximalIdeal ⊥ hbot) ▸ hr𝔪
      exact (Module.free_quotSMulTop_iff_free A M hmem hr).mp hfree

/-- Over a Noetherian local ring `A`, a finite module admitting a regular
sequence (also regular on `A` itself) that generates the maximal ideal is
free. This is the Auslander--Buchsbaum special case: maximal depth implies
freeness. -/
public theorem free_of_isRegular_of_span_eq_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (rs : List A) (hA : RingTheory.Sequence.IsRegular A rs)
    (hspan : Ideal.ofList rs = IsLocalRing.maximalIdeal A)
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : RingTheory.Sequence.IsRegular M rs) :
    Module.Free A M :=
  free_of_isWeaklyRegular_aux rs.length A rs rfl hspan M hM.toIsWeaklyRegular

end Module
