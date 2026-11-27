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
import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

open RingTheory.Sequence

namespace Module

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
    let := hF.toField
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
        Ideal.span_singleton_ne_top ((IsLocalRing.mem_maximalIdeal r).mp hr𝔪)
      have : Nontrivial (A ⧸ Ideal.span {r}) := Ideal.Quotient.nontrivial_iff.mpr hne
      have : IsLocalRing (A ⧸ Ideal.span {r}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      have hspan' : Ideal.ofList (rs'.map (Ideal.Quotient.mk (Ideal.span {r}))) =
          IsLocalRing.maximalIdeal (A ⧸ Ideal.span {r}) := by
        rw [← Ideal.map_ofList, ← IsLocalRing.map_maximalIdeal_of_surjective
          (Ideal.Quotient.mk (Ideal.span {r})) Ideal.Quotient.mk_surjective, ← hspan,
          Ideal.ofList_cons, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]
      have : Module.Finite (A ⧸ Ideal.span {r}) (QuotSMulTop r M) :=
        Module.Finite.of_restrictScalars_finite A _ _
      have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
      have hfree := ih (A ⧸ Ideal.span {r}) _ (by simpa using hlen) hspan'
        (QuotSMulTop r M) hM'
      have hmem : r ∈ Ring.jacobson A := (IsLocalRing.ringJacobson_eq_maximalIdeal A).ge hr𝔪
      exact (Module.free_quotSMulTop_iff_free A M hmem hr).mp hfree

/-- **Freeness from a weakly regular sequence generating the maximal ideal.** Let `A` be a
Noetherian local ring with maximal ideal `𝔪` and `M` a finite `A`-module. If a sequence `rs`
generates `𝔪` and is weakly regular on `M`, then `M` is free. Weak regularity asks only that each
element of `rs` be a nonzerodivisor on `M` modulo the earlier elements; unlike regularity, it does
not ask that `M ≠ 𝔪 • M`, so `M` may be zero. Nothing is asked of `rs` on `A`. This is a stronger
form of `Module.free_of_isRegular_of_span_eq_maximalIdeal`. -/
public theorem free_of_isWeaklyRegular_of_span_eq_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (rs : List A) (hspan : Ideal.ofList rs = IsLocalRing.maximalIdeal A)
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : RingTheory.Sequence.IsWeaklyRegular M rs) :
    Module.Free A M :=
  free_of_isWeaklyRegular_aux rs.length A rs rfl hspan M hM

/-- **Freeness from a regular sequence generating the maximal ideal.** Let `A` be a Noetherian
local ring with maximal ideal `𝔪` and `M` a finite `A`-module. If a sequence `rs` generates `𝔪`
and is regular both on `A` and on `M`, then `M` is free. Under these hypotheses `A` is a regular
local ring whose dimension is the length of `rs`, as `𝔪` is generated by the `A`-regular sequence
`rs`, and `rs` shows that `M` has depth equal to that dimension. The theorem is thus the familiar
fact that a finite module of maximal depth over a regular local ring is free, a consequence of the
Auslander–Buchsbaum formula. It is the special case of
`Module.free_of_isWeaklyRegular_of_span_eq_maximalIdeal` in which `rs` is also regular on `A` and
`M ≠ 𝔪 • M`. -/
public theorem free_of_isRegular_of_span_eq_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (rs : List A) (_hA : RingTheory.Sequence.IsRegular A rs)
    (hspan : Ideal.ofList rs = IsLocalRing.maximalIdeal A)
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : RingTheory.Sequence.IsRegular M rs) :
    Module.Free A M :=
  free_of_isWeaklyRegular_of_span_eq_maximalIdeal rs hspan M hM.toIsWeaklyRegular

end Module
