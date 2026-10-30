/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two.lean` and
`P2M/Sol/S_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two.lean`
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

public import MathlibExt.RingTheory.RegularLocalRing.IsDomain
public import MathlibExt.RingTheory.RegularLocalRing.QuotientSpanSingleton
public import MathlibExt.RingTheory.LocalRing.UFDQuotient
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Regular local rings of Krull dimension at most two are UFDs

In embedding dimension zero or one the ring is a field or a discrete
valuation ring, hence a PID; in embedding dimension two, quotienting by a
parameter gives a PID, and the UFD property lifts along the quotient.
-/

@[expose] public section

open IsLocalRing

namespace RegularUFDaux

private theorem isPrincipalIdealRing_of_spanFinrank_eq_one (S : Type*)
    [CommRing S] [IsRegularLocalRing S]
    (h : Submodule.spanFinrank (maximalIdeal S) = 1) : IsPrincipalIdealRing S := by
  have : IsDomain S := IsRegularLocalRing.isDomain S
  have hcot : Module.finrank (ResidueField S) (CotangentSpace S) = 1 := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace S]
    exact h
  have : IsDiscreteValuationRing S :=
    IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hcot
  infer_instance

private theorem isPrincipalIdealRing_of_maximalIdeal_eq_bot (S : Type*) [CommRing S]
    [IsLocalRing S] (h : maximalIdeal S = ⊥) : IsPrincipalIdealRing S := by
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊤
  · exact ⟨⟨1, by simp [hI]⟩⟩
  · have hIbot : I = ⊥ := le_bot_iff.mp (h ▸ IsLocalRing.le_maximalIdeal hI)
    exact ⟨⟨0, by simp [hIbot]⟩⟩

end RegularUFDaux

/-- A regular local ring of Krull dimension at most two is a unique
factorization monoid. -/
theorem IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two
    (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R ≤ 2) : UniqueFactorizationMonoid R := by
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have hdR : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) =
      ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hd2 : Submodule.spanFinrank (maximalIdeal R) ≤ 2 := by
    have hthis : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) ≤ 2 :=
      hdR ▸ hdim
    exact_mod_cast hthis
  rcases Nat.lt_or_ge (Submodule.spanFinrank (maximalIdeal R)) 2 with hlt | hge
  · rcases Nat.lt_or_ge (Submodule.spanFinrank (maximalIdeal R)) 1 with h0 | h1
    · have h0' : Submodule.spanFinrank (maximalIdeal R) = 0 := by omega
      have hm : maximalIdeal R = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h0'
      have : IsPrincipalIdealRing R :=
        RegularUFDaux.isPrincipalIdealRing_of_maximalIdeal_eq_bot R hm
      infer_instance
    · have h1' : Submodule.spanFinrank (maximalIdeal R) = 1 := by omega
      have : IsPrincipalIdealRing R :=
        RegularUFDaux.isPrincipalIdealRing_of_spanFinrank_eq_one R h1'
      infer_instance
  · have h2 : Submodule.spanFinrank (maximalIdeal R) = 2 := le_antisymm hd2 hge
    have hpos : 0 < ringKrullDim R := by
      rw [← hdR, h2]
      exact_mod_cast Nat.zero_lt_two
    obtain ⟨x, hx, hx2, hxmin⟩ :=
      IsLocalRing.exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem R hpos
    have hxtop : Ideal.span {x} ≠ ⊤ := by
      intro htop
      have hle : Ideal.span {x} ≤ maximalIdeal R :=
        (Ideal.span_singleton_le_iff_mem _).mpr hx
      exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (htop ▸ hle))
    have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hxtop
    have : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    obtain ⟨hreg, hsf⟩ :=
      IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
        R hx hx2 hxmin
    have : IsRegularLocalRing (R ⧸ Ideal.span {x}) := hreg
    have h1 : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span {x})) = 1 := by omega
    have : IsPrincipalIdealRing (R ⧸ Ideal.span {x}) :=
      RegularUFDaux.isPrincipalIdealRing_of_spanFinrank_eq_one (R ⧸ Ideal.span {x}) h1
    have : IsDomain (R ⧸ Ideal.span {x}) := IsRegularLocalRing.isDomain _
    exact IsLocalRing.uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient x
