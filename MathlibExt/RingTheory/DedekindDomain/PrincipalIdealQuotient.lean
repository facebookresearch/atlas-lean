/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

/-- Every quotient of a Dedekind domain by a nonzero ideal is a principal ideal ring. -/
theorem IsDedekindDomain.isPrincipalIdealRing_quotient {A : Type*} [CommRing A]
    [IsDedekindDomain A] (I : Ideal A) (hI : I ≠ ⊥) : IsPrincipalIdealRing (A ⧸ I) where
  principal J := by
    obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have ha0' : (Ideal.Quotient.mk I) a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr haI
    have haJ : a ∈ J.comap (Ideal.Quotient.mk I) := by
      change (Ideal.Quotient.mk I) a ∈ J
      rw [ha0']
      exact J.zero_mem
    obtain ⟨b, hb⟩ := IsDedekindDomain.exists_eq_span_pair haJ ha0
    have hmap : Ideal.map (Ideal.Quotient.mk I) (J.comap (Ideal.Quotient.mk I)) = J :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective J
    rw [hb, Ideal.map_span] at hmap
    rw [Set.image_pair, ha0', Ideal.span_insert,
      Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq] at hmap
    exact ⟨_, hmap.symm⟩
