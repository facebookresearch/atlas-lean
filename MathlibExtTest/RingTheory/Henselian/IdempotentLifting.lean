/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.RingTheory.Henselian.IdempotentLifting

import Mathlib.RingTheory.Finiteness.Prod

universe u v

-- Exact-source consumer, with the original binders and universes.
example {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    (ē : S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) (hē : IsIdempotentElem ē) :
    ∃! e : S, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) e = ē :=
  HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite ē hē

-- Existence: a nontrivial idempotent of the closed fibre lifts to a nontrivial
-- idempotent of `S`.
example {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    (ē : S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) (hē : IsIdempotentElem ē)
    (h0 : ē ≠ 0) (h1 : ē ≠ 1) :
    ∃ e : S, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  obtain ⟨e, ⟨he, hmk⟩, -⟩ :=
    HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite ē hē
  refine ⟨e, he, ?_, ?_⟩
  · rintro rfl
    exact h0 (by rw [← hmk, map_zero])
  · rintro rfl
    exact h1 (by rw [← hmk, map_one])

-- Uniqueness on a finite algebra that is not local: in `R × R`, an idempotent
-- that reduces to the class of `(1, 0)` is `(1, 0)`.
example (R : Type u) [CommRing R] [HenselianLocalRing R] (e : R × R)
    (he : IsIdempotentElem e)
    (hmk : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R (R × R))) e =
      Ideal.Quotient.mk _ (1, 0)) :
    e = (1, 0) := by
  have h10 : IsIdempotentElem ((1, 0) : R × R) := by
    simp [IsIdempotentElem]
  exact (HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
    (Ideal.Quotient.mk _ ((1, 0) : R × R)) (h10.map _)).unique ⟨he, hmk⟩ ⟨h10, rfl⟩
