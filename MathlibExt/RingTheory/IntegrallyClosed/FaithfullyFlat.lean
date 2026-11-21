/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsIntegrallyClosed_of_faithfullyFlat.lean`
and
`P2M/Sol/S_IsIntegrallyClosed_of_faithfullyFlat.lean`
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

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.FaithfullyFlat

@[expose] public section

universe u v

namespace IsIntegrallyClosed

/-- Integral closedness descends along a faithfully flat algebra of domains:
if `B` is integrally closed and `A → B` is faithfully flat, then `A` is
integrally closed. No locality hypothesis on either ring is needed. -/
theorem of_faithfullyFlat {A : Type u} {B : Type v} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.FaithfullyFlat A B]
    [IsIntegrallyClosed B] : IsIntegrallyClosed A := by
  have hinj : Function.Injective (algebraMap A B) :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance).injective
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  let φ : FractionRing A →+* FractionRing B :=
    IsFractionRing.map (A := A) (B := B) (K := FractionRing A)
      (L := FractionRing B) (j := algebraMap A B) hinj
  have hφ : ∀ r : A, φ (algebraMap A (FractionRing A) r) =
      algebraMap B (FractionRing B) (algebraMap A B r) := by
    intro r; simp [φ, IsFractionRing.map]
  have hx' : IsIntegral B (φ (algebraMap A _ a / algebraMap A _ b)) := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (algebraMap A B), hp.map _, ?_⟩
    have hcomp : φ.comp (algebraMap A (FractionRing A)) =
        (algebraMap B (FractionRing B)).comp (algebraMap A B) :=
      RingHom.ext hφ
    rw [Polynomial.eval₂_map, ← hcomp, ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨s, hs⟩ := (isIntegrallyClosed_iff (FractionRing B)).mp
    inferInstance hx'
  have hfb0 : algebraMap A B b ≠ 0 := fun h => hb0 (hinj (by simpa using h))
  have hdiv : algebraMap A B a = s * algebraMap A B b := by
    have h1 : algebraMap B (FractionRing B) s =
        algebraMap B (FractionRing B) (algebraMap A B a) /
          algebraMap B (FractionRing B) (algebraMap A B b) := by
      rw [hs, map_div₀, hφ, hφ]
    have h2 : algebraMap B (FractionRing B) (algebraMap A B b) ≠ 0 := by
      simpa using hfb0
    apply IsFractionRing.injective B (FractionRing B)
    rw [map_mul, h1, div_mul_cancel₀ _ h2]
  have hmem : a ∈ Ideal.comap (algebraMap A B)
      ((Ideal.span {b}).map (algebraMap A B)) := by
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton, hdiv]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨r, ?_⟩
  have hthis : algebraMap A (FractionRing A) b ≠ 0 := by simpa using hb0
  rw [eq_div_iff hthis, ← map_mul, hr]

end IsIntegrallyClosed
