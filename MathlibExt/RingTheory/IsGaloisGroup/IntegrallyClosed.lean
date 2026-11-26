/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed.lean`
and
`P2M/Sol/S_IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed.lean`
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

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IsGaloisGroup.Defs

/-!
# The invariant ring of a group action on an integrally closed domain

If a group `G` acts on a domain `B` whose subring `A` is its invariant ring (the
action commutes with `A`, and every element of `B` fixed by `G` comes from `A`,
in the sense of `Algebra.IsInvariant A B G`) and `B` is integrally closed, then
so is `A`: an element of the fraction field of `A` that is integral over `A` is
integral over `B`, hence lies in `B`, is fixed by `G`, and therefore lies in
`A`. The action of `G` need not be faithful, but the algebra map `A → B` must be
injective (`FaithfulSMul A B`); the case of a Galois group (`IsGaloisGroup G A B`)
is a corollary.
-/

@[expose] public section

open Polynomial

/-- **Invariant subrings of integrally closed domains are integrally closed.** Let a group `G`
act on an integrally closed domain `B` containing the domain `A`, commuting with `A`, such
that every element of `B` fixed by `G` comes from `A`. Then `A` is integrally closed. The
action of `G` need not be faithful, but the algebra map `A → B` must be injective
(`FaithfulSMul A B`). -/
theorem Algebra.IsInvariant.isIntegrallyClosed_of_isIntegrallyClosed
    (G : Type*) [Group G] {A B : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Algebra A B] [FaithfulSMul A B] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G] [IsIntegrallyClosed B] :
    IsIntegrallyClosed A := by
  classical
  let K := FractionRing A
  let L := FractionRing B
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hinjL : Function.Injective ((algebraMap B L).comp (algebraMap A B)) :=
    (IsFractionRing.injective B L).comp hinj
  let φ : K →+* L := IsFractionRing.lift hinjL
  have hφ : ∀ a : A, φ (algebraMap A K a) = algebraMap B L (algebraMap A B a) :=
    fun a => IsFractionRing.lift_algebraMap hinjL a
  refine (isIntegrallyClosed_iff K).mpr ?_
  intro x hx
  obtain ⟨a₁, a₂, ha₂, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have ha₂0 : a₂ ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha₂
  have hfa₂ : algebraMap A B a₂ ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha₂0
  have hKa₂ : algebraMap A K a₂ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha₂
  have hLa₂ : algebraMap B L (algebraMap A B a₂) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hfa₂
  have hint : IsIntegral B (φ (algebraMap A K a₁ / algebraMap A K a₂)) := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (algebraMap A B), hp.map _, ?_⟩
    rw [eval₂_map]
    have hcomp : (algebraMap B L).comp (algebraMap A B) = φ.comp (algebraMap A K) := by
      ext a; simp [hφ]
    rw [hcomp, ← hom_eval₂, hpx, map_zero]
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := B) (K := L)).mp hint
  rw [map_div₀, hφ, hφ, eq_div_iff hLa₂, ← map_mul] at hb
  have hb' : b * algebraMap A B a₂ = algebraMap A B a₁ :=
    IsFractionRing.injective B L hb
  have hfix : ∀ g : G, g • b = b := by
    intro g
    apply mul_right_cancel₀ hfa₂
    have h1 : g • (b * algebraMap A B a₂) = b * algebraMap A B a₂ := by
      rw [hb', smul_algebraMap]
    rwa [smul_mul', smul_algebraMap] at h1
  obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) b hfix
  refine ⟨a, ?_⟩
  have haa : a * a₂ = a₁ := hinj (by rw [map_mul, ha, hb'])
  rw [eq_div_iff hKa₂, ← map_mul, haa]

/-- **Galois-fixed subrings of integrally closed domains are integrally closed.** Let `A` and
`B` be domains, with the algebra map `A → B` injective (`FaithfulSMul A B`), and let `G` be a
Galois group for `B / A`. If `B` is integrally closed, then so is `A`. -/
theorem IsGaloisGroup.isIntegrallyClosed_of_isIntegrallyClosed
    (G : Type*) [Group G] {A B : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Algebra A B] [FaithfulSMul A B] [MulSemiringAction G B]
    [IsGaloisGroup G A B] [IsIntegrallyClosed B] : IsIntegrallyClosed A :=
  Algebra.IsInvariant.isIntegrallyClosed_of_isIntegrallyClosed (B := B) G
