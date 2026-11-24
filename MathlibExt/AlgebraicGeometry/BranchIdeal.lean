/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_
vanishingIdeal_closure_eq_branchIdeal.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_
vanishingIdeal_closure_eq_branchIdeal.lean`
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

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Stalk

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The branch ideal of a specialization `ξ ⤳ x`: the prime ideal of the stalk
at `x` consisting of germs whose specialization to `ξ` lies in the maximal
ideal of the stalk at `ξ`. -/
public noncomputable def branchIdeal {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x) :
    Ideal (X.presheaf.stalk x) :=
  Ideal.comap (X.presheaf.stalkSpecializes h).hom
    (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ))

instance branchIdeal_isPrime {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x) :
    (branchIdeal h).IsPrime :=
  Ideal.comap_isPrime _ _

/-- Membership in the branch ideal, by definition of the comap. -/
theorem mem_branchIdeal_iff {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x)
    (a : X.presheaf.stalk x) :
    a ∈ branchIdeal h ↔
      (X.presheaf.stalkSpecializes h).hom a ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) :=
  Iff.rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.IdealSheafData

private theorem vanishingIdeal_closure_ideal_eq {X : Scheme.{u}} (U : X.affineOpens)
    (ξ : X) (hξ : ξ ∈ (U : X.Opens)) :
    (vanishingIdeal ⟨closure ({ξ} : Set X), isClosed_closure⟩).ideal U =
      (U.2.primeIdealOf ⟨ξ, hξ⟩).asIdeal := by
  have hU : IsAffineOpen (U : X.Opens) := U.2
  rw [vanishingIdeal_ideal]
  have hpre : ⇑hU.fromSpec ⁻¹' closure ({ξ} : Set X) =
      closure {hU.primeIdealOf ⟨ξ, hξ⟩} := by
    rw [hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      hU.fromSpec.continuous]
    congr 1
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hq
      apply hU.fromSpec.isOpenEmbedding.injective
      rw [hq, IsAffineOpen.fromSpec_primeIdealOf]
    · rintro rfl
      exact hU.fromSpec_primeIdealOf ⟨ξ, hξ⟩
  refine (congrArg PrimeSpectrum.vanishingIdeal hpre).trans ?_
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    PrimeSpectrum.vanishingIdeal_singleton,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  exact (hU.primeIdealOf ⟨ξ, hξ⟩).isPrime.radical

/-- The germ at `x` of the vanishing ideal of the closure of a specializing
point `ξ` is the branch ideal of the specialization. -/
public theorem map_germ_vanishingIdeal_closure_eq_branchIdeal
    {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x) (U : X.affineOpens)
    (hx : x ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom
        ((vanishingIdeal ⟨closure {ξ}, isClosed_closure⟩).ideal U) =
      Scheme.branchIdeal h := by
  classical
  have hU : IsAffineOpen (U : X.Opens) := U.2
  have hξ : ξ ∈ (U : X.Opens) := h.mem_open U.1.isOpen hx
  rw [vanishingIdeal_closure_ideal_eq U ξ hξ]
  letI algx := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : (U : X.Opens))
  haveI locx := hU.isLocalization_stalk ⟨x, hx⟩
  let R := Γ(X, (U : X.Opens))
  let 𝔮 := hU.primeIdealOf ⟨ξ, hξ⟩
  let S := (X.presheaf.stalkSpecializes h).hom
  have hS : ∀ a : R, S ((X.presheaf.germ (U : X.Opens) x hx).hom a) =
      (X.presheaf.germ (U : X.Opens) ξ hξ).hom a := by
    intro a
    exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hx h a
  have hmem : ∀ a : R, (X.presheaf.germ (U : X.Opens) ξ hξ).hom a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ↔ a ∈ 𝔮.asIdeal := by
    intro a
    letI algξ := X.presheaf.algebra_section_stalk (⟨ξ, hξ⟩ : (U : X.Opens))
    haveI locξ := hU.isLocalization_stalk ⟨ξ, hξ⟩
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk ξ)
      𝔮.asIdeal a
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Scheme.mem_branchIdeal_iff]
    change S ((X.presheaf.germ (U : X.Opens) x hx).hom a) ∈ _
    rw [hS]
    exact (hmem a).mpr ha
  · intro s hs
    rw [Scheme.mem_branchIdeal_iff] at hs
    obtain ⟨⟨a, t⟩, hat⟩ :=
      IsLocalization.mk'_surjective (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl s
    simp only at hat
    subst hat
    have hxt : x ∈ X.basicOpen (t : R) := by
      rw [X.mem_basicOpen (t : R) x hx]
      exact IsLocalization.map_units
        (M := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (X.presheaf.stalk x) t
    have hξt : ξ ∈ X.basicOpen (t : R) := h.mem_open (X.basicOpen (t : R)).isOpen hxt
    have hunit : IsUnit ((X.presheaf.germ (U : X.Opens) ξ hξ).hom (t : R)) :=
      (X.mem_basicOpen (t : R) ξ hξ).mp hξt
    have hspec : S (IsLocalization.mk' (X.presheaf.stalk x) a t) *
        (X.presheaf.germ (U : X.Opens) ξ hξ).hom (t : R) =
        (X.presheaf.germ (U : X.Opens) ξ hξ).hom a := by
      rw [← hS (t : R), ← map_mul]
      change S (IsLocalization.mk' (X.presheaf.stalk x) a t *
        algebraMap R (X.presheaf.stalk x) (t : R)) = _
      rw [IsLocalization.mk'_spec, ← hS a]
      rfl
    have ha : a ∈ 𝔮.asIdeal := by
      rw [← hmem a, ← hspec]
      exact Ideal.mul_mem_right _ _ hs
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)

end AlgebraicGeometry.Scheme.IdealSheafData
