/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Faithfully flat algebras inside a localization

A faithfully flat algebra embedded compatibly in a localization of its base
is the base ring. The proof contracts a principal ideal and cancels the
image of its generator, which is a unit in the localization.

In particular, this applies to faithfully flat birational algebras. It
generalizes the bijectivity statement in the source's `Theorems/` file
`Thm_IsDiscreteValuationRing_bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing.lean`
of `anthropics/fermats-last-theorem`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`. The original type is exercised
in the companion test module; the proof here does not use valuation theory.
-/

public section

/-- **Faithfully flat algebras inside a localization equal the base ring.**
A faithfully flat `R`-algebra `S` which embeds compatibly in a localization
`K` of `R` has bijective structure map. No restriction on the denominators
or domain assumptions on the rings are required. -/
theorem IsLocalization.bijective_algebraMap_of_faithfullyFlat
    (R S K : Type*) [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra S K] [Algebra R K] [IsScalarTower R S K]
    (M : Submonoid R) [IsLocalization M K]
    [FaithfulSMul S K] [Module.FaithfullyFlat R S] :
    Function.Bijective (algebraMap R S) := by
  refine ⟨FaithfulSMul.algebraMap_injective R S, fun x ↦ ?_⟩
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj M (algebraMap S K x)
  have hmul : x * algebraMap R S b = algebraMap R S a := by
    apply FaithfulSMul.algebraMap_injective S K
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply] using hab
  have ha : a ∈ Ideal.span {(b : R)} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S)
      (Ideal.span {(b : R)})]
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton, ← hmul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp ha
  refine ⟨r, FaithfulSMul.algebraMap_injective S K ?_⟩
  apply (IsLocalization.map_units K b).mul_left_inj.mp
  rw [← IsScalarTower.algebraMap_apply, ← map_mul, hr, hab]
