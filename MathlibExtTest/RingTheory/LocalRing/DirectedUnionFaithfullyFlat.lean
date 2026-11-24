/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.DirectedUnionFaithfullyFlat

@[expose] public section

set_option autoImplicit false

universe u v

open IsLocalRing in
/-- Exact-source consumer, using the original binders verbatim. -/
example (A : Type u) [CommRing A] {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)]
    (S : ι → Subring A) (hS : Monotone S) (hcov : ∀ x : A, ∃ i, x ∈ S i)
    [∀ i, IsLocalRing (S i)] [∀ i, IsNoetherianRing (S i)]
    (hflat : ∀ ⦃i j : ι⦄ (h : i ≤ j), (Subring.inclusion (hS h)).Flat)
    (hmax : ∀ ⦃i j : ι⦄ (h : i ≤ j),
      Ideal.map (Subring.inclusion (hS h)) (maximalIdeal (S i)) = maximalIdeal (S j)) :
    ∃ _ : IsLocalRing A, IsNoetherianRing A ∧
      ∀ i, Module.FaithfullyFlat (S i) A ∧
        Ideal.map (algebraMap (S i) A) (maximalIdeal (S i)) = maximalIdeal A :=
  Subring.exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq
    A S hS hcov hflat hmax

/-- The same consumer in higher universes. -/
example (A : Type 1) [CommRing A] {ι : Type 1} [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)]
    (S : ι → Subring A) (hS : Monotone S) (hcov : ∀ x : A, ∃ i, x ∈ S i)
    [∀ i, IsLocalRing (S i)] [∀ i, IsNoetherianRing (S i)]
    (hflat : ∀ ⦃i j : ι⦄ (h : i ≤ j), (Subring.inclusion (hS h)).Flat)
    (hmax : ∀ ⦃i j : ι⦄ (h : i ≤ j),
      Ideal.map (Subring.inclusion (hS h)) (IsLocalRing.maximalIdeal (S i)) =
        IsLocalRing.maximalIdeal (S j)) :
    ∃ _ : IsLocalRing A, IsNoetherianRing A ∧
      ∀ i, Module.FaithfullyFlat (S i) A ∧
        Ideal.map (algebraMap (S i) A) (IsLocalRing.maximalIdeal (S i)) =
          IsLocalRing.maximalIdeal A :=
  Subring.exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq
    A S hS hcov hflat hmax

/-- Boundary example: a one-stage tower recovers the stage itself. -/
example (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ _ : IsLocalRing A, IsNoetherianRing A ∧
      ∀ _ : Unit, Module.FaithfullyFlat A A ∧
        Ideal.map (algebraMap A A) (IsLocalRing.maximalIdeal A) =
          IsLocalRing.maximalIdeal A := by
  refine ⟨inferInstance, inferInstance, fun _ => ⟨?_, ?_⟩⟩
  · exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  · simp
