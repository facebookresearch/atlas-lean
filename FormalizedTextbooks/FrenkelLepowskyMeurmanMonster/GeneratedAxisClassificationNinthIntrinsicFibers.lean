/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingClasses
public import Mathlib.LinearAlgebra.Span.Basic

/-! Intrinsic affine marking fibers recover linear subspaces using differences inside a
specified actual lattice-quotient subspace. This construction commutes with every genuine
linear isometry preserving the marking carrier and that subspace. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Differences from a marked point which remain in the specified quotient subspace. -/
def generatedNinthIntrinsicFiberDifferences
    (R : Submodule (ZMod 2) LeechModTwo) (C : Set LeechModTwo) (v : LeechModTwo) :
    Set LeechModTwo := {u | u ∈ R ∧ u + v ∈ C}

/-- The linear subspace intrinsically recovered from one affine marking fiber. -/
def generatedNinthIntrinsicFiberSpan
    (R : Submodule (ZMod 2) LeechModTwo) (C : Set LeechModTwo) (v : LeechModTwo) :
    Submodule (ZMod 2) LeechModTwo :=
  Submodule.span (ZMod 2) (generatedNinthIntrinsicFiberDifferences R C v)

/-- Every genuine linear equivalence transports the full difference fiber. -/
theorem generatedNinth_intrinsic_fiber_differences_map
    (f : LeechModTwo ≃ₗ[ZMod 2] LeechModTwo)
    (R : Submodule (ZMod 2) LeechModTwo) (C : Set LeechModTwo) (v : LeechModTwo) :
    f '' generatedNinthIntrinsicFiberDifferences R C v =
      generatedNinthIntrinsicFiberDifferences (R.map f.toLinearMap) (f '' C) (f v) := by
  ext u
  constructor
  · rintro ⟨w, ⟨hw, hc⟩, rfl⟩
    refine ⟨Submodule.mem_map.mpr ⟨w, hw, rfl⟩, ?_⟩
    exact ⟨w + v, hc, map_add f w v⟩
  · rintro ⟨hr, hc⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hr
    obtain ⟨x, hx, hxe⟩ := hc
    have he : x = w + v := f.injective (hxe.trans (map_add f w v).symm)
    exact ⟨w, ⟨hw, he ▸ hx⟩, rfl⟩

/-- The recovered whole subspace, not merely its finite point list, is transported. -/
theorem generatedNinth_intrinsic_fiber_span_map
    (f : LeechModTwo ≃ₗ[ZMod 2] LeechModTwo)
    (R : Submodule (ZMod 2) LeechModTwo) (C : Set LeechModTwo) (v : LeechModTwo) :
    (generatedNinthIntrinsicFiberSpan R C v).map f.toLinearMap =
      generatedNinthIntrinsicFiberSpan (R.map f.toLinearMap) (f '' C) (f v) := by
  rw [generatedNinthIntrinsicFiberSpan, Submodule.map_span]
  change Submodule.span (ZMod 2) (f '' generatedNinthIntrinsicFiberDifferences R C v) = _
  rw [generatedNinth_intrinsic_fiber_differences_map]
  rfl

/-- The unordered family of all subspaces intrinsically recovered from actual markings. -/
def generatedNinthIntrinsicFiberFamily
    (R : Submodule (ZMod 2) LeechModTwo) (C : Set LeechModTwo) :
    Set (Submodule (ZMod 2) LeechModTwo) :=
  generatedNinthIntrinsicFiberSpan R C '' C

/-- Preserving both actual carriers preserves their entire recovered family of subspaces. -/
theorem generatedNinth_intrinsic_fiber_family_preserved
    (f : LeechModTwo ≃ₗ[ZMod 2] LeechModTwo)
    (R : Submodule (ZMod 2) LeechModTwo) (C : Set LeechModTwo)
    (hR : R.map f.toLinearMap = R) (hC : f '' C = C) :
    (fun W : Submodule (ZMod 2) LeechModTwo => W.map f.toLinearMap) ''
        generatedNinthIntrinsicFiberFamily R C = generatedNinthIntrinsicFiberFamily R C := by
  unfold generatedNinthIntrinsicFiberFamily
  rw [Set.image_image]
  have he : (fun v => (generatedNinthIntrinsicFiberSpan R C v).map f.toLinearMap) =
      generatedNinthIntrinsicFiberSpan R C ∘ f := by
    funext v
    rw [generatedNinth_intrinsic_fiber_span_map, hR, hC]
    rfl
  rw [he, Set.image_comp, hC]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
