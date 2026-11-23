/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.CompactlyGenerated.FiniteRealization
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators
public import MathlibExt.CategoryTheory.Functor.FullyFaithfulLifting

/-!
# Realized boundary and horn generators in compactly generated spaces

Finite realized boundaries, horns, and simplices live natively in
`CompactlyGenerated`. Their maps are the fully faithful preimages of the
existing `TopCat` realization maps. Consequently their right lifting classes
are exactly the inverse images of the corresponding `TopCat` classes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MorphismProperty
open scoped Simplicial

universe u v

namespace CompactlyGenerated

/-- The realized boundary inclusion internal to compactly generated spaces. -/
noncomputable def realizedBoundaryInclusion (n : ℕ) :
    SSet.toCompactlyGeneratedOfFinite (SSet.boundary.{v} n) ⟶
      SSet.toCompactlyGeneratedOfFinite (Δ[n] : SSet.{v}) :=
  fullyFaithfulCompactlyGeneratedToTop.preimage
    (SSet.toTop.map (SSet.boundary.{v} n).ι)

/-- A positive-dimensional realized horn inclusion internal to compactly
generated spaces. -/
noncomputable def realizedHornInclusion (n : ℕ) (i : Fin (n + 2)) :
    SSet.toCompactlyGeneratedOfFinite (SSet.horn.{v} (n + 1) i) ⟶
      SSet.toCompactlyGeneratedOfFinite (Δ[n + 1] : SSet.{v}) :=
  fullyFaithfulCompactlyGeneratedToTop.preimage
    (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)

/-- Realized boundary inclusions internal to compactly generated spaces. -/
noncomputable def realizedBoundaryInclusions :
    MorphismProperty CompactlyGenerated.{u, v} :=
  .ofHoms (fun n : ℕ => realizedBoundaryInclusion n)

/-- Positive-dimensional realized horn inclusions internal to compactly
generated spaces. -/
noncomputable def realizedHornInclusions :
    MorphismProperty CompactlyGenerated.{u, v} :=
  ⨆ n : ℕ, .ofHoms
    (fun i : Fin (n + 2) => realizedHornInclusion n i)

theorem boundary_mem_realizedBoundaryInclusions (n : ℕ) :
    realizedBoundaryInclusions.{u, v} (realizedBoundaryInclusion n) := by
  constructor

theorem horn_mem_realizedHornInclusions (n : ℕ) (i : Fin (n + 2)) :
    realizedHornInclusions.{u, v} (realizedHornInclusion n i) := by
  unfold realizedHornInclusions
  rw [MorphismProperty.iSup_iff]
  exact ⟨n, ⟨i⟩⟩

theorem compactlyGeneratedToTop_map_realizedBoundaryInclusion (n : ℕ) :
    compactlyGeneratedToTop.{u, v}.map
        (realizedBoundaryInclusion.{v, u} n) =
      SSet.toTop.map (SSet.boundary.{v} n).ι :=
  fullyFaithfulCompactlyGeneratedToTop.map_preimage _

theorem compactlyGeneratedToTop_map_realizedHornInclusion
    (n : ℕ) (i : Fin (n + 2)) :
    compactlyGeneratedToTop.{u, v}.map
        (realizedHornInclusion.{v, u} n i) =
      SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι :=
  fullyFaithfulCompactlyGeneratedToTop.map_preimage _

theorem realizedBoundaryInclusions_rlp :
    realizedBoundaryInclusions.{u, v}.rlp =
      TopCat.realizedBoundaryInclusions.{v}.rlp.inverseImage
        compactlyGeneratedToTop.{u, v} := by
  ext X Y p
  constructor
  · intro hp A B i hi
    obtain ⟨n⟩ := hi
    have hInternal :
        HasLiftingProperty (realizedBoundaryInclusion n) p :=
      hp _ (boundary_mem_realizedBoundaryInclusions n)
    have hMapped :
        HasLiftingProperty
          (compactlyGeneratedToTop.{u, v}.map
            (realizedBoundaryInclusion n))
          (compactlyGeneratedToTop.{u, v}.map p) :=
      (Functor.hasLiftingProperty_map_iff_of_full_faithful
        compactlyGeneratedToTop.{u, v}
        (realizedBoundaryInclusion n) p).mpr hInternal
    rw [compactlyGeneratedToTop_map_realizedBoundaryInclusion] at hMapped
    exact hMapped
  · intro hp A B i hi
    obtain ⟨n⟩ := hi
    have hMapped :
        HasLiftingProperty
          (compactlyGeneratedToTop.{u, v}.map
            (realizedBoundaryInclusion n))
          (compactlyGeneratedToTop.{u, v}.map p) := by
      rw [compactlyGeneratedToTop_map_realizedBoundaryInclusion]
      exact hp _ (TopCat.boundary_mem_realizedBoundaryInclusions n)
    exact (Functor.hasLiftingProperty_map_iff_of_full_faithful
      compactlyGeneratedToTop.{u, v}
      (realizedBoundaryInclusion n) p).mp hMapped

theorem realizedHornInclusions_rlp :
    realizedHornInclusions.{u, v}.rlp =
      TopCat.realizedHornInclusions.{v}.rlp.inverseImage
        compactlyGeneratedToTop.{u, v} := by
  ext X Y p
  constructor
  · intro hp A B i hi
    unfold TopCat.realizedHornInclusions at hi
    rw [MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨j⟩⟩ := hi
    have hInternal :
        HasLiftingProperty (realizedHornInclusion n j) p :=
      hp _ (horn_mem_realizedHornInclusions n j)
    have hMapped :
        HasLiftingProperty
          (compactlyGeneratedToTop.{u, v}.map
            (realizedHornInclusion n j))
          (compactlyGeneratedToTop.{u, v}.map p) :=
      (Functor.hasLiftingProperty_map_iff_of_full_faithful
        compactlyGeneratedToTop.{u, v}
        (realizedHornInclusion n j) p).mpr hInternal
    rw [compactlyGeneratedToTop_map_realizedHornInclusion] at hMapped
    exact hMapped
  · intro hp A B i hi
    unfold realizedHornInclusions at hi
    rw [MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨j⟩⟩ := hi
    have hTop : TopCat.realizedHornInclusions.{v}
      (SSet.toTop.map (SSet.horn.{v} (n + 1) j).ι) := by
      unfold TopCat.realizedHornInclusions
      rw [MorphismProperty.iSup_iff]
      exact ⟨n, ⟨j⟩⟩
    have hMapped :
        HasLiftingProperty
          (compactlyGeneratedToTop.{u, v}.map
            (realizedHornInclusion n j))
          (compactlyGeneratedToTop.{u, v}.map p) := by
      rw [compactlyGeneratedToTop_map_realizedHornInclusion]
      exact hp _ hTop
    exact (Functor.hasLiftingProperty_map_iff_of_full_faithful
      compactlyGeneratedToTop.{u, v}
      (realizedHornInclusion n j) p).mp hMapped

end CompactlyGenerated
