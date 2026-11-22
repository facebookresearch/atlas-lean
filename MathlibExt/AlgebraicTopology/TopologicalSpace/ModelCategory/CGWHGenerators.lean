/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CompactlyGeneratedGenerators
public import MathlibExt.AlgebraicTopology.TopologicalSpace.CGWH.FiniteRealization

/-!
# Realized boundary and horn generators in CGWH spaces

Finite realized boundaries, horns, and simplices live natively in `CGWH`.
Their maps are the fully faithful preimages of the compactly-generated
generator maps, so their right lifting classes are exactly the inverse images
along the immediate inclusion.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MorphismProperty
open scoped Simplicial

universe u v

namespace CGWH

/-- The realized boundary inclusion internal to CGWH spaces. -/
noncomputable def realizedBoundaryInclusion (n : ℕ) :
    SSet.toCGWHOfFinite (SSet.boundary.{v} n) ⟶
      SSet.toCGWHOfFinite (Δ[n] : SSet.{v}) :=
  fullyFaithfulCgwhToCompactlyGenerated.preimage
    (CompactlyGenerated.realizedBoundaryInclusion n)

/-- A positive-dimensional realized horn inclusion internal to CGWH spaces. -/
noncomputable def realizedHornInclusion (n : ℕ) (i : Fin (n + 2)) :
    SSet.toCGWHOfFinite (SSet.horn.{v} (n + 1) i) ⟶
      SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v}) :=
  fullyFaithfulCgwhToCompactlyGenerated.preimage
    (CompactlyGenerated.realizedHornInclusion n i)

/-- Realized boundary inclusions internal to CGWH spaces. -/
noncomputable def realizedBoundaryInclusions :
    MorphismProperty CGWH.{u, v} :=
  .ofHoms (fun n : ℕ => realizedBoundaryInclusion n)

/-- Positive-dimensional realized horn inclusions internal to CGWH spaces. -/
noncomputable def realizedHornInclusions : MorphismProperty CGWH.{u, v} :=
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

theorem cgwhToCompactlyGenerated_map_realizedBoundaryInclusion (n : ℕ) :
    cgwhToCompactlyGenerated.{u, v}.map
        (realizedBoundaryInclusion.{v, u} n) =
      CompactlyGenerated.realizedBoundaryInclusion n :=
  fullyFaithfulCgwhToCompactlyGenerated.map_preimage _

theorem cgwhToCompactlyGenerated_map_realizedHornInclusion
    (n : ℕ) (i : Fin (n + 2)) :
    cgwhToCompactlyGenerated.{u, v}.map
        (realizedHornInclusion.{v, u} n i) =
      CompactlyGenerated.realizedHornInclusion n i :=
  fullyFaithfulCgwhToCompactlyGenerated.map_preimage _

theorem realizedBoundaryInclusions_rlp :
    realizedBoundaryInclusions.{u, v}.rlp =
      CompactlyGenerated.realizedBoundaryInclusions.{u, v}.rlp.inverseImage
        cgwhToCompactlyGenerated.{u, v} := by
  ext X Y p
  constructor
  · intro hp A B i hi
    obtain ⟨n⟩ := hi
    have hInternal :
        HasLiftingProperty (realizedBoundaryInclusion n) p :=
      hp _ (boundary_mem_realizedBoundaryInclusions n)
    have hMapped :
        HasLiftingProperty
          (cgwhToCompactlyGenerated.{u, v}.map
            (realizedBoundaryInclusion n))
          (cgwhToCompactlyGenerated.{u, v}.map p) :=
      (Functor.hasLiftingProperty_map_iff_of_full_faithful
        cgwhToCompactlyGenerated.{u, v}
        (realizedBoundaryInclusion n) p).mpr hInternal
    rw [cgwhToCompactlyGenerated_map_realizedBoundaryInclusion] at hMapped
    exact hMapped
  · intro hp A B i hi
    obtain ⟨n⟩ := hi
    have hMapped :
        HasLiftingProperty
          (cgwhToCompactlyGenerated.{u, v}.map
            (realizedBoundaryInclusion n))
          (cgwhToCompactlyGenerated.{u, v}.map p) := by
      rw [cgwhToCompactlyGenerated_map_realizedBoundaryInclusion]
      exact hp _
        (CompactlyGenerated.boundary_mem_realizedBoundaryInclusions n)
    exact (Functor.hasLiftingProperty_map_iff_of_full_faithful
      cgwhToCompactlyGenerated.{u, v}
      (realizedBoundaryInclusion n) p).mp hMapped

theorem realizedHornInclusions_rlp :
    realizedHornInclusions.{u, v}.rlp =
      CompactlyGenerated.realizedHornInclusions.{u, v}.rlp.inverseImage
        cgwhToCompactlyGenerated.{u, v} := by
  ext X Y p
  constructor
  · intro hp A B i hi
    unfold CompactlyGenerated.realizedHornInclusions at hi
    rw [MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨j⟩⟩ := hi
    have hInternal :
        HasLiftingProperty (realizedHornInclusion n j) p :=
      hp _ (horn_mem_realizedHornInclusions n j)
    have hMapped :
        HasLiftingProperty
          (cgwhToCompactlyGenerated.{u, v}.map
            (realizedHornInclusion n j))
          (cgwhToCompactlyGenerated.{u, v}.map p) :=
      (Functor.hasLiftingProperty_map_iff_of_full_faithful
        cgwhToCompactlyGenerated.{u, v}
        (realizedHornInclusion n j) p).mpr hInternal
    rw [cgwhToCompactlyGenerated_map_realizedHornInclusion] at hMapped
    exact hMapped
  · intro hp A B i hi
    unfold realizedHornInclusions at hi
    rw [MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨j⟩⟩ := hi
    have hMapped :
        HasLiftingProperty
          (cgwhToCompactlyGenerated.{u, v}.map
            (realizedHornInclusion n j))
          (cgwhToCompactlyGenerated.{u, v}.map p) := by
      rw [cgwhToCompactlyGenerated_map_realizedHornInclusion]
      exact hp _
        (CompactlyGenerated.horn_mem_realizedHornInclusions n j)
    exact (Functor.hasLiftingProperty_map_iff_of_full_faithful
      cgwhToCompactlyGenerated.{u, v}
      (realizedHornInclusion n j) p).mp hMapped

end CGWH
