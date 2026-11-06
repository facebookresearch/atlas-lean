/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineMarkingClasses
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineAnchorCosets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineDirectionCoordinates

/-! Actual marking fibers recover their entire four-dimensional quotient subspaces.
The construction uses the actual original marking catalogue, not a chosen finite subset.
Preservation of the whole section range remains an explicit hypothesis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine quotient embedding of the eight discovered binary direction coordinates. -/
def generatedNinthAffineRootClassMap :
    (Fin 8 → ZMod 2) →ₗ[ZMod 2] LeechModTwo :=
  leechHyperbolicCoordinates.symm.toLinearMap.comp generatedNinthAffineRootMap

/-- The complete actual eight-direction quotient range containing all affine fiber directions. -/
def generatedNinthAffineRootClassRange : Submodule (ZMod 2) LeechModTwo :=
  generatedNinthAffineRootClassMap.range

/-- Each whole marking direction space is contained in the complete direction range. -/
theorem generatedNinth_affine_direction_class_le (i : Fin 9) :
    generatedNinthAffineDirectionClassSpace i ≤ generatedNinthAffineRootClassRange := by
  rintro v ⟨a, rfl⟩
  refine ⟨generatedNinthAffineDirectionRootMap i a, ?_⟩
  change leechHyperbolicCoordinates.symm
      (generatedNinthAffineRootMap (generatedNinthAffineDirectionRootMap i a)) =
    leechHyperbolicCoordinates.symm (generatedNinthAffineDirectionMap i a)
  exact congrArg leechHyperbolicCoordinates.symm
    (LinearMap.congr_fun (generatedNinth_affine_direction_factorization i) a)

/-- Distinct original quotient marking anchors have distinct cosets in the whole range. -/
theorem generatedNinth_affine_anchor_class_cosets_distinct (i j : Fin 9) (hij : i ≠ j) :
    generatedNinthAffineAnchorClass i - generatedNinthAffineAnchorClass j ∉
      generatedNinthAffineRootClassRange := by
  rintro ⟨a, ha⟩
  apply generatedNinth_affine_anchor_cosets_distinct i j hij
  refine ⟨a, ?_⟩
  have hb := congrArg leechHyperbolicCoordinates ha
  change leechHyperbolicCoordinates
      (leechHyperbolicCoordinates.symm (generatedNinthAffineRootMap a)) =
    leechHyperbolicCoordinates (leechHyperbolicCoordinates.symm _ -
      leechHyperbolicCoordinates.symm _) at hb
  simpa only [map_sub, LinearEquiv.apply_symm_apply] using hb

/-- The complete intrinsic difference fiber is exactly its whole actual direction subspace. -/
theorem generatedNinth_affine_fiber_differences (i : Fin 9) (a : Fin 4 → ZMod 2) :
    generatedNinthIntrinsicFiberDifferences generatedNinthAffineRootClassRange
      generatedNinthMarkedShortClasses
        (generatedNinthAffineAnchorClass i + generatedNinthAffineDirectionClassMap i a) =
      (generatedNinthAffineDirectionClassSpace i : Set LeechModTwo) := by
  ext u
  constructor
  · rintro ⟨hu, hc⟩
    rw [generatedNinth_marked_short_classes_eq_affine_range] at hc
    obtain ⟨⟨j, b⟩, he⟩ := hc
    change generatedNinthAffineAnchorClass j + generatedNinthAffineDirectionClassMap j b =
      u + (generatedNinthAffineAnchorClass i + generatedNinthAffineDirectionClassMap i a) at he
    have he' := he.symm
    have hij : i = j := by
      by_contra hij
      apply generatedNinth_affine_anchor_class_cosets_distinct i j hij
      have hi : generatedNinthAffineDirectionClassMap i a ∈
          generatedNinthAffineRootClassRange :=
        generatedNinth_affine_direction_class_le i ⟨a, rfl⟩
      have hj : generatedNinthAffineDirectionClassMap j b ∈
          generatedNinthAffineRootClassRange :=
        generatedNinth_affine_direction_class_le j ⟨b, rfl⟩
      have hv : generatedNinthAffineAnchorClass i - generatedNinthAffineAnchorClass j =
          generatedNinthAffineDirectionClassMap j b -
            generatedNinthAffineDirectionClassMap i a - u := by
        calc
          _ = (u + (generatedNinthAffineAnchorClass i +
                generatedNinthAffineDirectionClassMap i a)) -
              (generatedNinthAffineAnchorClass j + generatedNinthAffineDirectionClassMap j b) +
              (generatedNinthAffineDirectionClassMap j b -
                generatedNinthAffineDirectionClassMap i a - u) := by abel
          _ = _ := by rw [he', sub_self, zero_add]
      rw [hv]
      exact generatedNinthAffineRootClassRange.sub_mem
        (generatedNinthAffineRootClassRange.sub_mem hj hi) hu
    subst j
    have hv : u = generatedNinthAffineDirectionClassMap i b -
        generatedNinthAffineDirectionClassMap i a := by
      calc
        u = (u + (generatedNinthAffineAnchorClass i +
              generatedNinthAffineDirectionClassMap i a)) -
            (generatedNinthAffineAnchorClass i + generatedNinthAffineDirectionClassMap i a) := by
          abel
        _ = _ := by rw [he']; abel
    rw [hv]
    exact (generatedNinthAffineDirectionClassSpace i).sub_mem ⟨b, rfl⟩ ⟨a, rfl⟩
  · intro hu
    refine ⟨generatedNinth_affine_direction_class_le i hu, ?_⟩
    obtain ⟨b, rfl⟩ := hu
    rw [generatedNinth_marked_short_classes_eq_affine_range]
    refine ⟨(i, b + a), ?_⟩
    change generatedNinthAffineAnchorClass i + generatedNinthAffineDirectionClassMap i (b + a) =
      generatedNinthAffineDirectionClassMap i b +
        (generatedNinthAffineAnchorClass i + generatedNinthAffineDirectionClassMap i a)
    rw [map_add]
    abel

/-- Spanning the complete intrinsic fiber recovers the entire actual four-dimensional subspace. -/
theorem generatedNinth_affine_fiber_span (i : Fin 9) (a : Fin 4 → ZMod 2) :
    generatedNinthIntrinsicFiberSpan generatedNinthAffineRootClassRange
      generatedNinthMarkedShortClasses
        (generatedNinthAffineAnchorClass i + generatedNinthAffineDirectionClassMap i a) =
      generatedNinthAffineDirectionClassSpace i := by
  rw [generatedNinthIntrinsicFiberSpan, generatedNinth_affine_fiber_differences,
    Submodule.span_eq]

/-- The entire family recovered from the complete original markings is the nine whole spaces. -/
theorem generatedNinth_affine_fiber_family :
    generatedNinthIntrinsicFiberFamily generatedNinthAffineRootClassRange
      generatedNinthMarkedShortClasses = Set.range generatedNinthAffineDirectionClassSpace := by
  ext W
  constructor
  · rintro ⟨v, hv, hW⟩
    rw [generatedNinth_marked_short_classes_eq_affine_range] at hv
    obtain ⟨⟨i, a⟩, rfl⟩ := hv
    exact ⟨i, (generatedNinth_affine_fiber_span i a).symm.trans hW⟩
  · rintro ⟨i, rfl⟩
    refine ⟨generatedNinthAffineAnchorClass i + generatedNinthAffineDirectionClassMap i 0, ?_, ?_⟩
    · rw [generatedNinth_marked_short_classes_eq_affine_range]
      exact ⟨(i, 0), rfl⟩
    · exact generatedNinth_affine_fiber_span i 0

/-- Preserving both actual carriers preserves all nine entire recovered direction spaces. -/
theorem generatedNinth_affine_direction_family_preserved
    (f : LeechModTwo ≃ₗ[ZMod 2] LeechModTwo)
    (hR : generatedNinthAffineRootClassRange.map f.toLinearMap =
      generatedNinthAffineRootClassRange)
    (hC : f '' generatedNinthMarkedShortClasses = generatedNinthMarkedShortClasses) :
    (fun W : Submodule (ZMod 2) LeechModTwo => W.map f.toLinearMap) ''
      Set.range generatedNinthAffineDirectionClassSpace =
        Set.range generatedNinthAffineDirectionClassSpace := by
  rw [← generatedNinth_affine_fiber_family]
  exact generatedNinth_intrinsic_fiber_family_preserved f _ _ hR hC

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
