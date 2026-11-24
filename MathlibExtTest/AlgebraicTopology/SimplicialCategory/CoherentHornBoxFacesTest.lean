/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornBoxFaces

/-! # The smallest inner coherent horn and its Hom box

For `Λ[2, 1]` the outer coherent Hom runs from vertex `0` to vertex `2`, and the only
interior label is the middle vertex. So the box has exactly one positive face and no
negative face, and `cover` says the box is that single composition face. The supplied
face maps read back their positive composition map.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial
open CategoryTheory.SimplicialEnrichment
open CategoryTheory.CoherentRealization HornBoxFaces

namespace CoherentHornBoxFacesTest

theorem one_ne_zero : (1 : Fin 3) ≠ 0 := by decide

theorem one_ne_last : (1 : Fin 3) ≠ Fin.last 2 := by decide

/-- In the smallest inner horn every interior label is the middle vertex. -/
theorem vertex_eq_one (b : Interior.{u} 0) : vertex b = 1 := by
  obtain ⟨⟨v⟩, h₀, h₂⟩ := b
  change (0 : Fin 3) < v at h₀
  change v < Fin.last 2 at h₂
  change v = 1
  revert h₀ h₂
  fin_cases v <;> decide

/-- The interior is exactly the middle vertex. -/
theorem interior_eq_inner (b : Interior.{u} 0) : b = inner 1 one_ne_zero one_ne_last :=
  Subtype.ext (ULift.ext (vertex_eq_one b))

/-- No negative label survives at the missing middle vertex. -/
theorem no_negative (k : {k : Interior.{u} 0 // vertex k ≠ 1}) : False :=
  k.property (vertex_eq_one k.val)

/-- Every box label of the smallest inner horn is the single positive one. -/
theorem index_eq (x : Index.{u} (1 : Fin 3)) : x = .inl (inner 1 one_ne_zero one_ne_last) := by
  rcases x with b | k
  · exact congrArg Sum.inl (interior_eq_inner b)
  · exact (no_negative k).elim

/-- The interior is inhabited: the middle vertex is a genuine interior label. -/
theorem vertex_inner : vertex (inner.{u} (1 : Fin 3) one_ne_zero one_ne_last) = 1 := rfl

/-- `cover` read back at `n = 0`: the Hom box is the single positive composition face. -/
theorem box_eq_positive :
    HomOpenBox.subcomplex (show (ULift.up.{u} (0 : Fin 3)) ≤ ULift.up (Fin.last 2) from
      Fin.zero_le _) (inner 1 one_ne_zero one_ne_last) =
      CompositionFace.positive (ULift.up 0) (ULift.up 1) (ULift.up (Fin.last 2)) := by
  rw [← cover (1 : Fin 3) one_ne_zero one_ne_last]
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [index_eq x]
    exact le_rfl
  · exact le_iSup (fun x : Index.{u} (1 : Fin 3) => face 1 x)
      (.inl (inner 1 one_ne_zero one_ne_last))

/-- The single positive face is the composition face through the middle vertex. -/
theorem face_inl : face (1 : Fin 3) (.inl (inner.{u} 1 one_ne_zero one_ne_last)) =
    CompositionFace.positive (ULift.up 0) (ULift.up 1) (ULift.up (Fin.last 2)) := rfl

variable {C : Carrier.{u}} (f : (Λ[2, 1] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The face map at the single positive label is its positive composition map. -/
theorem maps_inl :
    maps f one_ne_zero one_ne_last (.inl (inner 1 one_ne_zero one_ne_last)) =
      positiveMap f one_ne_zero one_ne_last (inner 1 one_ne_zero one_ne_last) := rfl

/-- Map readback at `n = 0`: through the composition-face chart, the box map is the target
composition of the two short Hom maps `0 → 1` and `1 → 2`. -/
theorem maps_readback :
    (CompositionFace.positiveIso (ULift.up 0) (ULift.up 1) (ULift.up (Fin.last 2))).hom ≫
        maps f one_ne_zero one_ne_last (.inl (inner 1 one_ne_zero one_ne_last)) =
      (leftMap f one_ne_zero one_ne_last (inner 1 one_ne_zero one_ne_last) ⊗ₘ
        rightMap f one_ne_zero one_ne_last (inner 1 one_ne_zero one_ne_last)) ≫
        eComp SSet.{u} (HornFaces.object f 0) (HornFaces.object f 1)
          (HornFaces.object f (Fin.last 2)) :=
  positiveMap_readback f one_ne_zero one_ne_last (inner 1 one_ne_zero one_ne_last)

end CoherentHornBoxFacesTest
