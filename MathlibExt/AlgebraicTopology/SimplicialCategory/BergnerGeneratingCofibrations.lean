/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerObjectLifting
import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-!
# The actual global Bergner generating cofibrations and their right class

The original small family consists of the empty-to-point map and EVERY
original two-object boundary map, including dimension zero. Its full
right class is exactly literal original object surjectivity and boundary
RLP of every original scalar Hom map. These are the C0 generators and
the right-class argument of HTT Proposition A.3.2.4, page 858.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.Bergner

/-- The SAME original empty-to-point and all original two-object boundary arrows. -/
def generatingCofibrationArrow : Option ℕ → Arrow Carrier.{u}
  | none => Arrow.mk BergnerObjects.inclusion.{u}
  | some n => Arrow.mk (BergnerTwoObject.map.{u} (∂Δ[n]).ι)

/-- The genuine original countable global Bergner cofibration generating family. -/
def generatingCofibrations : MorphismProperty Carrier.{u} :=
  .ofHoms (fun k : Option ℕ => (generatingCofibrationArrow.{u} k).hom)

instance generatingCofibrations_isSmall : generatingCofibrations.{u}.IsSmall.{u} :=
  MorphismProperty.isSmall_ofHoms _

/-- The literal original object-adding map belongs to the genuine global family. -/
theorem object_mem_generatingCofibrations : generatingCofibrations.{u} BergnerObjects.inclusion.{u} :=
  MorphismProperty.ofHoms.mk none

/-- EVERY original two-object boundary belongs, including zero and all higher original dimensions. -/
theorem boundary_mem_generatingCofibrations (n : ℕ) :
    generatingCofibrations.{u} (BergnerTwoObject.map.{u} (∂Δ[n]).ι) :=
  MorphismProperty.ofHoms.mk (some n)

/-- Global generator right lifting retains literal object surjectivity and EVERY entire original Hom map. -/
theorem generatingCofibrations_rlp_iff {C D : Carrier.{u}} (F : C ⟶ D) :
    generatingCofibrations.rlp F ↔ Function.Surjective F.obj ∧
      ∀ x y : C, SSet.modelCategoryQuillen.I.rlp (F.map x y) := by
  constructor
  · intro h
    refine ⟨(BergnerObjects.hasLiftingProperty_iff F).mp (h _ object_mem_generatingCofibrations), ?_⟩
    intro x y A B i hi
    obtain ⟨n⟩ := hi
    exact (BergnerTwoObject.hasLiftingProperty_iff F (∂Δ[n]).ι).mp
      (h _ (boundary_mem_generatingCofibrations n)) x y
  · rintro ⟨hObj, hHom⟩ A B i hi
    obtain ⟨k⟩ := hi
    cases k with
    | none => exact (BergnerObjects.hasLiftingProperty_iff F).mpr hObj
    | some n =>
      exact (BergnerTwoObject.hasLiftingProperty_iff F (∂Δ[n]).ι).mpr
        (fun x y => hHom x y _ (SSet.modelCategoryQuillen.boundary_ι_mem_I n))

/-- The right class has the expected full original empty-boundary object and scalar lifting data. -/
theorem generatingCofibrations_right_object_surjective {C D : Carrier.{u}} (F : C ⟶ D)
    (hF : generatingCofibrations.rlp F) : Function.Surjective F.obj :=
  (generatingCofibrations_rlp_iff F).mp hF |>.1

/-- The actual right class lifts EVERY original scalar boundary at EVERY original source pair. -/
theorem generatingCofibrations_right_hom_boundaries {C D : Carrier.{u}} (F : C ⟶ D)
    (hF : generatingCofibrations.rlp F) (x y : C) : SSet.modelCategoryQuillen.I.rlp (F.map x y) :=
  (generatingCofibrations_rlp_iff F).mp hF |>.2 x y

end CategoryTheory.SimplicialEnrichment.Bergner
