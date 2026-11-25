/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationData
public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneSystem

/-!
# Strong deformation data imply anodyneness

For a specified exact cylinder and anodyne system, a strong deformation
datum gives lifting against every naive fibration. The actual endpoint-one
corner retains the full stationary restriction, and its endpoint zero
gives the strict diagonal.

This is Cisinski, *Higher Categories and Homotopical Algebra*, July 30,
2026, Lemma 2.4.32 (printed p.62 / PDF p.78). With the source's homotopy
oriented from the identity to the retract composite, the prescribed
retract map belongs at endpoint one and the diagonal is read at endpoint
zero; the printed diagram's opposite endpoint labels are corrected here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder.StrongDeformationData

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]
variable {P : Precylinder (𝟭 C)} [P.IsExact.{w}] {An : MorphismProperty C}
variable [P.IsAnodyneSystem.{w} An] {K L : C} {i : K ⟶ L}

/-- A chosen strong deformation datum makes its map anodyne for the specified system. -/
theorem mem_anodyne (D : P.StrongDeformationData i) : An i := by
  rw [← IsAnodyneSystem.llp_rlp_eq P An]
  intro X Y p hp
  constructor
  intro a b sq
  have : Mono i := D.mono
  have overlap : i ≫ (D.retraction ≫ a) = (P.app K).endpoint 1 ≫ ((P.app K).π ≫ a) := by
    calc
      i ≫ (D.retraction ≫ a) = a := by rw [← Category.assoc, D.retract, Category.id_comp]
      _ = (P.app K).endpoint 1 ≫ ((P.app K).π ≫ a) := by
        rw [← Category.assoc, (P.app K).endpoint_π, Category.id_comp]
  let top := pushout.desc (D.retraction ≫ a) ((P.app K).π ≫ a) overlap
  let bottom := D.homotopy.h ≫ b
  have cornerSq : CommSq top (P.endpointCorner i 1) p bottom := by
    constructor
    apply pushout.hom_ext
    · rw [← Category.assoc (pushout.inl i ((P.app K).endpoint 1)) top p]
      rw [show pushout.inl i ((P.app K).endpoint 1) ≫ top = D.retraction ≫ a
        from pushout.inl_desc ..]
      rw [inl_endpointCorner_assoc]
      change (D.retraction ≫ a) ≫ p = (P.app L).i₁ ≫ (D.homotopy.h ≫ b)
      rw [D.homotopy.h₁_assoc, Category.assoc, sq.w, Category.assoc]
    · rw [← Category.assoc (pushout.inr i ((P.app K).endpoint 1)) top p]
      rw [show pushout.inr i ((P.app K).endpoint 1) ≫ top = (P.app K).π ≫ a
        from pushout.inr_desc ..]
      rw [inr_endpointCorner_assoc]
      change ((P.app K).π ≫ a) ≫ p = P.I.map i ≫ (D.homotopy.h ≫ b)
      rw [← Category.assoc (P.I.map i), D.stationary]
      rw [Category.assoc, Category.assoc, sq.w]
  have hcorner : An (P.endpointCorner i 1) := IsAnodyneSystem.endpoint_corner i 1
  have : HasLiftingProperty (P.endpointCorner i 1) p := hp _ hcorner
  have restriction : P.I.map i ≫ cornerSq.lift = (P.app K).π ≫ a := by
    have h := congrArg (pushout.inr i ((P.app K).endpoint 1) ≫ ·) cornerSq.fac_left
    simpa only [inr_endpointCorner_assoc, top, pushout.inr_desc] using h
  refine CommSq.HasLift.mk' { l := (P.app L).i₀ ≫ cornerSq.lift, fac_left := ?_, fac_right := ?_ }
  · calc
      i ≫ ((P.app L).i₀ ≫ cornerSq.lift) =
          (P.app K).i₀ ≫ (P.I.map i ≫ cornerSq.lift) := by
        simpa only [endpoint_zero, Category.assoc] using
          congrArg (· ≫ cornerSq.lift) (P.endpoint_naturality i 0)
      _ = a := by rw [restriction, ← Category.assoc, (P.app K).i₀_π, Category.id_comp]
  · rw [Category.assoc, cornerSq.fac_right]
    simp only [bottom, ← Category.assoc, D.homotopy.h₀, Category.id_comp]

end HomotopicalAlgebra.Precylinder.StrongDeformationData
