/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneSystem
public import MathlibExt.AlgebraicTopology.ModelCategory.TrivialFibrationTesting

/-!
# Naive fibrations with dual deformation data

For an exact functorial cylinder and its specified anodyne system, a naive
fibration with dual deformation data lifts against every monomorphism.
The actual endpoint-one corner retains the full homotopy over the base;
endpoint zero gives both strict diagonal equations.

With monic initial maps, the generic pointwise-boundary construction gives
the converse. Neither direction needs a terminal object or fibrancy of the
codomain. This is Cisinski, *Higher Categories and Homotopical Algebra*,
July 30, 2026, Lemma 2.4.27 (printed pp.59–60 / PDF pp.75–76), with the
stated generic extension. The stronger presheaf construction stationary
on every chosen section remains a separate result.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] [HasPushouts C]

namespace DualDeformationData

variable {P : Precylinder (𝟭 C)} [P.IsExact.{w}] {An : MorphismProperty C}
variable [P.IsAnodyneSystem.{w} An] {X Y : C} {p : X ⟶ Y}

/-- Dual data and actual naive lifting give right lifting against every
monomorphism, without any object-fibrancy or initial-object premise. -/
theorem mem_rlp_monomorphisms (D : P.DualDeformationData p) (hp : An.rlp p) :
    (MorphismProperty.monomorphisms C).rlp p := by
  intro A B i hi
  have : Mono i := hi
  constructor
  intro a b sq
  have overlap : i ≫ (b ≫ D.section_) =
      (P.app A).endpoint 1 ≫ (P.I.map a ≫ D.homotopy.h) := by
    calc
      i ≫ (b ≫ D.section_) = a ≫ (p ≫ D.section_) := by
        rw [← Category.assoc, ← sq.w, Category.assoc]
      _ = a ≫ ((P.app X).endpoint 1 ≫ D.homotopy.h) := by
        rw [endpoint_one, D.homotopy.h₁]
      _ = (P.app A).endpoint 1 ≫ (P.I.map a ≫ D.homotopy.h) := by
        simpa only [Category.assoc] using
          congrArg (· ≫ D.homotopy.h) (P.endpoint_naturality a 1)
  let top := pushout.desc (b ≫ D.section_) (P.I.map a ≫ D.homotopy.h) overlap
  let bottom := (P.app B).π ≫ b
  have cornerSq : CommSq top (P.endpointCorner i 1) p bottom := by
    constructor
    apply pushout.hom_ext
    · rw [← Category.assoc (pushout.inl i ((P.app A).endpoint 1)) top p]
      rw [show pushout.inl i ((P.app A).endpoint 1) ≫ top = b ≫ D.section_
        from pushout.inl_desc ..]
      rw [inl_endpointCorner_assoc]
      change (b ≫ D.section_) ≫ p = (P.app B).i₁ ≫ ((P.app B).π ≫ b)
      rw [Category.assoc, D.section_comp, Category.comp_id, ← Category.assoc,
        (P.app B).i₁_π, Category.id_comp]
    · rw [← Category.assoc (pushout.inr i ((P.app A).endpoint 1)) top p]
      rw [show pushout.inr i ((P.app A).endpoint 1) ≫ top = P.I.map a ≫ D.homotopy.h
        from pushout.inr_desc ..]
      rw [inr_endpointCorner_assoc]
      change (P.I.map a ≫ D.homotopy.h) ≫ p = P.I.map i ≫ ((P.app B).π ≫ b)
      calc
        (P.I.map a ≫ D.homotopy.h) ≫ p = P.I.map a ≫ ((P.app X).π ≫ p) := by
          rw [Category.assoc, D.over_base]
        _ = ((P.app A).π ≫ a) ≫ p := by
          simpa only [Functor.id_map, Category.assoc] using
            congrArg (· ≫ p) (P.π.naturality a)
        _ = (P.app A).π ≫ (i ≫ b) := by rw [Category.assoc, sq.w]
        _ = P.I.map i ≫ ((P.app B).π ≫ b) := by
          simpa only [Functor.id_map, Category.assoc] using
            congrArg (· ≫ b) (P.π.naturality i).symm
  have hcorner : An (P.endpointCorner i 1) := IsAnodyneSystem.endpoint_corner i 1
  have : HasLiftingProperty (P.endpointCorner i 1) p := hp _ hcorner
  have restriction : P.I.map i ≫ cornerSq.lift = P.I.map a ≫ D.homotopy.h := by
    have h := congrArg (pushout.inr i ((P.app A).endpoint 1) ≫ ·) cornerSq.fac_left
    simpa only [inr_endpointCorner_assoc, top, pushout.inr_desc] using h
  refine CommSq.HasLift.mk'
    { l := (P.app B).i₀ ≫ cornerSq.lift, fac_left := ?_, fac_right := ?_ }
  · calc
      i ≫ ((P.app B).i₀ ≫ cornerSq.lift) =
          (P.app A).i₀ ≫ (P.I.map i ≫ cornerSq.lift) := by
        simpa only [endpoint_zero, Category.assoc] using
          congrArg (· ≫ cornerSq.lift) (P.endpoint_naturality i 0)
      _ = (P.app A).i₀ ≫ (P.I.map a ≫ D.homotopy.h) := by rw [restriction]
      _ = a ≫ ((P.app X).i₀ ≫ D.homotopy.h) := by
        simpa only [endpoint_zero, Category.assoc] using
          (congrArg (· ≫ D.homotopy.h) (P.endpoint_naturality a 0)).symm
      _ = a := by rw [D.homotopy.h₀, Category.comp_id]
  · rw [Category.assoc, cornerSq.fac_right]
    simp only [bottom, ← Category.assoc, (P.app B).i₀_π, Category.id_comp]

end DualDeformationData

namespace IsAnodyneSystem

/-- A naive fibration is trivial exactly when it has actual dual deformation
data. The codomain is arbitrary; a terminal object is not required. -/
theorem naiveFibration_mem_rlp_monomorphisms_iff_nonempty_dualDeformationData
    [HasInitial C] [InitialMonoClass C] (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
    (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An] {X Y : C} (p : X ⟶ Y)
    (hp : An.naiveFibrations p) :
    (MorphismProperty.monomorphisms C).rlp p ↔ Nonempty (P.DualDeformationData p) := by
  constructor
  · exact P.nonempty_dualDeformationData_of_rlp_monomorphisms p
  · rintro ⟨D⟩
    exact D.mem_rlp_monomorphisms hp

end IsAnodyneSystem

end HomotopicalAlgebra.Precylinder
