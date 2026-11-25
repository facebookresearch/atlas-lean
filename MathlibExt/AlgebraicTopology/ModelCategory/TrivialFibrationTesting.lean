/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PresheafTrivialFibrationDeformation
public import MathlibExt.AlgebraicTopology.ModelCategory.CylinderHomotopyYoneda

/-!
# Trivial fibrations are homotopy testing equivalences

Dual deformation data give an inverse in the actual chosen-cylinder
quotient. In a category with monic initial maps and an exact cylinder,
right lifting against all monomorphisms supplies these data by lifting
the pointwise cylinder boundary. This does not require the stronger
presheaf homotopy stationary on a chosen section.

The resulting inclusion in the testing class is the consequence of
Cisinski, *Higher Categories and Homotopical Algebra*, July 30, 2026,
Proposition 2.4.17 and Remark 2.4.21, with the stated generic extension.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder

section Inverse

variable {C : Type u} [Category.{v} C] {P : Precylinder (𝟭 C)} {X Y : C} {p : X ⟶ Y}

/-- The section and two endpoint equations give an actual inverse in the
chosen-cylinder quotient. No fibrancy or model hypothesis is needed. -/
theorem DualDeformationData.mem_homotopyEquivalences (D : P.DualDeformationData p) :
    P.homotopyEquivalences p := by
  rw [P.homotopyEquivalences_iff]
  refine ⟨P.homotopyQuotientFunctor.map D.section_, ?_, ?_⟩
  · have h := (P.homotopyQuotientFunctor_map_eq D.homotopy).symm
    simpa only [P.homotopyQuotientFunctor.map_comp, P.homotopyQuotientFunctor.map_id] using h
  · rw [← P.homotopyQuotientFunctor.map_comp, D.section_comp,
      P.homotopyQuotientFunctor.map_id]

end Inverse

section Boundary

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
  [HasInitial C] [InitialMonoClass C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}] {X Y : C}

/-- The initial square and monic pointwise boundary give dual deformation
data in any category with these properties. Section stationarity is not asserted. -/
theorem nonempty_dualDeformationData_of_rlp_monomorphisms (p : X ⟶ Y)
    (hp : (MorphismProperty.monomorphisms C).rlp p) :
    Nonempty (P.DualDeformationData p) := by
  obtain ⟨E⟩ := MorphismProperty.exists_splitEpi_of_rlp_monomorphisms p hp
  let top := coprod.desc (𝟙 X) (p ≫ E.section_)
  have sq : CommSq top (P.app X).i p ((P.app X).π ≫ p) := by
    constructor
    apply coprod.hom_ext
    · calc
        coprod.inl ≫ (top ≫ p) = p := by
          simp only [top, coprod.inl_desc_assoc, Category.id_comp]
        _ = coprod.inl ≫ ((P.app X).i ≫ ((P.app X).π ≫ p)) := by
          rw [← Category.assoc, (P.app X).inl_i, ← Category.assoc,
            (P.app X).i₀_π, Category.id_comp]
    · calc
        coprod.inr ≫ (top ≫ p) = (p ≫ E.section_) ≫ p := by
          simp only [top, coprod.inr_desc_assoc]
        _ = p := by rw [Category.assoc, E.id, Category.comp_id]
        _ = coprod.inr ≫ ((P.app X).i ≫ ((P.app X).π ≫ p)) := by
          rw [← Category.assoc, (P.app X).inr_i, ← Category.assoc,
            (P.app X).i₁_π, Category.id_comp]
  have : HasLiftingProperty (P.app X).i p := hp _ (by infer_instance)
  refine ⟨{
    section_ := E.section_
    section_comp := E.id
    homotopy := { h := sq.lift, h₀ := ?_, h₁ := ?_ }
    over_base := sq.fac_right }⟩
  · have h := congrArg ((coprod.inl : X ⟶ X ⨿ X) ≫ ·) sq.fac_left
    simpa only [← Category.assoc, (P.app X).inl_i, top, coprod.inl_desc] using h
  · have h := congrArg ((coprod.inr : X ⟶ X ⨿ X) ≫ ·) sq.fac_left
    simpa only [← Category.assoc, (P.app X).inr_i, top, coprod.inr_desc] using h

/-- All-monomorphism right lifting implies testing equivalence for any
specified naive target predicate, without source or target fibrancy. -/
theorem rlp_monomorphisms_le_testingEquivalences [HasTerminal C]
    (An : MorphismProperty C) :
    (MorphismProperty.monomorphisms C).rlp ≤ P.testingEquivalences An := by
  intro X Y p hp
  obtain ⟨D⟩ := P.nonempty_dualDeformationData_of_rlp_monomorphisms p hp
  exact P.homotopyEquivalences_le_testingEquivalences An p D.mem_homotopyEquivalences

end Boundary

end HomotopicalAlgebra.Precylinder
