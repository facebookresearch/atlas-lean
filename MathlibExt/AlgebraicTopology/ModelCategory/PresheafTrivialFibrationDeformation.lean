/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PresheafCylinderCorners
public import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationData
public import MathlibExt.AlgebraicTopology.ModelCategory.DualDeformationData
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Trivial fibrations and every chosen section

Right lifting against every monomorphism supplies a section. In presheaves,
the actual boundary corner of any chosen section is monic for an exact
cylinder. Lifting this corner retains both homotopy endpoints, the entire
stationary restriction on the section, and the over-base equation.

This is Cisinski, *Higher Categories and Homotopical Algebra*, July 30,
2026, Proposition 2.4.17 (printed p.56 / PDF p.72). The section step needs
only an initial object with monic outgoing maps. No model or fibrancy
condition is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v' v u

namespace CategoryTheory.MorphismProperty

/-- RLP against all monomorphisms supplies a section, using the initial square. -/
theorem exists_splitEpi_of_rlp_monomorphisms {C : Type u} [Category.{v} C]
    [HasInitial C] [InitialMonoClass C] {X Y : C} (p : X ⟶ Y)
    (hp : (monomorphisms C).rlp p) : Nonempty (SplitEpi p) := by
  have : HasLiftingProperty (initial.to Y) p := hp _ (by infer_instance)
  have sq : CommSq (initial.to X) (initial.to Y) p (𝟙 Y) := ⟨initial.hom_ext _ _⟩
  exact ⟨{ section_ := sq.lift, id := sq.fac_right }⟩

end CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.Precylinder

variable {A : Type v} [Category.{v'} A]
variable (P : Precylinder (𝟭 (Aᵒᵖ ⥤ Type u))) [P.IsExact.{w}]
variable {X Y : Aᵒᵖ ⥤ Type u}

/-- Every chosen section of a trivial fibration has strong deformation data
with the specified retraction; the same homotopy lies over the base. -/
theorem exists_strongDeformationData_of_section (p : X ⟶ Y)
    (hp : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type u)).rlp p)
    (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) :
    ∃ D : P.StrongDeformationData s,
      D.retraction = p ∧ D.homotopy.h ≫ p = (P.app X).π ≫ p := by
  have : Mono s := (SplitEpi.splitMono (⟨s, hs⟩ : SplitEpi p)).mono
  have overlap : coprod.map s s ≫ coprod.desc (𝟙 X) (p ≫ s) =
      (P.app Y).i ≫ ((P.app Y).π ≫ s) := by
    apply coprod.hom_ext
    · calc
        coprod.inl ≫ (coprod.map s s ≫ coprod.desc (𝟙 X) (p ≫ s)) = s := by
          rw [coprod.inl_map_assoc, coprod.inl_desc, Category.comp_id]
        _ = coprod.inl ≫ ((P.app Y).i ≫ ((P.app Y).π ≫ s)) := by
          rw [← Category.assoc, (P.app Y).inl_i, ← Category.assoc,
            (P.app Y).i₀_π, Category.id_comp]
    · calc
        coprod.inr ≫ (coprod.map s s ≫ coprod.desc (𝟙 X) (p ≫ s)) = s := by
          rw [coprod.inr_map_assoc, coprod.inr_desc, ← Category.assoc, hs, Category.id_comp]
        _ = coprod.inr ≫ ((P.app Y).i ≫ ((P.app Y).π ≫ s)) := by
          rw [← Category.assoc, (P.app Y).inr_i, ← Category.assoc,
            (P.app Y).i₁_π, Category.id_comp]
  let top := pushout.desc (coprod.desc (𝟙 X) (p ≫ s)) ((P.app Y).π ≫ s) overlap
  let bottom := (P.app X).π ≫ p
  have sq : CommSq top (P.boundaryCorner s) p bottom := by
    constructor
    apply pushout.hom_ext
    · rw [← Category.assoc (pushout.inl (coprod.map s s) (P.app Y).i) top p]
      rw [show pushout.inl (coprod.map s s) (P.app Y).i ≫ top =
        coprod.desc (𝟙 X) (p ≫ s) from pushout.inl_desc ..]
      rw [inl_boundaryCorner_assoc]
      apply coprod.hom_ext
      · calc
          coprod.inl ≫ (coprod.desc (𝟙 X) (p ≫ s) ≫ p) = p := by
            rw [coprod.inl_desc_assoc, Category.id_comp]
          _ = coprod.inl ≫ ((P.app X).i ≫ bottom) := by
            dsimp only [bottom]
            rw [← Category.assoc, (P.app X).inl_i, ← Category.assoc,
              (P.app X).i₀_π, Category.id_comp]
      · calc
          coprod.inr ≫ (coprod.desc (𝟙 X) (p ≫ s) ≫ p) = p := by
            rw [coprod.inr_desc_assoc, Category.assoc, hs, Category.comp_id]
          _ = coprod.inr ≫ ((P.app X).i ≫ bottom) := by
            dsimp only [bottom]
            rw [← Category.assoc, (P.app X).inr_i, ← Category.assoc,
              (P.app X).i₁_π, Category.id_comp]
    · rw [← Category.assoc (pushout.inr (coprod.map s s) (P.app Y).i) top p]
      rw [show pushout.inr (coprod.map s s) (P.app Y).i ≫ top =
        (P.app Y).π ≫ s from pushout.inr_desc ..]
      rw [inr_boundaryCorner_assoc]
      change ((P.app Y).π ≫ s) ≫ p = P.I.map s ≫ ((P.app X).π ≫ p)
      simpa only [Functor.id_map, Category.assoc] using
        congrArg (· ≫ p) (P.π.naturality s).symm
  have : HasLiftingProperty (P.boundaryCorner s) p := hp _ (by infer_instance)
  have boundary_eq : (P.app X).i ≫ sq.lift = coprod.desc (𝟙 X) (p ≫ s) := by
    have h := congrArg (pushout.inl (coprod.map s s) (P.app Y).i ≫ ·) sq.fac_left
    simpa only [inl_boundaryCorner_assoc, top, pushout.inl_desc] using h
  have stationary : P.I.map s ≫ sq.lift = (P.app Y).π ≫ s := by
    have h := congrArg (pushout.inr (coprod.map s s) (P.app Y).i ≫ ·) sq.fac_left
    simpa only [inr_boundaryCorner_assoc, top, pushout.inr_desc] using h
  refine ⟨{ retraction := p, retract := hs, homotopy :=
    { h := sq.lift, h₀ := ?_, h₁ := ?_, stationary := ?_ } }, rfl, sq.fac_right⟩
  · have h := congrArg ((coprod.inl : X ⟶ X ⨿ X) ≫ ·) boundary_eq
    simpa only [← Category.assoc, (P.app X).inl_i, coprod.inl_desc] using h
  · have h := congrArg ((coprod.inr : X ⟶ X ⨿ X) ≫ ·) boundary_eq
    simpa only [← Category.assoc, (P.app X).inr_i, coprod.inr_desc] using h
  · simpa only [Category.comp_id] using stationary

/-- A trivial fibration has dual deformation data, using the chosen-section
construction and the same stationary homotopy. -/
theorem exists_dualDeformationData_of_rlp_monomorphisms (p : X ⟶ Y)
    (hp : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type u)).rlp p) :
    Nonempty (P.DualDeformationData p) := by
  obtain ⟨E⟩ := MorphismProperty.exists_splitEpi_of_rlp_monomorphisms p hp
  obtain ⟨D, hret, hover⟩ := P.exists_strongDeformationData_of_section p hp E.section_ E.id
  exact ⟨{
    section_ := E.section_
    section_comp := E.id
    homotopy := {
      h := D.homotopy.h
      h₀ := D.homotopy.h₀
      h₁ := by simpa only [hret] using D.homotopy.h₁ }
    over_base := hover }⟩

end HomotopicalAlgebra.Precylinder
