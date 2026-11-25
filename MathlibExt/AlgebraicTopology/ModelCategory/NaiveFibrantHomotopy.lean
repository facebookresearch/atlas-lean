/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneSystem
public import MathlibExt.AlgebraicTopology.ModelCategory.CylinderHomotopyCategory
public import MathlibExt.AlgebraicTopology.ModelCategory.NaiveFibrations
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Elementary homotopy into a naive fibrant target

For a fixed exact functorial precylinder and its anodyne system, elementary
homotopy into a naive fibrant object is an equivalence relation. The proof
fills the source's common-start three-face corner and keeps the original
precylinder. Equality in its homotopy category therefore has one elementary
homotopy witness with the specified endpoints.

## References

- Cisinski, *Higher Categories and Homotopical Algebra*, Lemma 2.4.24.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder.IsAnodyneSystem

variable {C : Type u} [Category.{v} C]
  [HasBinaryCoproducts C] [HasPushouts C] [HasTerminal C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]

/-- The common-start construction uses both full homotopies and the constant face. -/
private lemma commonStart {X T : C} {f g h : X ⟶ T}
    (hT : An.naiveFibrantObjects T)
    (H : (P.app X).LeftHomotopy f g) (K : (P.app X).LeftHomotopy f h) :
    Nonempty ((P.app X).LeftHomotopy g h) := by
  let : PreservesColimitsOfSize.{0, 0} P.I :=
    preservesSmallestColimits_of_preservesColimits P.I
  let boundary : X ⨿ X ⟶ P.I.obj X := (P.app X).i
  let b : P.I.obj (X ⨿ X) ⟶ T :=
    inv (coprodComparison P.I X X) ≫ coprod.desc H.h K.h
  let a : P.I.obj X ⟶ T := (P.app X).π ≫ f
  have b₀ : P.I.map (coprod.inl : X ⟶ X ⨿ X) ≫ b = H.h := by
    simp [b, map_inl_inv_coprodComparison_assoc]
  have b₁ : P.I.map (coprod.inr : X ⟶ X ⨿ X) ≫ b = K.h := by
    simp [b, map_inr_inv_coprodComparison_assoc]
  have overlap : boundary ≫ a = (P.app (X ⨿ X)).endpoint 0 ≫ b := by
    apply coprod.hom_ext
    · calc
        coprod.inl ≫ boundary ≫ a = f := by
          simp only [boundary, a, ← Category.assoc, (P.app X).inl_i,
            (P.app X).i₀_π, Category.id_comp]
        _ = (P.app X).i₀ ≫ H.h := H.h₀.symm
        _ = (P.app X).endpoint 0 ≫ (P.I.map coprod.inl ≫ b) := by rw [b₀]; rfl
        _ = coprod.inl ≫ (P.app (X ⨿ X)).endpoint 0 ≫ b := by
          simpa only [Category.assoc] using
            congrArg (· ≫ b) (P.endpoint_naturality (coprod.inl : X ⟶ X ⨿ X) 0).symm
    · calc
        coprod.inr ≫ boundary ≫ a = f := by
          simp only [boundary, a, ← Category.assoc, (P.app X).inr_i,
            (P.app X).i₁_π, Category.id_comp]
        _ = (P.app X).i₀ ≫ K.h := K.h₀.symm
        _ = (P.app X).endpoint 0 ≫ (P.I.map coprod.inr ≫ b) := by rw [b₁]; rfl
        _ = coprod.inr ≫ (P.app (X ⨿ X)).endpoint 0 ≫ b := by
          simpa only [Category.assoc] using
            congrArg (· ≫ b) (P.endpoint_naturality (coprod.inr : X ⟶ X ⨿ X) 0).symm
  have hAn : An (P.endpointCorner boundary 0) := endpoint_corner boundary 0
  obtain ⟨F, hF⟩ := (An.naiveFibrantObjects_iff_extensions T).mp hT
    (P.endpointCorner boundary 0) hAn (pushout.desc a b overlap)
  have restriction : P.I.map boundary ≫ F = b := by
    have q := congrArg ((pushout.inr boundary ((P.app (X ⨿ X)).endpoint 0)) ≫ ·) hF
    simpa only [inr_endpointCorner_assoc, pushout.inr_desc] using q
  have F₀ : P.I.map (P.app X).i₀ ≫ F = H.h := by
    rw [← (P.app X).inl_i, Functor.map_comp, Category.assoc]
    exact (congrArg (P.I.map (coprod.inl : X ⟶ X ⨿ X) ≫ ·) restriction).trans b₀
  have F₁ : P.I.map (P.app X).i₁ ≫ F = K.h := by
    rw [← (P.app X).inr_i, Functor.map_comp, Category.assoc]
    exact (congrArg (P.I.map (coprod.inr : X ⟶ X ⨿ X) ≫ ·) restriction).trans b₁
  refine ⟨{ h := (P.app (P.I.obj X)).i₁ ≫ F, h₀ := ?_, h₁ := ?_ }⟩
  · calc
      (P.app X).i₀ ≫ ((P.app (P.I.obj X)).i₁ ≫ F) =
          (P.app X).i₁ ≫ (P.I.map (P.app X).i₀ ≫ F) := by
        simpa only [Functor.id_map, Category.assoc] using
          congrArg (· ≫ F) (P.i₁.naturality (P.app X).i₀)
      _ = g := by rw [F₀, H.h₁]
  · calc
      (P.app X).i₁ ≫ ((P.app (P.I.obj X)).i₁ ≫ F) =
          (P.app X).i₁ ≫ (P.I.map (P.app X).i₁ ≫ F) := by
        simpa only [Functor.id_map, Category.assoc] using
          congrArg (· ≫ F) (P.i₁.naturality (P.app X).i₁)
      _ = h := by rw [F₁, K.h₁]

/-- Elementary homotopy for the fixed cylinder is an equivalence relation into a naive
fibrant target, for every source object. -/
theorem equivalence_elementaryHomotopyRel {X T : C} (hT : An.naiveFibrantObjects T) :
    Equivalence (fun f g : X ⟶ T ↦ P.elementaryHomotopyRel f g) := by
  have reverse {f g : X ⟶ T} (H : (P.app X).LeftHomotopy f g) :
      Nonempty ((P.app X).LeftHomotopy g f) :=
    commonStart P An hT H (LeftHomotopy.refl (P.app X) f)
  refine ⟨fun f ↦ ⟨LeftHomotopy.refl (P.app X) f⟩, ?_, ?_⟩
  · rintro f g ⟨H⟩
    exact reverse H
  · rintro f g h ⟨H⟩ ⟨K⟩
    obtain ⟨H'⟩ := reverse H
    exact commonStart P An hT H' K

/-- Equality of classes has a single native left homotopy with the requested orientation. -/
theorem homotopyQuotientFunctor_map_eq_iff_nonempty_leftHomotopy
    {X T : C} (hT : An.naiveFibrantObjects T) (f g : X ⟶ T) :
    P.homotopyQuotientFunctor.map f = P.homotopyQuotientFunctor.map g ↔
      Nonempty ((P.app X).LeftHomotopy f g) := by
  rw [P.homotopyQuotientFunctor_map_eq_iff]
  exact (equivalence_elementaryHomotopyRel P An hT).eqvGen_iff

end HomotopicalAlgebra.Precylinder.IsAnodyneSystem
