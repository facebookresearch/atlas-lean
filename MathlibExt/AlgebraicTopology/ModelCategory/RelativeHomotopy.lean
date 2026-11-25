/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialCylinder
public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy

/-!
# Homotopies stationary on a specified map

For a chosen functorial precylinder, a relative homotopy retains the native
left homotopy and its stationarity equation. Restriction along the specified
map is constant throughout the cylinder. The endpoint restrictions therefore
agree. Restriction to a smaller source and postcomposition preserve this data.

The definition applies to any specified map. Its use for monomorphisms and an
exact cylinder gives the relative homotopies used in Cisinski's deformation
retract equations (Definition 2.4.16); ordinary homotopies are Definition 2.4.14.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe v u

namespace HomotopicalAlgebra.Precylinder

variable {C : Type u} [Category.{v} C]
variable (P : Precylinder (𝟭 C)) {S T X Y Z : C}

/-- Restrict a native left homotopy using the chosen functorial cylinder. -/
def precompLeftHomotopy {f₀ f₁ : X ⟶ Y}
    (H : (P.app X).LeftHomotopy f₀ f₁) (i : S ⟶ X) :
    (P.app S).LeftHomotopy (i ≫ f₀) (i ≫ f₁) where
  h := P.I.map i ≫ H.h
  h₀ := by
    calc
      (P.app S).i₀ ≫ (P.I.map i ≫ H.h) =
          i ≫ ((P.app X).i₀ ≫ H.h) := by
        simpa only [Functor.id_map, Category.assoc] using
          congrArg (fun k ↦ k ≫ H.h) (P.i₀.naturality i).symm
      _ = i ≫ f₀ := by rw [H.h₀]
  h₁ := by
    calc
      (P.app S).i₁ ≫ (P.I.map i ≫ H.h) =
          i ≫ ((P.app X).i₁ ≫ H.h) := by
        simpa only [Functor.id_map, Category.assoc] using
          congrArg (fun k ↦ k ≫ H.h) (P.i₁.naturality i).symm
      _ = i ≫ f₁ := by rw [H.h₁]

/-- A native left homotopy whose restriction along `i` is the constant
cylinder map. This equation retains stationarity on the whole cylinder. -/
structure RelativeLeftHomotopy (i : S ⟶ X) (f₀ f₁ : X ⟶ Y)
    extends (P.app X).LeftHomotopy f₀ f₁ where
  stationary : P.I.map i ≫ h = (P.app S).π ≫ i ≫ f₀

namespace RelativeLeftHomotopy

variable {P} {i : S ⟶ X} {f₀ f₁ : X ⟶ Y}

/-- Stationarity implies that the two endpoint restrictions agree. -/
lemma restrictions_eq (H : P.RelativeLeftHomotopy i f₀ f₁) :
    i ≫ f₀ = i ≫ f₁ := by
  have h₁ := (P.precompLeftHomotopy H.toLeftHomotopy i).h₁
  change (P.app S).i₁ ≫ (P.I.map i ≫ H.h) = i ≫ f₁ at h₁
  rw [H.stationary] at h₁
  simpa only [← Category.assoc, (P.app S).i₁_π, Category.id_comp] using h₁

/-- The stationarity equation can use either endpoint restriction. -/
lemma stationary_right (H : P.RelativeLeftHomotopy i f₀ f₁) :
    P.I.map i ≫ H.h = (P.app S).π ≫ i ≫ f₁ := by
  rw [H.stationary, H.restrictions_eq]

/-- The constant native homotopy is stationary along any specified map. -/
def refl (i : S ⟶ X) (f : X ⟶ Y) :
    P.RelativeLeftHomotopy i f f where
  toLeftHomotopy := LeftHomotopy.refl (P.app X) f
  stationary := by
    change P.I.map i ≫ ((P.app X).π ≫ f) = (P.app S).π ≫ i ≫ f
    simpa only [Functor.id_map, Category.assoc] using
      congrArg (fun k ↦ k ≫ f) (P.π.naturality i)

/-- Postcomposition preserves the full stationarity equation. -/
def postcomp (H : P.RelativeLeftHomotopy i f₀ f₁) (p : Y ⟶ Z) :
    P.RelativeLeftHomotopy i (f₀ ≫ p) (f₁ ≫ p) where
  toLeftHomotopy := H.toLeftHomotopy.postcomp p
  stationary := by
    change P.I.map i ≫ (H.h ≫ p) = (P.app S).π ≫ i ≫ (f₀ ≫ p)
    rw [← Category.assoc, H.stationary]
    simp only [Category.assoc]

/-- A homotopy stationary along `i` is stationary along every `k ≫ i`. -/
def precomp (H : P.RelativeLeftHomotopy i f₀ f₁) (k : T ⟶ S) :
    P.RelativeLeftHomotopy (k ≫ i) f₀ f₁ where
  toLeftHomotopy := H.toLeftHomotopy
  stationary := by
    calc
      P.I.map (k ≫ i) ≫ H.h = P.I.map k ≫ (P.I.map i ≫ H.h) := by
        rw [Functor.map_comp, Category.assoc]
      _ = P.I.map k ≫ ((P.app S).π ≫ i ≫ f₀) := by rw [H.stationary]
      _ = (P.app T).π ≫ (k ≫ i) ≫ f₀ := by
        simpa only [Functor.id_map, Category.assoc] using
          congrArg (fun q ↦ q ≫ i ≫ f₀) (P.π.naturality k)

end RelativeLeftHomotopy

end HomotopicalAlgebra.Precylinder
