/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Basic
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Fibration
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Degenerate
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Actual marked Cartesian and cocartesian fibrations over a base

The marking consists precisely of the actual relative Cartesian or
cocartesian edges. Over a quasicategory, the proven degenerate-edge law
makes this a genuine marked simplicial set. The full subcategories of
marked objects over the maximally marked base retain the original maps,
their strict base equation, and preservation of the relevant edge class.
No marked model structure or straightening equivalence is asserted.
-/

noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

variable {X B : SSet.{u}}

/-- The original total space marked by precisely its p-cartesian edges. -/
def cartesian (p : X ⟶ B) [InnerFibration p] [Quasicategory B] : Marked.{u} where
  toSSet := X
  marking := {e | CartesianEdge.IsPCartesian p (yonedaEquiv.symm e)}
  degenerate_mem := CartesianEdge.isPCartesian_degenerate p

/-- The original total space marked by precisely its p-cocartesian edges. -/
def cocartesian (p : X ⟶ B) [InnerFibration p] [Quasicategory B] : Marked.{u} where
  toSSet := X
  marking := {e | CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm e)}
  degenerate_mem := CocartesianEdge.isPCocartesian_degenerate p

/-- The original Cartesian projection as a map of genuinely marked carriers. -/
def cartesianProjection (p : X ⟶ B) [InnerFibration p] [Quasicategory B] :
    cartesian p ⟶ max B := toMax p

/-- The original cocartesian projection as a map of genuinely marked carriers. -/
def cocartesianProjection (p : X ⟶ B) [InnerFibration p] [Quasicategory B] :
    cocartesian p ⟶ max B := toMax p

/-- Actual Cartesian fibrations with exactly the Cartesian marking over this base. -/
def cartesianObjects (B : SSet.{u}) : ObjectProperty (Over (max B)) := fun X =>
  CartesianFibration X.hom.hom ∧
    ∀ e : X.left.toSSet _⦋1⦌,
      e ∈ X.left.marking ↔ CartesianEdge.IsPCartesian X.hom.hom (yonedaEquiv.symm e)

/-- Actual cocartesian fibrations with exactly the cocartesian marking over this base. -/
def cocartesianObjects (B : SSet.{u}) : ObjectProperty (Over (max B)) := fun X =>
  CocartesianFibration X.hom.hom ∧
    ∀ e : X.left.toSSet _⦋1⦌,
      e ∈ X.left.marking ↔ CocartesianEdge.IsPCocartesian X.hom.hom (yonedaEquiv.symm e)

/-- The genuine category of marked Cartesian fibrations and Cartesian-edge preserving maps. -/
abbrev CartesianOver (B : SSet.{u}) := (cartesianObjects B).FullSubcategory

/-- The genuine category of marked cocartesian fibrations and edge-preserving maps. -/
abbrev CocartesianOver (B : SSet.{u}) := (cocartesianObjects B).FullSubcategory

/-- Bundle the supplied Cartesian fibration using its original projection and exact marking. -/
def ofCartesian (p : X ⟶ B) [CartesianFibration p] [Quasicategory B] : CartesianOver B where
  obj := Over.mk (cartesianProjection p)
  property := ⟨inferInstanceAs (CartesianFibration p), fun _ => Iff.rfl⟩

/-- Bundle the supplied cocartesian fibration with the same original map and exact marking. -/
def ofCocartesian (p : X ⟶ B) [CocartesianFibration p] [Quasicategory B] : CocartesianOver B where
  obj := Over.mk (cocartesianProjection p)
  property := ⟨inferInstanceAs (CocartesianFibration p), fun _ => Iff.rfl⟩

/-- Forget the Cartesian marking and fibration property, retaining each original simplicial map. -/
def CartesianOver.forget (B : SSet.{u}) : CartesianOver B ⥤ SSet.{u} :=
  (cartesianObjects B).ι ⋙ Over.forget (max B) ⋙ Marked.forget

/-- Forget the cocartesian marking and property while retaining the original maps. -/
def CocartesianOver.forget (B : SSet.{u}) : CocartesianOver B ⥤ SSet.{u} :=
  (cocartesianObjects B).ι ⋙ Over.forget (max B) ⋙ Marked.forget

/-- Forgetting a Cartesian morphism keeps exactly its original underlying map. -/
@[simp] theorem CartesianOver.forget_map {B : SSet.{u}} {X Y : CartesianOver B} (f : X ⟶ Y) :
    (CartesianOver.forget B).map f = f.hom.left.hom := rfl

/-- Forgetting a cocartesian morphism keeps exactly its original underlying map. -/
@[simp] theorem CocartesianOver.forget_map {B : SSet.{u}} {X Y : CocartesianOver B} (f : X ⟶ Y) :
    (CocartesianOver.forget B).map f = f.hom.left.hom := rfl

/-- A Cartesian morphism retains its literal whole base equation. -/
theorem CartesianOver.map_over {B : SSet.{u}} {X Y : CartesianOver B} (f : X ⟶ Y) :
    (CartesianOver.forget B).map f ≫ Y.obj.hom.hom = X.obj.hom.hom :=
  congrArg Hom.hom (Over.w f.hom)

/-- A cocartesian morphism retains its literal whole base equation. -/
theorem CocartesianOver.map_over {B : SSet.{u}} {X Y : CocartesianOver B} (f : X ⟶ Y) :
    (CocartesianOver.forget B).map f ≫ Y.obj.hom.hom = X.obj.hom.hom :=
  congrArg Hom.hom (Over.w f.hom)

/-- The original underlying map of a Cartesian morphism preserves actual Cartesian edges. -/
theorem CartesianOver.map_cartesian {B : SSet.{u}} {X Y : CartesianOver B} (f : X ⟶ Y)
    (e : (Δ[1] : SSet.{u}) ⟶ X.obj.left.toSSet)
    (he : CartesianEdge.IsPCartesian X.obj.hom.hom e) :
    CartesianEdge.IsPCartesian Y.obj.hom.hom (e ≫ (CartesianOver.forget B).map f) := by
  rw [CartesianOver.forget_map]
  have hx : yonedaEquiv e ∈ X.obj.left.marking :=
    (X.property.2 _).mpr (by simpa only [Equiv.symm_apply_apply] using he)
  have hy := f.hom.left.preserve hx
  have ht := (Y.property.2 _).mp hy
  simpa only [← yonedaEquiv_comp, Equiv.symm_apply_apply] using ht

/-- The original underlying map of a cocartesian morphism preserves actual cocartesian edges. -/
theorem CocartesianOver.map_cocartesian {B : SSet.{u}} {X Y : CocartesianOver B} (f : X ⟶ Y)
    (e : (Δ[1] : SSet.{u}) ⟶ X.obj.left.toSSet)
    (he : CocartesianEdge.IsPCocartesian X.obj.hom.hom e) :
    CocartesianEdge.IsPCocartesian Y.obj.hom.hom (e ≫ (CocartesianOver.forget B).map f) := by
  rw [CocartesianOver.forget_map]
  have hx : yonedaEquiv e ∈ X.obj.left.marking :=
    (X.property.2 _).mpr (by simpa only [Equiv.symm_apply_apply] using he)
  have hy := f.hom.left.preserve hx
  have ht := (Y.property.2 _).mp hy
  simpa only [← yonedaEquiv_comp, Equiv.symm_apply_apply] using ht

end SSet.Marked
