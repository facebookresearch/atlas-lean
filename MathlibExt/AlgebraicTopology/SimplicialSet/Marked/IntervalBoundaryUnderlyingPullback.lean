/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntervalCylinderExact
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The actual underlying whole boundary square is a pullback

Forgetting preserves the original marked coproduct and endpoint pullbacks.
Universality of coproducts in the original simplicial presheaf category
then combines these two endpoint squares into its whole boundary square.
No extensivity or adhesivity of the marked category is assumed, and both
original marked coproduct maps remain in the statement.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra

namespace SSet.Marked

/-- The original marked cylinder boundary naturality square is a genuine underlying simplicial pullback. -/
theorem intervalCylinder_boundary_underlying_isPullback {X Y : Marked.{u}} (f : X ⟶ Y) :
    IsPullback (coprod.map f f).hom (intervalCylinder.app X).i.hom (intervalCylinder.app Y).i.hom
      (intervalCylinder.I.map f).hom := by
  let _ : PreservesColimitsOfSize.{u, u} forget.{u} := forgetPreservesColimits
  let _ : PreservesLimitsOfSize.{u, u} forget.{u} := forgetPreservesLimits
  let a : Cofan (pairFunction Y.toSSet Y.toSSet) :=
    BinaryCofan.mk (coprod.inl : Y ⟶ Y ⨿ Y).hom (coprod.inr : Y ⟶ Y ⨿ Y).hom
  let d : Cofan (pairFunction X.toSSet X.toSSet) :=
    BinaryCofan.mk (coprod.inl : X ⟶ X ⨿ X).hom (coprod.inr : X ⟶ X ⨿ X).hom
  have ha : IsColimit a := isColimitOfHasBinaryCoproductOfPreservesColimit forget Y Y
  have hd : IsColimit d := isColimitOfHasBinaryCoproductOfPreservesColimit forget X X
  let esY : ∀ j, pairFunction Y.toSSet Y.toSSet j ⟶ (intervalCylinder.I.obj Y).toSSet
    | .left => (intervalCylinderEndpoint Y 0).hom
    | .right => (intervalCylinderEndpoint Y 1).hom
  let esX : ∀ j, pairFunction X.toSSet X.toSSet j ⟶ (intervalCylinder.I.obj X).toSSet
    | .left => (intervalCylinderEndpoint X 0).hom
    | .right => (intervalCylinderEndpoint X 1).hom
  let fs : ∀ j, pairFunction X.toSSet X.toSSet j ⟶ pairFunction Y.toSSet Y.toSSet j
    | .left => f.hom
    | .right => f.hom
  have hq : ∀ j, IsPullback (esX j) (fs j) (intervalCylinder.I.map f).hom (esY j) := by
    intro j
    cases j
    · exact ((intervalCylinderEndpoint_isPullback f 0).map forget).flip
    · exact ((intervalCylinderEndpoint_isPullback f 1).map forget).flip
  have hu : ∀ j, a.inj j ≫ (intervalCylinder.app Y).i.hom = esY j := by
    intro j
    cases j
    · exact congrArg Hom.hom (intervalCylinder.app Y).inl_i
    · exact congrArg Hom.hom (intervalCylinder.app Y).inr_i
  have h₁ : Cofan.IsColimit.desc hd esX = (intervalCylinder.app X).i.hom := by
    apply hd.hom_ext
    rintro ⟨j⟩
    cases j
    · change d.inj .left ≫ _ = d.inj .left ≫ (intervalCylinder.app X).i.hom
      rw [Cofan.IsColimit.fac]
      exact (congrArg Hom.hom (intervalCylinder.app X).inl_i).symm
    · change d.inj .right ≫ _ = d.inj .right ≫ (intervalCylinder.app X).i.hom
      rw [Cofan.IsColimit.fac]
      exact (congrArg Hom.hom (intervalCylinder.app X).inr_i).symm
  have h₂ : Cofan.IsColimit.desc hd (fun j => fs j ≫ a.inj j) = (coprod.map f f).hom := by
    apply hd.hom_ext
    rintro ⟨j⟩
    cases j
    · change d.inj .left ≫ _ = d.inj .left ≫ (coprod.map f f).hom
      rw [Cofan.IsColimit.fac]
      exact (congrArg Hom.hom (coprod.inl_map f f)).symm
    · change d.inj .right ≫ _ = d.inj .right ≫ (coprod.map f f).hom
      rw [Cofan.IsColimit.fac]
      exact (congrArg Hom.hom (coprod.inr_map f f)).symm
  have hp := (FinitaryPreExtensive.universal' a ha).isPullback_of_isColimit_left
    esY (intervalCylinder.app Y).i.hom (intervalCylinder.I.map f).hom esX fs hq hd hu
  rw [h₁, h₂] at hp
  exact hp.flip

end SSet.Marked
