/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CoherentIso
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# The actual walking-groupoid E-contraction

This is a map E × E → E from the constant-zero endomorphism to the
identity, constructed in every degree from the original walking groupoid.
It is E-contraction data, without a geometric-contractibility inference
or a Segal-space/power/Dwyer--Kan conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CartesianMonoidalCategory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.CategoricalEContraction

/-- The genuine functor on the original codiscrete walking-groupoid product. -/
def conjunctionFunctor : WalkingIso.{u} × WalkingIso.{u} ⥤ WalkingIso.{u} :=
  Codiscrete.functor (fun p : WalkingIso.{u} × WalkingIso.{u} =>
    ULift.up (WalkingIso.equivBool p.1 && WalkingIso.equivBool p.2))

/-- Apply the actual functor to the original pair of composable-arrow simplices. -/
def conjunctionSimplex {n : ℕ} (s t : coherentIso.{u} _⦋n⦌) : coherentIso.{u} _⦋n⦌ :=
  ((conjunctionFunctor.{u}).mapComposableArrows n).obj (s.prod' t)

/-- Every original vertex is computed by Boolean conjunction in the walking groupoid. -/
theorem conjunctionSimplex_vertexBool {n : ℕ} (s t : coherentIso.{u} _⦋n⦌)
    (i : Fin (n + 1)) :
    coherentIso.vertexBool (conjunctionSimplex s t) i =
      (coherentIso.vertexBool s i && coherentIso.vertexBool t i) := rfl

/-- The actual whole simplicial-set E-contraction, retaining both original factors. -/
def contraction : coherentIso.{u} ⊗ coherentIso.{u} ⟶ coherentIso.{u} where
  app _ := ↾fun p => conjunctionSimplex p.1 p.2
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro p
    apply coherentIso.eq_of_forall_vertexBool_eq
    intro i
    rfl

/-- The zero parameter endpoint is the original constant-zero endomorphism. -/
theorem contraction_zero :
    CartesianMonoidalCategory.lift (𝟙 coherentIso.{u}) (SSet.const coherentIso.x₀) ≫
      contraction = SSet.const coherentIso.x₀ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply coherentIso.eq_of_forall_vertexBool_eq
  intro i
  change (coherentIso.vertexBool s i && false) = false
  cases coherentIso.vertexBool s i <;> rfl

/-- The one parameter endpoint is the identity on the SAME original E. -/
theorem contraction_one :
    CartesianMonoidalCategory.lift (𝟙 coherentIso.{u}) (SSet.const coherentIso.x₁) ≫
      contraction = 𝟙 coherentIso.{u} := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply coherentIso.eq_of_forall_vertexBool_eq
  intro i
  change (coherentIso.vertexBool s i && true) = coherentIso.vertexBool s i
  cases coherentIso.vertexBool s i <;> rfl

/-- The original zero object stays fixed throughout the entire E parameter. -/
theorem contraction_zero_left :
    CartesianMonoidalCategory.lift (SSet.const coherentIso.x₀) (𝟙 coherentIso.{u}) ≫
      contraction = SSet.const coherentIso.x₀ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply coherentIso.eq_of_forall_vertexBool_eq
  intro i
  change (false && coherentIso.vertexBool s i) = false
  cases coherentIso.vertexBool s i <;> rfl

/-- Every original inner face or degeneracy commutes with the whole contraction. -/
theorem contraction_operator {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    (coherentIso.{u} ⊗ coherentIso.{u}).map α ≫ contraction.app n =
      contraction.app m ≫ coherentIso.{u}.map α :=
  contraction.naturality α

end SSet.CategoricalEContraction
