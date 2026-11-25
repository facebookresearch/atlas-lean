/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneSystemEndpoints
public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy

/-! # Public endpoint-lifting and strict-section consumers -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomotopicalAlgebra

universe w v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.AnodyneSystemEndpointsTest

variable {C : Type u} [Category.{v} C]
  [HasBinaryCoproducts C] [HasPushouts C] [HasInitial C] [InitialMonoClass C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]

/-- Actual endpoint squares lift against the specified right class,
retaining both equations for either endpoint. -/
theorem endpoint_square_lift (Z : C) (ε : Fin 2) {X Y : C}
    (p : X ⟶ Y) (hp : An.rlp p) (a : Z ⟶ X) (b : P.I.obj Z ⟶ Y)
    (sq : CommSq a ((P.app Z).endpoint ε) p b) :
    ∃ l : P.I.obj Z ⟶ X, (P.app Z).endpoint ε ≫ l = a ∧ l ≫ p = b := by
  have hlp : HasLiftingProperty ((P.app Z).endpoint ε) p :=
    hp _ (Precylinder.IsAnodyneSystem.endpoint_mem_anodyne P An Z ε)
  have : sq.HasLift := hlp.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- An endpoint-one lift keeps the whole supplied base homotopy and the
prescribed map; its endpoint-zero restriction is a strict section. -/
theorem strict_section_correction {X Y : C} (p : X ⟶ Y) (hp : An.rlp p)
    (t : Y ⟶ X) (K : (P.app Y).LeftHomotopy (𝟙 Y) (t ≫ p)) :
    ∃ l : P.I.obj Y ⟶ X, (P.app Y).i₁ ≫ l = t ∧ l ≫ p = K.h ∧
      ((P.app Y).i₀ ≫ l) ≫ p = 𝟙 Y := by
  have sq : CommSq t ((P.app Y).endpoint 1) p K.h := ⟨K.h₁.symm⟩
  obtain ⟨l, h₁, hover⟩ := endpoint_square_lift P An Y 1 p hp t K.h sq
  refine ⟨l, h₁, hover, ?_⟩
  simpa only [Category.assoc, hover] using K.h₀

end MathlibExtTest.AlgebraicTopology.ModelCategory.AnodyneSystemEndpointsTest
