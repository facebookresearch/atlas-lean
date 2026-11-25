/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenHomotopyAdjunction

/-!
# Original right-adjoint maps on genuine model right classes

A Quillen right adjoint maps actual good path objects using fibrant
Brown preservation. Its map on the original right classes consequently
retains every ordinary original map, and commutes with the original
adjunction transpose. No localized or Quillen equivalence is assumed.
-/

noncomputable section
universe u₁ u₂ v₁ v₂
open CategoryTheory HomotopicalAlgebra

namespace CategoryTheory.Adjunction.IsQuillenAdjunction

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R} [IsQuillenAdjunction adj]

include adj

/-- Actual fibrant Brown preservation maps every original right homotopy into a fibrant target
through the SAME right
adjoint. -/
theorem rightHomotopyRel_map {F G : D} [IsFibrant G] {f g : F ⟶ G}
    (h : RightHomotopyRel f g) : RightHomotopyRel (R.map f) (R.map g) := by
  obtain ⟨P, hP, ⟨h⟩⟩ := h.exists_good_pathObject
  let _ : P.IsGood := hP
  let _ : IsFibrant P.P := inferInstance
  let Q : PathObject (R.obj G) :=
    { __ := P.toPrepathObject.map R
      weakEquivalence_ι := map_weakEquivalence_of_fibrant (adj := adj) P.ι }
  refine ⟨Q, ⟨{ h := R.map h.h, h₀ := ?_, h₁ := ?_ }⟩⟩
  · exact (R.map_comp _ _).symm.trans (congrArg R.map h.h₀)
  · exact (R.map_comp _ _).symm.trans (congrArg R.map h.h₁)

/-- The SAME original right-adjoint Hom map descends to actual model right-homotopy classes at
fibrant targets. -/
def rightHomotopyClassMap {F G : D} [IsFibrant G] :
    RightHomotopyClass F G → RightHomotopyClass (R.obj F) (R.obj G) :=
  Quot.map R.map (fun _ _ h => rightHomotopyRel_map (adj := adj) h)

/-- Every original representative remains the SAME original ordinary right-adjoint map. -/
theorem rightHomotopyClassMap_mk {F G : D} [IsFibrant G] (f : F ⟶ G) :
    rightHomotopyClassMap (adj := adj) (RightHomotopyClass.mk f) =
      RightHomotopyClass.mk (R.map f) := rfl

/-- Actual right-class mapping commutes with the SAME whole original adjunction transpose on every
source and
representative. -/
theorem rightHomotopyClassMap_pre_homEquiv (X : C) [IsCofibrant X]
    {F G : D} [IsFibrant G] (i : L.obj X ⟶ F) (a : RightHomotopyClass F G) :
    (rightHomotopyClassMap (adj := adj) a).precomp (adj.homEquiv X F i) =
      rightHomotopyHomEquiv (adj := adj) X G (a.precomp i) := by
  induction a using Quot.inductionOn with
  | _ a =>
    change RightHomotopyClass.mk (adj.homEquiv X F i ≫ R.map a) =
      RightHomotopyClass.mk (adj.homEquiv X G (i ≫ a))
    exact congrArg RightHomotopyClass.mk (adj.homEquiv_naturality_right i a).symm

end CategoryTheory.Adjunction.IsQuillenAdjunction
