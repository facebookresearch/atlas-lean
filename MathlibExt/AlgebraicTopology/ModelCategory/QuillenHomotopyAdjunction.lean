/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy

/-!
# Actual Quillen transposition of model homotopy classes

A genuine Quillen adjunction transposes right homotopy classes between
an actual cofibrant source and actual fibrant target. The forward proof
maps a genuine good path object through the right adjoint, using fibrant
Brown preservation. The inverse maps a genuine good cylinder through the
left adjoint, using cofibrant Brown preservation. Every endpoint map is
the original adjunction transpose; no derived-adjunction outcome is used.
-/

@[expose] public section

noncomputable section
universe u₁ u₂ v₁ v₂
open CategoryTheory HomotopicalAlgebra

namespace CategoryTheory.Adjunction.IsQuillenAdjunction

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
    {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {L : C ⥤ D} {R : D ⥤ C} {adj : L ⊣ R} [IsQuillenAdjunction adj]

/-- Genuine Quillen transposition preserves and reflects the actual model right-homotopy relation.
-/
theorem rightHomotopyRel_homEquiv_iff {X : C} {Y : D} [IsCofibrant X] [IsFibrant Y]
    (f g : L.obj X ⟶ Y) :
    RightHomotopyRel f g ↔ RightHomotopyRel (adj.homEquiv X Y f) (adj.homEquiv X Y g) := by
  let _ : IsCofibrant (L.obj X) := preservesCofibrantObjects (adj := adj) inferInstance
  let _ : IsFibrant (R.obj Y) := preservesFibrantObjects (adj := adj) inferInstance
  constructor
  · intro h
    obtain ⟨P, hP, ⟨h⟩⟩ := h.exists_good_pathObject
    let _ : P.IsGood := hP
    let _ : IsFibrant P.P := inferInstance
    let Q : PathObject (R.obj Y) :=
      { __ := P.toPrepathObject.map R
        weakEquivalence_ι := map_weakEquivalence_of_fibrant (adj := adj) P.ι }
    refine ⟨Q, ⟨{ h := adj.homEquiv X P.P h.h, h₀ := ?_, h₁ := ?_ }⟩⟩
    · exact ((adj.homEquiv_naturality_right h.h P.p₀).symm).trans
        (congrArg (adj.homEquiv X Y) h.h₀)
    · exact ((adj.homEquiv_naturality_right h.h P.p₁).symm).trans
        (congrArg (adj.homEquiv X Y) h.h₁)
  · intro h
    have hL : LeftHomotopyRel (adj.homEquiv X Y f) (adj.homEquiv X Y g) :=
      leftHomotopyRel_iff_rightHomotopyRel.mpr h
    obtain ⟨P, hP, ⟨h⟩⟩ := hL.exists_good_cylinder
    let _ : P.IsGood := hP
    let _ : IsCofibrant P.I := inferInstance
    let Q : Cylinder (L.obj X) :=
      { __ := P.toPrecylinder.map L
        weakEquivalence_π := map_weakEquivalence_of_cofibrant (adj := adj) P.π }
    have hQ : Q.LeftHomotopy f g :=
      { h := (adj.homEquiv P.I Y).symm h.h
        h₀ := ((adj.homEquiv_naturality_left_symm P.i₀ h.h).symm).trans
          ((congrArg (adj.homEquiv X Y).symm h.h₀).trans ((adj.homEquiv X Y).symm_apply_apply f))
        h₁ := ((adj.homEquiv_naturality_left_symm P.i₁ h.h).symm).trans
          ((congrArg (adj.homEquiv X Y).symm h.h₁).trans ((adj.homEquiv X Y).symm_apply_apply g)) }
    exact leftHomotopyRel_iff_rightHomotopyRel.mp hQ.leftHomotopyRel

/-- The SAME original adjunction Hom equivalence descends genuinely to actual model right-homotopy
classes. -/
def rightHomotopyHomEquiv (X : C) (Y : D) [IsCofibrant X] [IsFibrant Y] :
    RightHomotopyClass (L.obj X) Y ≃ RightHomotopyClass X (R.obj Y) where
  toFun := Quot.map (adj.homEquiv X Y) (fun f g h => (rightHomotopyRel_homEquiv_iff (adj := adj) f
    g).mp h)
  invFun := Quot.map (adj.homEquiv X Y).symm (by
    intro f g h
    apply (rightHomotopyRel_homEquiv_iff (adj := adj) ((adj.homEquiv X Y).symm f)
      ((adj.homEquiv X Y).symm g)).mpr
    simpa only [Equiv.apply_symm_apply] using h)
  left_inv f := Quot.inductionOn f (fun f =>
    congrArg RightHomotopyClass.mk ((adj.homEquiv X Y).symm_apply_apply f))
  right_inv f := Quot.inductionOn f (fun f =>
    congrArg RightHomotopyClass.mk ((adj.homEquiv X Y).apply_symm_apply f))

/-- The actual model class equivalence sends every original representative to its SAME original
adjunction transpose. -/
theorem rightHomotopyHomEquiv_mk (X : C) (Y : D) [IsCofibrant X] [IsFibrant Y]
    (f : L.obj X ⟶ Y) :
    rightHomotopyHomEquiv (adj := adj) X Y (RightHomotopyClass.mk f) =
      RightHomotopyClass.mk (adj.homEquiv X Y f) := rfl

end CategoryTheory.Adjunction.IsQuillenAdjunction
