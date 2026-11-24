/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Basic
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Determinant

/-!
# Stable determinant `StableGL R →* Rˣ`

The finite determinants assemble into a cocone from the finite-GL stabilization
diagram `finiteGLDiagram.obj (SemiRingCat.of R)` to `GrpCat.of Rˣ`.  Compatibility
uses successor-stabilization invariance `det_stabilization`.  The universal
property of the explicit filtered colimit then yields `StableGL.det`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace AlgebraicKTheory
namespace StableGL

variable {R : Type u} [CommRing R]

/-- Determinant cocone from the finite-GL diagram to `Rˣ`; compatible by `det_stabilization`. -/
def detCocone : Cocone (finiteGLDiagram.obj (SemiRingCat.of R)) where
  pt := GrpCat.of Rˣ
  ι :=
    NatTrans.ofSequence
      (fun n => GrpCat.ofHom (Matrix.GeneralLinearGroup.det (n := Fin n) (R := R)))
      (fun n => by
        have hmap :
            (finiteGLDiagram.obj (SemiRingCat.of R)).map
              (homOfLE (Nat.le_add_right n 1)) =
              GrpCat.ofHom (Matrix.GeneralLinearGroup.stabilization (R := R)) :=
          finiteGLDiagram_obj_map_succ (R := SemiRingCat.of R) n
        rw [hmap]
        apply GrpCat.hom_ext
        ext g
        exact Matrix.GeneralLinearGroup.det_stabilization g)

/-- Stable determinant induced by the colimit universal property. -/
def det : StableGL R →* Rˣ :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit
      (F := finiteGLDiagram.obj (SemiRingCat.of R))).desc detCocone |>.hom

/-- Finite determinant agrees with the stable determinant on representatives. -/
@[simp]
theorem det_of {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R) :
    det (R := R) (StableGL.of g) = Matrix.GeneralLinearGroup.det g := by
  have hfac :=
    (GrpCat.FilteredColimits.colimitCoconeIsColimit
        (F := finiteGLDiagram.obj (SemiRingCat.of R))).fac detCocone n
  have h_of : StableGL.of g =
      ((GrpCat.FilteredColimits.colimitCocone
        (F := finiteGLDiagram.obj (SemiRingCat.of R))).ι.app n).hom g := rfl
  have h_comp :
      ((GrpCat.FilteredColimits.colimitCoconeIsColimit
          (F := finiteGLDiagram.obj (SemiRingCat.of R))).desc detCocone).hom
          (((GrpCat.FilteredColimits.colimitCocone
              (F := finiteGLDiagram.obj (SemiRingCat.of R))).ι.app n).hom g) =
        ((GrpCat.FilteredColimits.colimitCocone
            (F := finiteGLDiagram.obj (SemiRingCat.of R))).ι.app n ≫
          (GrpCat.FilteredColimits.colimitCoconeIsColimit
            (F := finiteGLDiagram.obj (SemiRingCat.of R))).desc detCocone).hom g := rfl
  have h_det : (detCocone.ι.app n).hom g = Matrix.GeneralLinearGroup.det g := rfl
  change ((GrpCat.FilteredColimits.colimitCoconeIsColimit
      (F := finiteGLDiagram.obj (SemiRingCat.of R))).desc detCocone).hom
      (StableGL.of g) = Matrix.GeneralLinearGroup.det g
  rw [h_of, h_comp, hfac, h_det]

end StableGL
end AlgebraicKTheory

end
