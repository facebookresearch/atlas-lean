/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeIntervalProductUnits
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Original marked slice maps are exactly maximal relative mapping vertices

The actual zero-parameter unit and original slice currying adjunction
identify every whole marked map over the same base with its original
maximal relative mapping vertex. Both directions retain their native
unit, base equation and complete original simplicial map.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Every original marked slice map is exactly a vertex of its actual maximal relative mapping complex. -/
def relativeMappingVertexEquiv (Z : Marked.{u}) (X Y : Over Z) :
    (X ⟶ Y) ≃ (relativeMappingComplex .maximal X.hom Y.hom) _⦋0⦌ where
  toFun f := yonedaEquiv (overParameterHomEquiv Z X (Δ[0] : SSet.{u}) Y
    ((relativePointProductIso Z X).hom ≫ f))
  invFun x := (relativePointProductIso Z X).inv ≫
    (overParameterHomEquiv Z X (Δ[0] : SSet.{u}) Y).symm (yonedaEquiv.symm x)
  left_inv f := by
    simp only [Equiv.symm_apply_apply]
    exact (relativePointProductIso Z X).inv_hom_id_assoc f
  right_inv x := by
    let e := overParameterHomEquiv Z X (Δ[0] : SSet.{u}) Y
    let a := e.symm (yonedaEquiv.symm x)
    have h := congrArg (fun g => yonedaEquiv (e g)) ((relativePointProductIso Z X).hom_inv_id_assoc a)
    exact h.trans (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply])

/-- The original marked map is read by its native zero-unit family and literal relative currying. -/
theorem relativeMappingVertexEquiv_apply (Z : Marked.{u}) (X Y : Over Z) (f : X ⟶ Y) :
    relativeMappingVertexEquiv Z X Y f =
      yonedaEquiv (overParameterHomEquiv Z X (Δ[0] : SSet.{u}) Y
        ((relativePointProductIso Z X).hom ≫ f)) := rfl

/-- Reading the native zero family back keeps exactly the original whole base-preserving map. -/
theorem relativeMappingVertexEquiv_symm_apply (Z : Marked.{u}) (X Y : Over Z)
    (x : (relativeMappingComplex .maximal X.hom Y.hom) _⦋0⦌) :
    (relativeMappingVertexEquiv Z X Y).symm x = (relativePointProductIso Z X).inv ≫
      (overParameterHomEquiv Z X (Δ[0] : SSet.{u}) Y).symm (yonedaEquiv.symm x) := rfl

/-- The same full native zero family is the original vertex's Yoneda representative. -/
theorem relativeMappingVertexEquiv_yoneda_symm (Z : Marked.{u}) (X Y : Over Z) (f : X ⟶ Y) :
    yonedaEquiv.symm (relativeMappingVertexEquiv Z X Y f) =
      overParameterHomEquiv Z X (Δ[0] : SSet.{u}) Y ((relativePointProductIso Z X).hom ≫ f) :=
  Equiv.symm_apply_apply _ _

end SSet.Marked
