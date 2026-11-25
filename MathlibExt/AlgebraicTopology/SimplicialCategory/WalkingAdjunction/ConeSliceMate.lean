/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The original join/path slice map is the native adjunction mate

The two actual structured cone adjunctions construct a natural map
between their original right adjoints. Its full component is exactly
the already defined join-to-path slice map, with the same leading
projection. This identification uses the original counit evaluation
and whole fat-cone/path dictionary.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet.WalkingAdjunction.ConeSliceMate

/-- The native right mate of the actual whole cone comparison. -/
def comparison : joinRightDivision (Δ[0] : SSet.{u}) ⟶ FatCone.pathFunctor :=
  conjugateEquiv (joinOverAdjunction (Δ[0] : SSet.{u})) FatCone.adjunction FatCone.joinComparison

private theorem joinCounit_read (P : Under (Δ[0] : SSet.{u})) :
    ((joinOverAdjunction (Δ[0] : SSet.{u})).counit.app P).right = sliceOver.evaluation P.right P.hom := by
  change (sliceOver.homEquiv P.right P.hom (sliceOver P.right P.hom) (𝟙 _)).val = _
  rw [sliceOver.homEquiv_apply]
  have hid : (join.map (𝟙 (sliceOver P.right P.hom))).app (Δ[0] : SSet.{u}) = 𝟙 _ :=
    NatTrans.congr_app (join.{u}.map_id (sliceOver P.right P.hom)) (Δ[0] : SSet.{u})
  exact (congrArg (fun p => p ≫ sliceOver.evaluation P.right P.hom) hid).trans (Category.id_comp _)

/-- The entire native mate component is the identical original join-to-path slice map. -/
theorem comparison_app (P : Under (Δ[0] : SSet.{u})) :
    comparison.app P = ConeCylinder.joinToPath P.right P.hom := by
  let X : SSet.{u} := sliceOver P.right P.hom
  let B : X ⟶ pathSliceOver P.hom := comparison.app P
  let j : X ⋆ (Δ[0] : SSet.{u}) ⟶ P.right :=
    ((joinOverAdjunction (Δ[0] : SSet.{u})).counit.app P).right
  let q : FatCone.underFunctor.obj X ⟶ P :=
    FatCone.joinComparison.app X ≫ (joinOverAdjunction (Δ[0] : SSet.{u})).counit.app P
  have hhom : FatCone.adjunction.homEquiv X P = FatCone.homEquiv X P := by
    rw [FatCone.adjunction, Adjunction.mkOfHomEquiv_homEquiv]
  have hs : (FatCone.adjunction.homEquiv X P).symm B =
      FatCone.underFunctor.map B ≫ FatCone.adjunction.counit.app P :=
    Adjunction.homEquiv_counit FatCone.adjunction X P B
  have hq : (FatCone.adjunction.homEquiv X P).symm B = q :=
    hs.trans (conjugateEquiv_counit (joinOverAdjunction (Δ[0] : SSet.{u}))
      FatCone.adjunction FatCone.joinComparison P)
  have he : B = FatCone.homEquiv X P q :=
    (Equiv.apply_symm_apply (FatCone.adjunction.homEquiv X P) B).symm.trans
      ((congrArg (FatCone.adjunction.homEquiv X P) hq).trans (congrArg (fun e => e q) hhom))
  have hpath : FatCone.toPath q.right = ConeCylinder.pathOfJoinCone (sliceOver.evaluation P.right P.hom) := by
    have hf : q.right = FatCone.toJoin X ≫ j := rfl
    have hj : j = sliceOver.evaluation P.right P.hom := joinCounit_read P
    exact (congrArg FatCone.toPath hf).trans
      ((FatCone.toPath_toJoin j).trans (congrArg ConeCylinder.pathOfJoinCone hj))
  change B = ConeCylinder.joinToPath P.right P.hom
  exact pathSliceOver.hom_ext P.hom
    ((congrArg (fun p => p ≫ pathSliceOver.fst P.hom) he).trans
      ((FatCone.homEquiv_fst X P q).trans
        (hpath.trans (ConeCylinder.joinToPath_fst P.right P.hom).symm)))

/-- The whole native right mate retains the identical original leading projection. -/
theorem comparison_proj (P : Under (Δ[0] : SSet.{u})) :
    comparison.app P ≫ pathSliceOver.proj P.hom = sliceOver.proj P.right P.hom := by
  rw [comparison_app]
  exact ConeCylinder.joinToPath_proj P.right P.hom

end SSet.WalkingAdjunction.ConeSliceMate
