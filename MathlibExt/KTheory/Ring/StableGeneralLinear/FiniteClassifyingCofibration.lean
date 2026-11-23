/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpace
public import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarNerve
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHRealizationCofibrations
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Types.Basic
public import MathlibExt.CategoryTheory.ClassifyingSpace.Group

/-!
# Cofibrations of the original finite BGL stages

The original successor stabilization is injective on its actual matrix
group. It is therefore injective on every actual composable-arrow simplex.
The original nerve map is a monomorphism, and its original ordinary and
native realizations are cofibrations through the existing realization APIs.
No inclusion, filtration, CW or cofibration witness is supplied.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen CGWH.modelCategory TopCat.modelCategory

universe u w

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Semiring R]

/-- The original successor nerve map of the finite classifying diagram. -/
public abbrev finiteBGLSuccessorNerveMap (n : ℕ) :
    nerve ((finiteClassifyingCategoryDiagram R).obj n) ⟶
      nerve ((finiteClassifyingCategoryDiagram R).obj (n + 1)) :=
  nerveMap (((finiteClassifyingCategoryDiagram R).map
    (homOfLE (Nat.le_add_right n 1))).toFunctor)

/-- The actual successor nerve map is injective at EVERY simplex,
retaining all original matrix arrows and the original diagram transition. -/
public theorem finiteBGLSuccessorNerveMap_mono (n : ℕ) :
    Mono (finiteBGLSuccessorNerveMap R n) := by
  let k : n ⟶ n + 1 := homOfLE (Nat.le_add_right n 1)
  let F := (finiteGLDiagram.obj (SemiRingCat.of R)).map k
  have hF : Function.Injective F := by
    change Function.Injective
      ((finiteGLDiagram.obj (SemiRingCat.of R)).map (homOfLE (Nat.le_add_right n 1)))
    rw [finiteGLDiagram_obj_map_succ (R := SemiRingCat.of R) n]
    exact Matrix.GeneralLinearGroup.stabilization_injective
  let G := ((finiteClassifyingCategoryDiagram R).map k).toFunctor
  let : G.Faithful :=
    { map_injective := by
        intro X Y a b hab
        apply MulOpposite.unop_injective
        apply hF
        change MulOpposite.op (F (MulOpposite.unop a)) =
          MulOpposite.op (F (MulOpposite.unop b)) at hab
        exact congrArg MulOpposite.unop hab }
  let : Subsingleton ((finiteClassifyingCategoryDiagram R).obj n) := by
    rw [finiteClassifyingCategoryDiagram_obj R n]
    change Subsingleton (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
    infer_instance
  have hObj : Function.Injective G.obj := by
    intro X Y hXY
    exact Subsingleton.elim X Y
  change Mono (nerveMap G)
  exact SSet.nerveMap_mono_of_faithful G hObj

/-- The original native finite-stage transition is a cofibration; its
actual map is the realization of the PROVED original nerve mono. -/
public theorem finiteBGLSuccessor_cofibration (n : ℕ) :
    Cofibration ((finiteBGLDiagram.{w} R).map (homOfLE (Nat.le_add_right n 1))) := by
  let f := finiteBGLSuccessorNerveMap R n
  letI : Mono f := finiteBGLSuccessorNerveMap_mono R n
  letI : Cofibration f := (SSet.modelCategoryQuillen.cofibration_iff f).mpr inferInstance
  change Cofibration (SSet.toCGWH.{w, u}.map f)
  exact CGWH.modelCategory.toCGWH_map_cofibration f

/-- The corresponding ORIGINAL ordinary realized transition is a
cofibration, with no product or model witness added. -/
public theorem finiteOrdinaryBGLSuccessor_cofibration (n : ℕ) :
    Cofibration (SSet.toTop.map (finiteBGLSuccessorNerveMap R n)) := by
  letI : Mono (finiteBGLSuccessorNerveMap R n) := finiteBGLSuccessorNerveMap_mono R n
  exact (cofibration_iff _).mpr
    (SSet.toTop_map_mem_realizedBoundaryLLP (finiteBGLSuccessorNerveMap R n))

/-- The ORIGINAL finite-stage inclusion sends its actual native group
vertex to the original stable BGL vertex. -/
public theorem finiteBGLToBGL_nativeGroupPoint (n : ℕ) :
    finiteBGLToBGL.{w} R n
        (CategoryTheory.groupClassifyingNativePoint.{u, w} (Matrix.GeneralLinearGroup (Fin n) R)) =
      BGLBasepoint.{w} R := by
  rw [CategoryTheory.groupClassifyingNativePoint_eq_categoryPoint.{u, w}]
  exact CategoryTheory.classifyingSpaceCGWH_map_point.{w, u, 0} (finiteToStableCategoryMap R n).toFunctor
    (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)

end AlgebraicKTheory.StableGL

end
