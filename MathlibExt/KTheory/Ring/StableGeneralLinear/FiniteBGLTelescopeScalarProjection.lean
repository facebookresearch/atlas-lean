/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.ScalarClassifyingSource
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeScalarMap
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpaceTelescopeFundamentalGroup

/-!
# The actual scalar telescope projection square

The original projection reads every telescope arrow as its stable finite
matrix label. The same actual scalar map sends that label entrywise.
Functor equality and the earned realization composition laws therefore
prove a strict square between the original ordinary spaces. No projection
comparison, inverse, homotopy or naturality witness is an input.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap Simplicial

universe uR uS uA

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

private theorem projection_map_fiber_value (A : Type uA) [Semiring A]
    {X Y : FiniteBGLTelescopeCategory A} (a : X ⟶ Y) :
    (show (StableGL A)ᵐᵒᵖ from (finiteBGLTelescopeToStableCategory A).map a) =
      MulOpposite.op (StableGL.of (MulOpposite.unop
        (show (Matrix.GeneralLinearGroup (Fin Y.base) A)ᵐᵒᵖ from a.fiber))) := by
  change MulOpposite.op
      (((StableGL.inclusion Y.base).app (SemiRingCat.of A)).hom
        (MulOpposite.unop (show (Matrix.GeneralLinearGroup (Fin Y.base) A)ᵐᵒᵖ from a.fiber))) =
    MulOpposite.op (StableGL.of _)
  exact congrArg MulOpposite.op (StableGL.inclusion_apply Y.base A _)

/-- Every original telescope arrow satisfies the coefficient/projection functor square. -/
public theorem finiteBGLTelescopeScalarProjectionFunctor (f : R →+* S) :
    finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToStableCategory S =
      finiteBGLTelescopeToStableCategory R ⋙ classifyingCategoryScalarMap f := by
  let L := finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToStableCategory S
  let M := finiteBGLTelescopeToStableCategory R ⋙ classifyingCategoryScalarMap f
  have hObj (X : FiniteBGLTelescopeCategory R) : L.obj X = M.obj X := Subsingleton.elim _ _
  refine Functor.hext hObj ?_
  intro X Y a
  apply heq_of_eq
  change (show (StableGL S)ᵐᵒᵖ from
      (finiteBGLTelescopeToStableCategory S).map ((finiteBGLTelescopeScalarFunctor f).map a)) =
    (show (StableGL S)ᵐᵒᵖ from
      (classifyingCategoryScalarMap f).map ((finiteBGLTelescopeToStableCategory R).map a))
  let g : Matrix.GeneralLinearGroup (Fin Y.base) S :=
    Matrix.GeneralLinearGroup.mapRingHom f
      (MulOpposite.unop (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber))
  have hLabel : MulOpposite.op (StableGL.of (MulOpposite.unop (MulOpposite.op g))) =
      MulOpposite.op (StableGL.of g) :=
    congrArg (fun x : Matrix.GeneralLinearGroup (Fin Y.base) S => MulOpposite.op (StableGL.of x))
      (MulOpposite.unop_op g)
  simp only [projection_map_fiber_value, classifyingCategoryScalarMap_map,
    finiteBGLTelescopeScalarFunctor_map_fiber, MulOpposite.unop_op, scalarMap_of]
  exact hLabel

private theorem zeroRankTelescopeObject_eq (A : Type uA) [Semiring A]
    (X : FiniteBGLTelescopeCategory A) (h : X.base = 0) : X = finiteBGLTelescopeBaseObject A := by
  rcases X with ⟨n, x⟩
  change n = 0 at h
  subst n
  let : Subsingleton ((finiteClassifyingCategoryDiagram A).obj 0) := by
    rw [finiteClassifyingCategoryDiagram_obj A 0]
    simpa only [Cat.of_α] using
      (show Subsingleton (SingleObj (Matrix.GeneralLinearGroup (Fin 0) A)ᵐᵒᵖ) from
        ⟨fun _ _ => Quiver.SingleObj.ext⟩)
  have hx : x = (finiteBGLTelescopeBaseObject A).fiber := Subsingleton.elim _ _
  cases hx
  rfl

/-- The scalar functor retains the literal original rank-zero telescope object. -/
public theorem finiteBGLTelescopeScalarFunctor_baseObject (f : R →+* S) :
    (finiteBGLTelescopeScalarFunctor f).obj (finiteBGLTelescopeBaseObject R) =
      finiteBGLTelescopeBaseObject S :=
  zeroRankTelescopeObject_eq S _
    (finiteBGLTelescopeScalarFunctor_obj_base f (finiteBGLTelescopeBaseObject R))

/-- The actual coefficient functor realized between the original ordinary telescope carriers. -/
public def ordinaryFiniteBGLTelescopeScalarMap (f : R →+* S) :
    C(ordinaryFiniteBGLTelescope R, ordinaryFiniteBGLTelescope S) :=
  CategoryTheory.realizedNerveFunctorMap.{0, uR, 0, uS} (finiteBGLTelescopeScalarFunctor f)

private theorem telescopeScalarMap_point_computed (f : R →+* S) :
    ordinaryFiniteBGLTelescopeScalarMap f (ordinaryFiniteBGLTelescopeBasepoint R) =
      ordinaryFiniteBGLTelescopeBasepoint S := by
  change CategoryTheory.realizedNerveFunctorMap (finiteBGLTelescopeScalarFunctor f)
      (SSet.realizedVertex (X := nerve (FiniteBGLTelescopeCategory R))
        (ComposableArrows.mk₀ (finiteBGLTelescopeBaseObject R))) =
    SSet.realizedVertex (X := nerve (FiniteBGLTelescopeCategory S))
      (ComposableArrows.mk₀ (finiteBGLTelescopeBaseObject S))
  exact (CategoryTheory.realizedNerveFunctorMap_vertex (finiteBGLTelescopeScalarFunctor f)
    (finiteBGLTelescopeBaseObject R)).trans
      (congrArg (fun X : FiniteBGLTelescopeCategory S =>
        SSet.realizedVertex (X := nerve (FiniteBGLTelescopeCategory S)) (ComposableArrows.mk₀ X))
        (finiteBGLTelescopeScalarFunctor_baseObject f))

/-- The actual scalar telescope map preserves its original selected vertex. -/
public theorem ordinaryFiniteBGLTelescopeScalarMap_point (f : R →+* S) :
    ordinaryFiniteBGLTelescopeScalarMap f (ordinaryFiniteBGLTelescopeBasepoint R) =
      ordinaryFiniteBGLTelescopeBasepoint S :=
  telescopeScalarMap_point_computed f

private theorem projection_eq_realizedFunctor (A : Type uA) [Semiring A] :
    (ordinaryFiniteBGLTelescopeToBGL A).hom =
      CategoryTheory.realizedNerveFunctorMap.{0, uA, 0, uA}
        (finiteBGLTelescopeToStableCategory A) := by
  change (SSet.toTop.map
    (nerveMap (finiteBGLTelescopeToStableCategory A))).hom = _
  exact (CategoryTheory.realizedNerveFunctorMap_sameFrame
    (finiteBGLTelescopeToStableCategory A)).symm

/-- The original telescope projection commutes strictly with the selected
actual mixed-ring source map. -/
public theorem ordinaryFiniteBGLTelescopeScalarMap_projection (f : R →+* S) :
    (ordinaryBGLScalarMap f).comp (ordinaryFiniteBGLTelescopeToBGL R).hom =
      (ordinaryFiniteBGLTelescopeToBGL S).hom.comp (ordinaryFiniteBGLTelescopeScalarMap f) := by
  let TR := ordinaryFiniteBGLTelescope R
  let TS := ordinaryFiniteBGLTelescope S
  let BR := ordinaryBGL R
  let BS := ordinaryBGL S
  let pR : C(TR, BR) := (ordinaryFiniteBGLTelescopeToBGL R).hom
  let pS : C(TS, BS) := (ordinaryFiniteBGLTelescopeToBGL S).hom
  let b : C(BR, BS) := ordinaryBGLScalarMap f
  let t : C(TR, TS) := ordinaryFiniteBGLTelescopeScalarMap f
  let rb : C(BR, BS) := CategoryTheory.realizedNerveFunctorMap
    (classifyingCategoryScalarMap f)
  let rt : C(TR, TS) := CategoryTheory.realizedNerveFunctorMap
    (finiteBGLTelescopeScalarFunctor f)
  let rpR : C(TR, BR) := CategoryTheory.realizedNerveFunctorMap
    (finiteBGLTelescopeToStableCategory R)
  let rpS : C(TS, BS) := CategoryTheory.realizedNerveFunctorMap
    (finiteBGLTelescopeToStableCategory S)
  have hb : b = rb := ordinaryBGLScalarMap_eq_realizedFunctorMap f
  have hpR : pR = rpR := projection_eq_realizedFunctor R
  have hpS : pS = rpS := projection_eq_realizedFunctor S
  have ht : t = rt := rfl
  change b.comp pR = pS.comp t
  calc
    b.comp pR = rb.comp pR := congrArg (fun m : C(BR, BS) => m.comp pR) hb
    _ = rb.comp rpR := congrArg (fun m : C(TR, BR) => rb.comp m) hpR
    _ = CategoryTheory.realizedNerveFunctorMap
        (finiteBGLTelescopeToStableCategory R ⋙ classifyingCategoryScalarMap f) :=
      (CategoryTheory.realizedNerveFunctorMap_precomp_sameFrame
        (finiteBGLTelescopeToStableCategory R) (classifyingCategoryScalarMap f)).symm
    _ = CategoryTheory.realizedNerveFunctorMap
        (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToStableCategory S) :=
      congrArg (fun F : FiniteBGLTelescopeCategory R ⥤ ClassifyingCategory S =>
        CategoryTheory.realizedNerveFunctorMap.{0, uR, 0, uS} F)
        (finiteBGLTelescopeScalarProjectionFunctor f).symm
    _ = rpS.comp rt := CategoryTheory.realizedNerveFunctorMap_postcomp_sameFrame
      (finiteBGLTelescopeScalarFunctor f) (finiteBGLTelescopeToStableCategory S)
    _ = pS.comp rt := congrArg (fun m : C(TS, BS) => m.comp rt) hpS.symm
    _ = pS.comp t := congrArg (fun m : C(TR, TS) => pS.comp m) ht.symm

end AlgebraicKTheory.StableGL

end


noncomputable section

universe uR uS

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

private theorem ordinaryFiniteBGLTelescopeScalarMap_eq_realizedFunctorMap_computed
    (f : R →+* S) :
    ordinaryFiniteBGLTelescopeScalarMap f =
      CategoryTheory.realizedNerveFunctorMap.{0, uR, 0, uS}
        (finiteBGLTelescopeScalarFunctor f) := by
  rfl

/-- The entire SAME original telescope coefficient map has its actual
mixed-world functor realization, with both original Ring roles retained. -/
public theorem ordinaryFiniteBGLTelescopeScalarMap_eq_realizedFunctorMap
    (f : R →+* S) :
    ordinaryFiniteBGLTelescopeScalarMap f =
      CategoryTheory.realizedNerveFunctorMap.{0, uR, 0, uS}
        (finiteBGLTelescopeScalarFunctor f) :=
  ordinaryFiniteBGLTelescopeScalarMap_eq_realizedFunctorMap_computed f

end AlgebraicKTheory.StableGL

end
