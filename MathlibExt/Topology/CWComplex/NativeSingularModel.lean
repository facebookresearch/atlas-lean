/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.SingularModel
public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.FundamentalGroupIso
public import MathlibExt.Topology.Homotopy.PointRelativeComposition

/-!
# The actual pointed native singular CW model

The existing based singular-counit inverse supplies the actual inverse
and both singleton-relative families. Native realization has the same
underlying ordinary realization through its existing canonical Iso.
The marked native vertex and its point Cofibration are the original
singular vertex, not a model or inverse supplied by the caller.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomotopicalAlgebra
open scoped TopCat.modelCategory ContinuousMap

universe u

namespace TopCat

/-- Native realization of the original singular simplicial set. -/
public abbrev nativeSingularSpace (X : TopCat.{u}) : CGWH.{u, u} :=
  SSet.toCGWH.{u, u}.obj (TopCat.toSSet.obj X)

/-- The original singular vertex of the selected actual point. -/
public abbrev nativeSingularPoint (X : TopCat.{u}) (x : X) : nativeSingularSpace X :=
  SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)

/-- The existing native/ordinary realization comparison. -/
public abbrev nativeSingularToTopIso (X : TopCat.{u}) :
    (nativeSingularSpace X).toTop ≅ SSet.toTop.obj (TopCat.toSSet.obj X) :=
  SSet.realizationToTopIso.{u, u}.app (TopCat.toSSet.obj X)

/-- Calibrated actual pointed inverse data, derived from point cofibrancy. -/
public structure NativeSingularPointModel (X : TopCat.{u}) (x : X) where
  /-- The actual native singular realization equivalence. -/
  equiv : nativeSingularSpace X ≃ₕ X
  /-- Its forward map is the canonical native comparison followed by the
  ORIGINAL singular counit. -/
  forward_eq : equiv.toFun =
    ((nativeSingularToTopIso X).hom ≫ sSetTopAdj.counit.app X).hom
  /-- The original vertex maps to the original selected point. -/
  forwardPoint : equiv.toFun (nativeSingularPoint X x) = x
  /-- The actual inverse maps the original point to that same vertex. -/
  backwardPoint : equiv.invFun x = nativeSingularPoint X x
  /-- The whole native inverse family fixes the original singular vertex. -/
  leftFamily : ContinuousMap.HomotopyRel (equiv.invFun.comp equiv.toFun)
    (ContinuousMap.id (nativeSingularSpace X)) {nativeSingularPoint X x}
  /-- The whole original-space inverse family fixes the original point. -/
  rightFamily : ContinuousMap.HomotopyRel (equiv.toFun.comp equiv.invFun)
    (ContinuousMap.id X) {x}

/-- Point cofibrancy of the ACTUAL space internally derives its native
CW model and both actual point-relative inverse families. -/
public def nativeSingularPointModelOfCofibrantPoint (X : TopCat.{u}) (x : X)
    [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)] :
    NativeSingularPointModel X x := by
  let C := SSet.toTop.obj (TopCat.toSSet.obj X)
  let s := sSetTopAdj.counit.app X
  let h := singularRealization_based_inverse_of_cofibrant_point X x
  let r : X ⟶ C := Classical.choose h
  have hr := Classical.choose_spec h
  let HC := hr.2.1.some.cast (TopCat.hom_comp s r) (TopCat.hom_id (X := C))
  let HX := hr.2.2.some.cast (TopCat.hom_comp r s) (TopCat.hom_id (X := X))
  let e : nativeSingularSpace X ≃ₕ X :=
    { toFun := s.hom
      invFun := r.hom
      left_inv := ⟨HC.toHomotopy⟩
      right_inv := ⟨HX.toHomotopy⟩ }
  exact
    { equiv := e
      forward_eq := rfl
      forwardPoint := (TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x)).trans
        (TopCat.toSSetObj₀Equiv.apply_symm_apply x)
      backwardPoint := hr.1
      leftFamily := HC
      rightFamily := HX }

/-- The point Cofibration of the native model is the same actual realized
singular vertex Cofibration, independently of any target-space model. -/
public theorem nativeSingularPoint_cofibration (X : TopCat.{u}) (x : X) :
    Cofibration (TopCat.const (nativeSingularPoint X x) :
      TopCat.of PUnit.{u + 1} ⟶ (nativeSingularSpace X).toTop) :=
  SSet.realizedVertex_pointMap_cofibration
    (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x)

/-- The actual native singular model is Hausdorff. -/
public theorem nativeSingularSpace_t2Space (X : TopCat.{u}) :
    T2Space (nativeSingularSpace X) :=
  SSet.realization_t2Space (TopCat.toSSet.obj X)

/-- Original path connectedness transfers to the actual pointed native
singular model through the derived genuine CW equivalence. -/
public theorem nativeSingularSpace_pathConnected (X : TopCat.{u}) (x : X)
    [PathConnectedSpace X]
    [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)] :
    PathConnectedSpace (nativeSingularSpace X) := by
  let M := nativeSingularPointModelOfCofibrantPoint X x
  let C := SSet.toTop.obj (TopCat.toSSet.obj X)
  have hCW : ∃ C : TopCat.{u}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X) :=
    ⟨C, SSet.realization_t2Space (TopCat.toSSet.obj X),
      SSet.instCWComplexToTop (TopCat.toSSet.obj X), ⟨M.equiv⟩⟩
  exact singularRealization_pathConnected_of_connected_CWType X hCW

namespace NativeSingularPointModel

universe v

/-- This actual singular realization is a genuine CW model of the
original space. Its forward and inverse maps are the stored derived
maps, without any further model premise. -/
public theorem cwType {X : TopCat.{u}} {x : X} (M : NativeSingularPointModel X x) :
    ∃ C : TopCat.{u}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X) :=
  ⟨SSet.toTop.obj (TopCat.toSSet.obj X),
    SSet.realization_t2Space (TopCat.toSSet.obj X),
    SSet.instCWComplexToTop (TopCat.toSSet.obj X), ⟨M.equiv⟩⟩

/-- The ACTUAL original-space inverse family transports an entire
point-relative native homotopy to the SAME original target. No independent
based-model comparison family is supplied by the caller. -/
public def reflectPointRelativeHomotopy
    {X : TopCat.{u}} {x : X} (M : NativeSingularPointModel X x)
    {A : Type v} [TopologicalSpace A] (a : A) (f g : C(A, X))
    (hfa : f a = x) (hga : g a = x)
    (H : ContinuousMap.HomotopyRel (M.equiv.invFun.comp f) (M.equiv.invFun.comp g) {a}) :
    ContinuousMap.HomotopyRel f g {a} := by
  let HO := H.compContinuousMap M.equiv.toFun
  let HF : ContinuousMap.HomotopyRel (M.equiv.toFun.comp (M.equiv.invFun.comp f)) f {a} :=
    (M.rightFamily.precomposePointRelative f a hfa).cast
      (by apply ContinuousMap.ext; intro b; rfl)
      (by apply ContinuousMap.ext; intro b; rfl)
  let HG : ContinuousMap.HomotopyRel (M.equiv.toFun.comp (M.equiv.invFun.comp g)) g {a} :=
    (M.rightFamily.precomposePointRelative g a hga).cast
      (by apply ContinuousMap.ext; intro b; rfl)
      (by apply ContinuousMap.ext; intro b; rfl)
  exact (HF.symm.trans HO).trans HG

/-- The original selected target fundamental-group commutativity
transports through the DERIVED actual pointed model equivalence. The
native Group dictionaries are unchanged. -/
public theorem fundamentalGroup_isMulCommutative
    {X : TopCat.{u}} {x : X} (M : NativeSingularPointModel X x)
    [IsMulCommutative (FundamentalGroup X x)] :
    IsMulCommutative (FundamentalGroup (nativeSingularSpace X) (nativeSingularPoint X x)) := by
  let e := FundamentalGroup.mulEquivOfHomotopyEquivAt M.equiv
    (nativeSingularPoint X x) x M.forwardPoint
  apply IsMulCommutative.of_comm
  intro p q
  apply e.injective
  exact (e.map_mul p q).trans
    ((mul_comm' (e p) (e q)).trans (e.map_mul q p).symm)

end NativeSingularPointModel

end TopCat

end
