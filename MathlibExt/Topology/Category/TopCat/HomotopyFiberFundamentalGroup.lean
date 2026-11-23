/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison.TopCatSingularHomotopyGroup
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.ConnectingHomInjectivity
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.ConnectingImageCentrality
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceHomotopyGroupIso
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MappingPathFiber
import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularPathHomotopyFiberIso
import MathlibExt.Topology.Homotopy.PiOneMapNaturality
import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality
import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoops

/-!
# The fundamental-group sequence of the complete homotopy fiber

For an arbitrary pointed map, the full ending-path homotopy fiber has its actual
fundamental-group source projection and connecting map from the actual cube-based
second homotopy group. The singular comparison and strict mapping-path fiber
isomorphisms identify these maps with the original Kan fibration-sequence maps.
The characteristic equation, exact kernel/image, source-projection range,
connecting-image centrality and injectivity criterion refer to these same maps
at the canonical selected constant-path point.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial
open scoped Simplicial Topology

universe u

namespace TopCat

private local instance singularKan (X : TopCat.{u}) :
    SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X

private local instance mappingPathKan {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SSet.KanComplex (SSet.mappingPathSpace (TopCat.toSSet.map f)) :=
  (SSet.KanComplex.W.of_mappingPathSection (TopCat.toSSet.map f)).kanComplex_target

private abbrev fiberPoint {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) : TopCat.homotopyFiber f y :=
  TopCat.homotopyFiberSelectedPointMap f x y hxy PUnit.unit

private theorem singularMap_point {X Y : TopCat.{u}} (f : X ⟶ Y)
    {x : X} {y : Y} (hxy : f x = y) :
    (TopCat.toSSet.map f).app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm y := by
  change (TopCat.toSSetObj₀Equiv (X := Y)).symm (f x) =
    (TopCat.toSSetObj₀Equiv (X := Y)).symm y
  exact congrArg (TopCat.toSSetObj₀Equiv (X := Y)).symm hxy

private abbrev nativeFiberIso {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) :=
  SSet.singularPathHomotopyFiberIso f y ≪≫
    SSet.pathHomotopyFiberStrictMappingPathIso (TopCat.toSSet.map f)
      (TopCat.toSSetObj₀Equiv.symm y)

private theorem nativeFiberIso_total {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) :
    (nativeFiberIso f y).hom ≫
      ((SSet.Subcomplex.fiber (SSet.mappingPathTarget (TopCat.toSSet.map f))
        (TopCat.toSSetObj₀Equiv.symm y)).ι ≫
          SSet.mappingPathRetract (TopCat.toSSet.map f)) =
      TopCat.toSSet.map (TopCat.homotopyFiberToTotal f y) := by
  rw [show (nativeFiberIso f y).hom =
    (SSet.singularPathHomotopyFiberIso f y).hom ≫
      (SSet.pathHomotopyFiberStrictMappingPathIso (TopCat.toSSet.map f)
        (TopCat.toSSetObj₀Equiv.symm y)).hom from rfl]
  rw [Category.assoc, SSet.pathHomotopyFiberStrictMappingPathIso_hom_total]
  exact SSet.singularPathHomotopyFiberIso_hom_toTotal f y

/-- The original Kan mapping-path sequence at the actual selected fiber point. -/
abbrev homotopyFiberFibrationSequence {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) : SSet.FibrationSequence.{u} := by
  let q := TopCat.toSSet.map f
  let z := (nativeFiberIso f y).hom.app (op ⦋0⦌)
    (TopCat.toSSetObj₀Equiv.symm (fiberPoint f x y hxy))
  exact
    { E := SSet.mappingPathSpace q
      B := TopCat.toSSet.obj Y
      p := SSet.mappingPathTarget q
      fibration_p := inferInstance
      fibrant_B := inferInstance
      e := z.1
      b := TopCat.toSSetObj₀Equiv.symm y
      hb := (SSet.Subcomplex.mem_fiber_obj_zero_iff _ _).mp z.2 }

private theorem nativeFiberIso_point {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) :
    (nativeFiberIso f y).hom.app (op ⦋0⦌)
        (TopCat.toSSetObj₀Equiv.symm (fiberPoint f x y hxy)) =
      (homotopyFiberFibrationSequence f x y hxy).fiberPoint := by
  apply Subtype.ext
  rfl

private theorem nativeRetract_point {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) :
    (SSet.mappingPathRetract (TopCat.toSSet.map f)).app (op ⦋0⦌)
        (homotopyFiberFibrationSequence f x y hxy).e = TopCat.toSSetObj₀Equiv.symm x := by
  have h := congrArg (fun k => k.app (op ⦋0⦌)
    (TopCat.toSSetObj₀Equiv.symm (fiberPoint f x y hxy))) (nativeFiberIso_total f y)
  exact h.trans (singularMap_point (TopCat.homotopyFiberToTotal f y)
    ((ConcreteCategory.congr_hom
      (TopCat.homotopyFiberSelectedPointMap_toTotal f x y hxy) PUnit.unit)))

private def fundamentalSingularEquiv (X : TopCat.{u}) (x : X) :
    FundamentalGroup X x ≃*
      SSet.KanComplex.π 1 (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x) :=
  (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x)).symm.trans
    (TopCat.homotopyGroupSingularMulEquiv 0 X x)

private theorem fundamentalSingularEquiv_naturality {X Y : TopCat.{u}} (f : X ⟶ Y)
    {x : X} {y : Y} (hxy : f x = y) (g : FundamentalGroup X x) :
    fundamentalSingularEquiv Y y (FundamentalGroup.mapOfEq f.hom hxy g) =
      SSet.KanComplex.π.map (TopCat.toSSet.map f) (singularMap_point f hxy) 1
        (fundamentalSingularEquiv X x g) := by
  cases hxy
  change TopCat.homotopyGroupSingularMulEquiv 0 Y (f x)
    ((HomotopyGroup.pi1MulEquivFundamentalGroup (X := Y) (x := f x)).symm
      (FundamentalGroup.mapOfEq f.hom rfl g)) = _
  rw [FundamentalGroup.mapOfEq_rfl,
    HomotopyGroup.piOneMulEquivFundamentalGroup_symm_map]
  change TopCat.homotopyGroupSingularMulEquiv 0 Y (f x)
      (HomotopyGroup.map f.hom
        ((HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x)).symm g)) =
    SSet.KanComplex.π.map (TopCat.toSSet.map f) (singularMap_point f rfl) 1
      (TopCat.homotopyGroupSingularMulEquiv 0 X x
        ((HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x)).symm g))
  simpa only [HomotopyGroup.mapHomOfEq_apply] using
    TopCat.homotopyGroupSingularMulEquiv_naturality 0 f rfl
      ((HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x)).symm g)

private def nativeWeakEquiv {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) (hf : SSet.KanComplex.W f)
    {a : A _⦋0⦌} {b : B _⦋0⦌} (h : f.app _ a = b) :
    SSet.KanComplex.π 1 A a ≃* SSet.KanComplex.π 1 B b := by
  cases h
  exact SSet.KanComplex.W.homotopyGroupIso f hf 0 a

private theorem nativeWeakEquiv_apply {A B : SSet.{u}}
    [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) (hf : SSet.KanComplex.W f)
    {a : A _⦋0⦌} {b : B _⦋0⦌} (h : f.app _ a = b)
    (g : SSet.KanComplex.π 1 A a) :
    nativeWeakEquiv f hf h g = SSet.KanComplex.π.map f h 1 g := by
  cases h
  rfl

/-- The actual fiber fundamental group is the corresponding Kan strict-fiber group. -/
def homotopyFiberFundamentalGroupMulEquiv {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) :
    FundamentalGroup (TopCat.homotopyFiber f y) (homotopyFiberSelectedPointMap f x y hxy PUnit.unit) ≃*
      SSet.KanComplex.π 1 (homotopyFiberFibrationSequence f x y hxy).fiber
        (homotopyFiberFibrationSequence f x y hxy).fiberPoint :=
  (fundamentalSingularEquiv (TopCat.homotopyFiber f y) (fiberPoint f x y hxy)).trans
    { toEquiv := SSet.KanComplex.π.equivOfIso (nativeFiberIso f y)
        (nativeFiberIso_point f x y hxy) 1
      map_mul' := SSet.KanComplex.π.map_mul (nativeFiberIso f y).hom
        (nativeFiberIso_point f x y hxy) 0 }

private def nativeTotalEquiv {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) :
    SSet.KanComplex.π 1 (homotopyFiberFibrationSequence f x y hxy).E (homotopyFiberFibrationSequence f x y hxy).e ≃*
      SSet.KanComplex.π 1 (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x) :=
  nativeWeakEquiv (SSet.mappingPathRetract (TopCat.toSSet.map f))
    (SSet.KanComplex.W.of_mappingPathRetract (TopCat.toSSet.map f))
    (nativeRetract_point f x y hxy)

private theorem nativeTotalEquiv_apply {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y)
    (z : SSet.KanComplex.π 1 (homotopyFiberFibrationSequence f x y hxy).E
      (homotopyFiberFibrationSequence f x y hxy).e) :
    nativeTotalEquiv f x y hxy z =
      SSet.KanComplex.π.map (SSet.mappingPathRetract (TopCat.toSSet.map f))
        (nativeRetract_point f x y hxy) 1 z :=
  nativeWeakEquiv_apply _ _ _ z

private abbrev nativeInclHom (S : SSet.FibrationSequence.{u}) :
    SSet.KanComplex.π 1 S.fiber S.fiberPoint →* SSet.KanComplex.π 1 S.E S.e :=
  ((SSet.FibrationSequence.Geometry.inclusionGroupNatTrans 0).app S).hom

private theorem nativeInclHom_apply (S : SSet.FibrationSequence.{u})
    (z : SSet.KanComplex.π 1 S.fiber S.fiberPoint) :
    nativeInclHom S z = SSet.KanComplex.π.map S.fiberIncl
      ((by rfl) : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e) 1 z := rfl

/-- The ordinary fundamental-group map of the original total-space projection. -/
def homotopyFiberFundamentalGroupProjection {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) :
    FundamentalGroup (TopCat.homotopyFiber f y) (homotopyFiberSelectedPointMap f x y hxy PUnit.unit) →*
      FundamentalGroup X x :=
  FundamentalGroup.mapOfEq (TopCat.homotopyFiberToTotal f y).hom
    ((ConcreteCategory.congr_hom
      (TopCat.homotopyFiberSelectedPointMap_toTotal f x y hxy) PUnit.unit))

private theorem homotopyFiberFundamentalGroupProjection_native {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y)
    (g : FundamentalGroup (TopCat.homotopyFiber f y) (fiberPoint f x y hxy)) :
    fundamentalSingularEquiv X x (homotopyFiberFundamentalGroupProjection f x y hxy g) =
      nativeTotalEquiv f x y hxy
        (nativeInclHom (homotopyFiberFibrationSequence f x y hxy)
          (homotopyFiberFundamentalGroupMulEquiv f x y hxy g)) := by
  let S := homotopyFiberFibrationSequence f x y hxy
  let I := nativeFiberIso f y
  let r := SSet.mappingPathRetract (TopCat.toSSet.map f)
  let a := TopCat.toSSetObj₀Equiv.symm (fiberPoint f x y hxy)
  let μ := fundamentalSingularEquiv (TopCat.homotopyFiber f y) (fiberPoint f x y hxy) g
  have hi : I.hom.app (op ⦋0⦌) a = S.fiberPoint := nativeFiberIso_point f x y hxy
  have hFiber : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e := rfl
  have hir : (I.hom ≫ S.fiberIncl).app (op ⦋0⦌) a = S.e :=
    congrArg (S.fiberIncl.app (op ⦋0⦌)) hi
  have ht : ((I.hom ≫ S.fiberIncl) ≫ r).app (op ⦋0⦌) a =
      TopCat.toSSetObj₀Equiv.symm x :=
    (congrArg (r.app (op ⦋0⦌)) hir).trans (nativeRetract_point f x y hxy)
  have hmaps : (I.hom ≫ S.fiberIncl) ≫ r =
      TopCat.toSSet.map (TopCat.homotopyFiberToTotal f y) :=
    (Category.assoc I.hom S.fiberIncl r).trans (nativeFiberIso_total f y)
  have hNat := fundamentalSingularEquiv_naturality (TopCat.homotopyFiberToTotal f y)
    ((ConcreteCategory.congr_hom
      (TopCat.homotopyFiberSelectedPointMap_toTotal f x y hxy) PUnit.unit)) g
  rw [nativeTotalEquiv_apply, nativeInclHom_apply]
  change fundamentalSingularEquiv X x (homotopyFiberFundamentalGroupProjection f x y hxy g) =
    SSet.KanComplex.π.map r (nativeRetract_point f x y hxy) 1
      (SSet.KanComplex.π.map S.fiberIncl hFiber 1
        (SSet.KanComplex.π.map I.hom hi 1 μ))
  rw [← SSet.KanComplex.π.map_comp_apply I.hom S.fiberIncl hi hFiber hir,
    ← SSet.KanComplex.π.map_comp_apply (I.hom ≫ S.fiberIncl) r hir
      (nativeRetract_point f x y hxy) ht]
  exact hNat.trans
    (congrFun (SSet.KanComplex.π.map_congr hmaps ht
      (singularMap_point (TopCat.homotopyFiberToTotal f y)
        ((ConcreteCategory.congr_hom
      (TopCat.homotopyFiberSelectedPointMap_toTotal f x y hxy) PUnit.unit))) 1) μ).symm

private def mappingPathEndpointHomotopy {A B : SSet.{u}} (q : A ⟶ B) :
    SSet.Homotopy (SSet.mappingPathRetract q ≫ q) (SSet.mappingPathTarget q) :=
  { h := (β_ (SSet.mappingPathSpace q) (Δ[1] : SSet.{u})).hom ≫
      MonoidalClosed.uncurry (SSet.mappingPathEval q)
    h₀ := (SSet.comp_eval₀_eq_ι₀_braiding_uncurry (SSet.mappingPathEval q)).symm.trans
      (pullback.condition.symm)
    h₁ := (SSet.comp_eval₁_eq_ι₁_braiding_uncurry (SSet.mappingPathEval q)).symm
    rel := by
      ext n z
      exact (show False from z.1.property).elim }

private theorem nativeHomotopy_zero_iff {A B : SSet.{u}}
    [SSet.KanComplex B] {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (a : A _⦋0⦌) (z : SSet.KanComplex.π 1 A a) :
    SSet.KanComplex.π.map f rfl 1 z = 1 ↔ SSet.KanComplex.π.map g rfl 1 z = 1 := by
  let e := (SSet.congrMapFundamentalGroupoid H).hom.app (SSet.FundamentalGroupoid.mk a)
  let T := SSet.KanComplex.π.actionMulEquiv (m := 0) e
  have h : T (SSet.KanComplex.π.map f rfl 1 z) =
      SSet.KanComplex.π.map g rfl 1 z :=
    SSet.KanComplex.π.action_map_eq_map_of_homotopy H z
  constructor
  · intro hz
    exact h.symm.trans ((congrArg T hz).trans T.map_one)
  · intro hz
    apply T.injective
    exact (h.trans hz).trans T.map_one.symm

private theorem nativeMap_zero_iff_raw {A B : SSet.{u}}
    (f : A ⟶ B)
    {a : A _⦋0⦌} {b : B _⦋0⦌} (h : f.app _ a = b)
    (z : SSet.KanComplex.π 1 A a) :
    SSet.KanComplex.π.map f h 1 z = 1 ↔ SSet.KanComplex.π.map f rfl 1 z = 1 := by
  cases h
  rfl

private theorem nativeBase_zero_iff {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y)
    (z : SSet.KanComplex.π 1 (homotopyFiberFibrationSequence f x y hxy).E
      (homotopyFiberFibrationSequence f x y hxy).e) :
    SSet.KanComplex.π.map (homotopyFiberFibrationSequence f x y hxy).p
        (homotopyFiberFibrationSequence f x y hxy).hb 1 z = 1 ↔
      SSet.KanComplex.π.map (TopCat.toSSet.map f) (singularMap_point f hxy) 1
        (nativeTotalEquiv f x y hxy z) = 1 := by
  let S := homotopyFiberFibrationSequence f x y hxy
  let q := TopCat.toSSet.map f
  let r := SSet.mappingPathRetract q
  have hc : (r ≫ q).app (op ⦋0⦌) S.e = TopCat.toSSetObj₀Equiv.symm y :=
    (congrArg (q.app (op ⦋0⦌)) (nativeRetract_point f x y hxy)).trans
      (singularMap_point f hxy)
  have hzero := (nativeMap_zero_iff_raw (r ≫ q) hc z).trans
    ((nativeHomotopy_zero_iff (mappingPathEndpointHomotopy q) S.e z).trans
      (nativeMap_zero_iff_raw S.p S.hb z).symm)
  have hcomp := SSet.KanComplex.π.map_comp_apply r q
    (nativeRetract_point f x y hxy) (singularMap_point f hxy) hc z
  rw [nativeTotalEquiv_apply]
  exact hzero.symm.trans (iff_of_eq (congrArg (fun a => a = 1) hcomp))

/-- The original cube-second-homotopy connecting map into the complete fiber fundamental group. -/
def homotopyFiberConnectingHom {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) :
    HomotopyGroup.Pi 2 Y y →*
      FundamentalGroup (TopCat.homotopyFiber f y) (homotopyFiberSelectedPointMap f x y hxy PUnit.unit) :=
  (homotopyFiberFundamentalGroupMulEquiv f x y hxy).symm.toMonoidHom.comp
    ((SSet.FibrationSequence.Geometry.sequenceConnectingGroupHom
      (homotopyFiberFibrationSequence f x y hxy) 0).comp
        (TopCat.homotopyGroupSingularMulEquiv 1 Y y).toMonoidHom)

/-- The canonical fiber equivalence carries the actual connecting map to the Kan connecting map. -/
theorem homotopyFiberConnectingHom_native {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) (a : HomotopyGroup.Pi 2 Y y) :
    homotopyFiberFundamentalGroupMulEquiv f x y hxy (homotopyFiberConnectingHom f x y hxy a) =
      SSet.FibrationSequence.Geometry.sequenceConnectingGroupHom
        (homotopyFiberFibrationSequence f x y hxy) 0 (TopCat.homotopyGroupSingularMulEquiv 1 Y y a) := by
  change (homotopyFiberFundamentalGroupMulEquiv f x y hxy)
    ((homotopyFiberFundamentalGroupMulEquiv f x y hxy).symm
      (SSet.FibrationSequence.Geometry.sequenceConnectingGroupHom
        (homotopyFiberFibrationSequence f x y hxy) 0 (TopCat.homotopyGroupSingularMulEquiv 1 Y y a))) = _
  exact (homotopyFiberFundamentalGroupMulEquiv f x y hxy).apply_symm_apply _

/-- The actual source projection kills the actual connecting image. -/
theorem homotopyFiberFundamentalGroupProjection_connecting {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) (a : HomotopyGroup.Pi 2 Y y) :
    homotopyFiberFundamentalGroupProjection f x y hxy (homotopyFiberConnectingHom f x y hxy a) = 1 := by
  apply (fundamentalSingularEquiv X x).injective
  rw [homotopyFiberFundamentalGroupProjection_native, homotopyFiberConnectingHom_native, map_one]
  have hi := SSet.FibrationSequence.Geometry.groupExact_at_fiber 0 (homotopyFiberFibrationSequence f x y hxy)
  have hz := (hi ((SSet.FibrationSequence.Geometry.sequenceConnectingGroupHom
    (homotopyFiberFibrationSequence f x y hxy) 0) (TopCat.homotopyGroupSingularMulEquiv 1 Y y a))).2
      ⟨TopCat.homotopyGroupSingularMulEquiv 1 Y y a, rfl⟩
  exact (congrArg (nativeTotalEquiv f x y hxy) hz).trans
    (nativeTotalEquiv f x y hxy).map_one

/-- A fiber loop projects to one exactly when it is the actual boundary of a second homotopy class. -/
theorem homotopyFiberFundamentalGroupProjection_exact {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y)
    (g : FundamentalGroup (TopCat.homotopyFiber f y) (homotopyFiberSelectedPointMap f x y hxy PUnit.unit)) :
    homotopyFiberFundamentalGroupProjection f x y hxy g = 1 ↔ ∃ a, homotopyFiberConnectingHom f x y hxy a = g := by
  constructor
  · intro hg
    have hz := (homotopyFiberFundamentalGroupProjection_native f x y hxy g).symm.trans
      ((congrArg (fundamentalSingularEquiv X x) hg).trans (map_one _))
    have hi : nativeInclHom (homotopyFiberFibrationSequence f x y hxy)
        (homotopyFiberFundamentalGroupMulEquiv f x y hxy g) = 1 :=
      (nativeTotalEquiv f x y hxy).injective (hz.trans (map_one _).symm)
    have hExact : Function.MulExact
        (SSet.FibrationSequence.Geometry.sequenceConnectingGroupHom (homotopyFiberFibrationSequence f x y hxy) 0)
        (nativeInclHom (homotopyFiberFibrationSequence f x y hxy)) :=
      SSet.FibrationSequence.Geometry.groupExact_at_fiber 0 (homotopyFiberFibrationSequence f x y hxy)
    obtain ⟨a, ha⟩ := (hExact (homotopyFiberFundamentalGroupMulEquiv f x y hxy g)).1 hi
    refine ⟨(TopCat.homotopyGroupSingularMulEquiv 1 Y y).symm a, ?_⟩
    apply (homotopyFiberFundamentalGroupMulEquiv f x y hxy).injective
    rw [homotopyFiberConnectingHom_native, MulEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨a, rfl⟩
    exact homotopyFiberFundamentalGroupProjection_connecting f x y hxy a

/-- The original source projection has image the kernel of the pointed original map. -/
theorem homotopyFiberFundamentalGroupProjection_range {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) :
    (homotopyFiberFundamentalGroupProjection f x y hxy).range = (FundamentalGroup.mapOfEq f.hom hxy).ker := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply (fundamentalSingularEquiv Y y).injective
    rw [fundamentalSingularEquiv_naturality, homotopyFiberFundamentalGroupProjection_native,
      (fundamentalSingularEquiv Y y).map_one]
    apply (nativeBase_zero_iff f x y hxy _).mp
    exact (homotopyFiberFibrationSequence f x y hxy).map_p_comp_fiberIncl_eq_one
      (homotopyFiberFundamentalGroupMulEquiv f x y hxy a)
  · intro hg
    have hq : SSet.KanComplex.π.map (TopCat.toSSet.map f) (singularMap_point f hxy) 1
        (fundamentalSingularEquiv X x g) = 1 :=
      (fundamentalSingularEquiv_naturality f hxy g).symm.trans
        ((congrArg (fundamentalSingularEquiv Y y) (MonoidHom.mem_ker.mp hg)).trans (map_one _))
    obtain ⟨z, hz⟩ := (nativeTotalEquiv f x y hxy).surjective (fundamentalSingularEquiv X x g)
    have hp := (nativeBase_zero_iff f x y hxy z).mpr (by rw [hz]; exact hq)
    have hExact : Function.MulExact (nativeInclHom (homotopyFiberFibrationSequence f x y hxy))
        (((SSet.FibrationSequence.Geometry.projectionGroupNatTrans 0).app
          (homotopyFiberFibrationSequence f x y hxy)).hom) :=
      SSet.FibrationSequence.Geometry.groupExact_at_total 0 (homotopyFiberFibrationSequence f x y hxy)
    obtain ⟨a, ha⟩ := (hExact z).1 hp
    refine ⟨(homotopyFiberFundamentalGroupMulEquiv f x y hxy).symm a, ?_⟩
    apply (fundamentalSingularEquiv X x).injective
    rw [homotopyFiberFundamentalGroupProjection_native, MulEquiv.apply_symm_apply, ha, hz]

/-- The actual source projection is the ordinary fundamental-group map of the fiber projection. -/
theorem homotopyFiberFundamentalGroupProjection_eq_mapOfEq {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) :
    homotopyFiberFundamentalGroupProjection f x y hxy =
      FundamentalGroup.mapOfEq (homotopyFiberToTotal f y).hom
        (ConcreteCategory.congr_hom (homotopyFiberSelectedPointMap_toTotal f x y hxy)
          PUnit.unit) := rfl

/-- Exactness identifies the original connecting image with the original projection kernel. -/
theorem homotopyFiberFundamentalGroupProjection_ker {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) :
    (homotopyFiberFundamentalGroupProjection f x y hxy).ker =
      (homotopyFiberConnectingHom f x y hxy).range := by
  ext g
  exact homotopyFiberFundamentalGroupProjection_exact f x y hxy g

/-- A trivial source second homotopy group makes the same original connecting map injective. -/
theorem homotopyFiberConnectingHom_injective {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y)
    (hX : Subsingleton (HomotopyGroup.Pi 2 X x)) :
    Function.Injective (homotopyFiberConnectingHom f x y hxy) := by
  let _ := hX
  let S := homotopyFiberFibrationSequence f x y hxy
  let q := TopCat.toSSet.map f
  let r := SSet.mappingPathRetract q
  have hSingular : Subsingleton (SSet.KanComplex.π 2 (TopCat.toSSet.obj X)
      (TopCat.toSSetObj₀Equiv.symm x)) :=
    (TopCat.homotopyGroupSingularMulEquiv 1 X x).symm.injective.subsingleton
  have hPoint : r.app (op ⦋0⦌) S.e = TopCat.toSSetObj₀Equiv.symm x :=
    nativeRetract_point f x y hxy
  have hAtRetract : Subsingleton (SSet.KanComplex.π 2 (TopCat.toSSet.obj X)
      (r.app (op ⦋0⦌) S.e)) := by
    rw [hPoint]
    exact hSingular
  let _ := hAtRetract
  let E := SSet.KanComplex.W.homotopyGroupIso r
    (SSet.KanComplex.W.of_mappingPathRetract q) 1 S.e
  have hTotal : Subsingleton (SSet.KanComplex.π 2 S.E S.e) := E.injective.subsingleton
  unfold homotopyFiberConnectingHom
  exact SSet.FibrationSequence.Geometry.sequenceConnectingGroupHom_transport_injective
    S _ _ hTotal

/-- The original connecting image is central in the original complete fiber fundamental group. -/
theorem homotopyFiberConnectingHom_range_le_center {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (hxy : f x = y) :
    (homotopyFiberConnectingHom f x y hxy).range ≤
      Subgroup.center (FundamentalGroup (homotopyFiber f y)
        (homotopyFiberSelectedPointMap f x y hxy PUnit.unit)) := by
  rintro g ⟨a, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro b
  apply (homotopyFiberFundamentalGroupMulEquiv f x y hxy).injective
  have hδ := homotopyFiberConnectingHom_native f x y hxy a
  simpa only [map_mul, hδ] using Subgroup.mem_center_iff.mp
    (SSet.FibrationSequence.Geometry.sequenceConnectingGroupHom_range_le_center
      (homotopyFiberFibrationSequence f x y hxy)
      ⟨TopCat.homotopyGroupSingularMulEquiv 1 Y y a, rfl⟩)
    (homotopyFiberFundamentalGroupMulEquiv f x y hxy b)

end TopCat

end
