/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Singular.HomotopyFunctor
public import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison.TopCatSingularHomotopyGroup
public import Mathlib.CategoryTheory.Whiskering
public import MathlibExt.Topology.Homotopy.HomotopyGroupLoopShift
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroupUnit

/-!
# The actual cube and singular homotopy functors of original pointed CGWH spaces

The existing original cube functors are retained in every literal degree.
The degree-zero comparison passes through all ordinary path components and
all singular components; the positive comparison is the existing genuine
multiplicative cube-to-singular equivalence. Its degree-one convention
retains the noncommutative fundamental-group comparison.

The two complete original functors are naturally isomorphic. The positive
comparison is also a natural Iso of genuine bundled group functors. Both
forward and inverse maps, constant classes, and full naturalities are kept.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Simplicial
open scoped Simplicial Topology

namespace PointedCGWH.CubeSingularGeometry

open PointedCGWH.SingularHomotopyGeometry (singularFunctor singularPoint piFunctor)

/-- The actual original singular space is Kan by the genuine singular construction. -/
instance singularFunctorKanComplex (X : PointedCGWH.{u, v}) :
    SSet.KanComplex (singularFunctor.obj X) :=
  TopCat.toSSet_obj_kanComplex (CGWH.cgwhToTop.obj X.right)

/-- The positive singular homotopy functor has its actual original group structure. -/
instance piFunctorGroup (n : ℕ) (X : PointedCGWH.{u, v}) :
    Group ((piFunctor (n + 1)).obj X) :=
  inferInstanceAs (Group (SSet.KanComplex.π (n + 1)
    (singularFunctor.obj X) (singularPoint X)))

/-- The complete original positive-group dictionary has the original constant unit. -/
private theorem piFunctorGroup_one (n : ℕ) (X : PointedCGWH.{u, v}) :
    @One.one ((piFunctor (n + 1)).obj X) (piFunctorGroup n X).toOne =
      SSet.KanComplex.π.mk (SSet.RelativeMorphism.const :
        (singularFunctor.obj X).PtSimplex (n + 1) (singularPoint X)) :=
  SSet.KanComplex.π.group_one_eq_instOne

/-- The genuine positive original singular homotopy functor has full group maps. -/
def singularPositiveFunctor (n : ℕ) : PointedCGWH.{u, v} ⥤ GrpCat.{v} where
  obj X := GrpCat.of ((piFunctor (n + 1)).obj X)
  map f := GrpCat.ofHom
    { toFun := (piFunctor (n + 1)).map f
      map_one' := by
        change (piFunctor (n + 1)).map f
          (@One.one _ (piFunctorGroup n _).toOne) =
            @One.one _ (piFunctorGroup n _).toOne
        rw [piFunctorGroup_one, piFunctorGroup_one]
        rw [PointedCGWH.SingularHomotopyGeometry.piFunctor_map]
        exact SSet.KanComplex.π.map_one (singularFunctor.map f)
          (PointedCGWH.SingularHomotopyGeometry.singularPoint_naturality f) (n + 1)
      map_mul' := SSet.KanComplex.π.map_mul (singularFunctor.map f)
        (PointedCGWH.SingularHomotopyGeometry.singularPoint_naturality f) n }
  map_id X := by
    apply GrpCat.hom_ext
    ext q
    exact ConcreteCategory.congr_hom ((piFunctor (n + 1)).map_id X) q
  map_comp f g := by
    apply GrpCat.hom_ext
    ext q
    exact ConcreteCategory.congr_hom ((piFunctor (n + 1)).map_comp f g) q

/-- Every full singular group map has exactly the original all-degree function. -/
theorem singularPositiveFunctor_map (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (q : (piFunctor (n + 1)).obj X) :
    ((singularPositiveFunctor n).map f).hom q = (piFunctor (n + 1)).map f q := rfl

/-- Reversing the original point equality identifies the equality-aware cube map. -/
theorem mapHomOfEq_cast_back {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) (n : ℕ)
    (q : HomotopyGroup.Pi (n + 1) X x) :
    Eq.mp (congrArg (fun z => HomotopyGroup.Pi (n + 1) Y z) h.symm)
        (HomotopyGroup.mapHomOfEq f h n q) = HomotopyGroup.map f q := by
  cases h
  rw [HomotopyGroup.mapHomOfEq_apply]
  rfl

/-- The existing original native cube functor uses the actual equality-aware cube map. -/
theorem piNMap_eq_mapHomOfEq (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (q : PointedCGWH.piN (n + 1) X) :
    PointedCGWH.piNMap (n + 1) f q = HomotopyGroup.mapHomOfEq
      (CGWH.cgwhToTop.map f.right).hom
      (PointedCGWH.underlyingBasepoint_naturality f) n q := by
  let h := PointedCGWH.underlyingBasepoint_naturality f
  let e := Equiv.cast (congrArg (fun z => HomotopyGroup.Pi (n + 1)
    (CGWH.cgwhToTop.obj Y.right) z) h.symm)
  apply e.injective
  exact (PointedCGWH.piNMap_apply (n + 1) f q).trans
    (mapHomOfEq_cast_back (CGWH.cgwhToTop.map f.right).hom h n q).symm

/-- The actual degree-zero cube type is the entire degree-zero singular homotopy type. -/
def cubeSingularZeroEquiv (X : PointedCGWH.{u, v}) :
    PointedCGWH.piN 0 X ≃ (piFunctor 0).obj X :=
  (PointedCGWH.piNZeroEquivPiZero X).trans
    ((TopCat.zerothHomotopyEquiv (X := CGWH.cgwhToTop.obj X.right)).trans
      (SSet.KanComplex.π₀EquivπZero (singularPoint X)))

/-- All ordinary cube and singular components retain the entire original map naturality. -/
theorem cubeSingularZeroEquiv_naturality {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (q : PointedCGWH.piN 0 X) :
    cubeSingularZeroEquiv Y (PointedCGWH.piNMap 0 f q) =
      (piFunctor 0).map f (cubeSingularZeroEquiv X q) := by
  let z := PointedCGWH.piNZeroEquivPiZero X q
  have hCube := PointedCGWH.piNZeroEquivPiZero_naturality f q
  have hZero := TopCat.zerothHomotopyEquiv_naturality (CGWH.cgwhToTop.map f.right) z
  have hSing := congrFun (SSet.KanComplex.mapπ_comp_π₀EquivπZero
    (singularFunctor.map f) (singularPoint X) (singularPoint Y)
    (PointedCGWH.SingularHomotopyGeometry.singularPoint_naturality f))
    (TopCat.zerothHomotopyEquiv z)
  exact (congrArg (fun w => SSet.KanComplex.π₀EquivπZero (singularPoint Y)
      (TopCat.zerothHomotopyEquiv w)) hCube).trans
    ((congrArg (SSet.KanComplex.π₀EquivπZero (singularPoint Y)) hZero).trans hSing.symm)

/-- The actual positive comparison keeps the existing genuine cube group and multiplication. -/
def cubeSingularMulEquiv (n : ℕ) (X : PointedCGWH.{u, v}) :
    PointedCGWH.piN (n + 1) X ≃* (piFunctor (n + 1)).obj X :=
  TopCat.homotopyGroupSingularMulEquiv n (CGWH.cgwhToTop.obj X.right)
    (PointedCGWH.underlyingBasepoint X)

/-- Every positive original cube map commutes with the actual original singular group map. -/
theorem cubeSingularMulEquiv_naturality (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (q : PointedCGWH.piN (n + 1) X) :
    cubeSingularMulEquiv n Y (PointedCGWH.piNMap (n + 1) f q) =
      (piFunctor (n + 1)).map f (cubeSingularMulEquiv n X q) := by
  rw [piNMap_eq_mapHomOfEq, PointedCGWH.SingularHomotopyGeometry.piFunctor_map]
  exact TopCat.homotopyGroupSingularMulEquiv_naturality n (CGWH.cgwhToTop.map f.right)
    (PointedCGWH.underlyingBasepoint_naturality f) q

/-- Every literal original cube homotopy degree has the complete singular equivalence. -/
def cubeSingularEquiv (n : ℕ) (X : PointedCGWH.{u, v}) :
    PointedCGWH.piN n X ≃ (piFunctor n).obj X :=
  match n with
  | 0 => cubeSingularZeroEquiv X
  | n + 1 => (cubeSingularMulEquiv n X).toEquiv

/-- All original whole maps retain the complete cube-singular naturality in every degree. -/
theorem cubeSingularEquiv_naturality (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (q : PointedCGWH.piN n X) :
    cubeSingularEquiv n Y (PointedCGWH.piNMap n f q) =
      (piFunctor n).map f (cubeSingularEquiv n X q) := by
  cases n with
  | zero => exact cubeSingularZeroEquiv_naturality f q
  | succ n => exact cubeSingularMulEquiv_naturality n f q

/-- The complete original cube functor is naturally the actual pointed singular homotopy functor. -/
def cubeSingularNatIso (n : ℕ) : PointedCGWH.piNFunctor.{u, v} n ≅ piFunctor n :=
  NatIso.ofComponents (fun X => (cubeSingularEquiv n X).toIso) (by
    intro X Y f
    apply ConcreteCategory.hom_ext
    intro q
    exact cubeSingularEquiv_naturality n f q)

/-- Each forward comparison component is the actual whole cube-singular equivalence. -/
theorem cubeSingularNatIso_hom_app (n : ℕ) (X : PointedCGWH.{u, v}) :
    (cubeSingularNatIso n).hom.app X = TypeCat.ofHom (cubeSingularEquiv n X) := rfl

/-- Each inverse comparison component is the actual whole inverse cube-singular equivalence. -/
theorem cubeSingularNatIso_inv_app (n : ℕ) (X : PointedCGWH.{u, v}) :
    (cubeSingularNatIso n).inv.app X = TypeCat.ofHom (cubeSingularEquiv n X).symm := rfl

/-- Every entire original inverse cube-singular comparison has the full original map naturality. -/
theorem cubeSingularNatIso_inv_naturality (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (piFunctor n).map f ≫ (cubeSingularNatIso n).inv.app Y =
      (cubeSingularNatIso n).inv.app X ≫ (PointedCGWH.piNFunctor n).map f :=
  (cubeSingularNatIso n).inv.naturality f

/-- The entire original positive cube and singular functors are naturally isomorphic as groups. -/
def cubePositiveSingularNatIso (n : ℕ) :
    PointedCGWH.piNPositiveFunctor.{u, v} n ≅ singularPositiveFunctor n :=
  NatIso.ofComponents (fun X => (cubeSingularMulEquiv n X).toGrpIso) (by
    intro X Y f
    apply GrpCat.hom_ext
    ext q
    change cubeSingularMulEquiv n Y (((PointedCGWH.piNPositiveFunctor n).map f).hom q) =
      ((singularPositiveFunctor n).map f).hom (cubeSingularMulEquiv n X q)
    exact (congrArg (cubeSingularMulEquiv n Y)
        (PointedCGWH.piNPositiveMap_apply n f q)).trans
      ((cubeSingularMulEquiv_naturality n f q).trans
        (singularPositiveFunctor_map n f (cubeSingularMulEquiv n X q)).symm))

/-- The group comparison keeps the actual forward multiplicative function. -/
theorem cubePositiveSingularNatIso_hom_app (n : ℕ) (X : PointedCGWH.{u, v})
    (q : PointedCGWH.piN (n + 1) X) :
    ((cubePositiveSingularNatIso n).hom.app X).hom q = cubeSingularMulEquiv n X q := rfl

/-- The group comparison keeps the actual inverse multiplicative function. -/
theorem cubePositiveSingularNatIso_inv_app (n : ℕ) (X : PointedCGWH.{u, v})
    (q : (piFunctor (n + 1)).obj X) :
    ((cubePositiveSingularNatIso n).inv.app X).hom q =
      (cubeSingularMulEquiv n X).symm q := rfl

/-- Every whole inverse group comparison keeps full original source-first naturality. -/
theorem cubePositiveSingularNatIso_inv_naturality (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (singularPositiveFunctor n).map f ≫ (cubePositiveSingularNatIso n).inv.app Y =
      (cubePositiveSingularNatIso n).inv.app X ≫ (PointedCGWH.piNPositiveFunctor n).map f :=
  (cubePositiveSingularNatIso n).inv.naturality f

end PointedCGWH.CubeSingularGeometry
