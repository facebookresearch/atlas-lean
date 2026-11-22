/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.Singular.LoopComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.GroupFunctors

/-!
# The whole actual original native loop homotopy shift

The original one-sphere internal-Hom loop functor has its full all-degree
cube homotopy shift. The genuine native singular Iso and actual based-path
connecting equivalence construct all maps and preserve every original
pointed-map naturality, including all degree-zero loop components.

In positive target degrees the shift is a genuine natural Iso of the
existing original cube group functors. Its underlying function agrees with
the all-degree shift, and both whole inverse naturalities are retained.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed Simplicial Topology

namespace PointedCGWH.NativeLoopShiftGeometry

open PointedCGWH.SingularHomotopyGeometry
  (singularFunctor singularPoint singularPoint_naturality piFunctor)
open PointedCGWH.CubeSingularGeometry
  (cubeSingularEquiv cubeSingularNatIso cubeSingularMulEquiv cubePositiveSingularNatIso
    singularPositiveFunctor piFunctorGroup)
open SSet.LoopShiftOriginalGeometry (originalLoopPoint loopConnectingEquiv)

/-- The full original native-loop singular complex has its genuine Kan property. -/
instance nativeLoopSingularFunctorKanComplex (X : PointedCGWH.{u, v}) :
    SSet.KanComplex (nativeLoopSingularFunctor.obj X) :=
  PointedCGWH.CubeSingularGeometry.singularFunctorKanComplex (PointedCGWH.loop.obj X)

/-- The full original strict-loop singular complex has its genuine Kan property. -/
instance strictLoopSingularFunctorKanComplex (X : PointedCGWH.{u, v}) :
    SSet.KanComplex (strictLoopSingularFunctor.obj X) :=
  SSet.loopSpace_kanComplex (singularFunctor.obj X) (singularPoint X)

/-- Every original native-loop singular homotopy degree forms its complete functor. -/
def nativeLoopPiFunctor (n : ℕ) : PointedCGWH.{u, v} ⥤ Type v :=
  PointedCGWH.loop ⋙ piFunctor n

/-- Equal original singular maps retain the same entire original based-path map. -/
theorem basedPathMap_original_eq {X Y : SSet.{v}} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f g : X ⟶ Y) (hEq : f = g) (hf : f.app _ x = y) (hg : g.app _ x = y) :
    SSet.basedPathMap f hf = SSet.basedPathMap g hg := by
  cases hEq
  rfl

/-- Every entire original pointed singular map gives its actual based-path fibration sequence. -/
def loopSequenceFunctor : PointedCGWH.{u, v} ⥤ SSet.FibrationSequence.{v} where
  obj X := SSet.loopFibrationSequence (singularFunctor.obj X) (singularPoint X)
  map f := SSet.loopFibrationSequenceHom (singularFunctor.map f) (singularPoint_naturality f)
  map_id X := by
    apply SSet.FibrationSequence.Geometry.hom_ext
    · exact (basedPathMap_original_eq (x := singularPoint X) (y := singularPoint X)
        _ _ (singularFunctor.map_id X) (singularPoint_naturality (𝟙 X)) rfl).trans
          SSet.basedPathMap_id
    · exact singularFunctor.map_id X
  map_comp {X Y Z} f g := by
    have hPoint : (singularFunctor.map f ≫ singularFunctor.map g).app _
        (singularPoint X) = singularPoint Z := by
      change (singularFunctor.map g).app _
        ((singularFunctor.map f).app _ (singularPoint X)) = _
      rw [singularPoint_naturality, singularPoint_naturality]
    apply SSet.FibrationSequence.Geometry.hom_ext
    · exact (basedPathMap_original_eq (x := singularPoint X) (y := singularPoint Z)
        _ _ (singularFunctor.map_comp f g) (singularPoint_naturality (f ≫ g)) hPoint).trans
        (SSet.basedPathMap_comp (singularFunctor.map f) (singularFunctor.map g)
          (singularPoint_naturality f) (singularPoint_naturality g))
    · exact singularFunctor.map_comp f g

/-- The entire original based-path sequence fiber is the original strict singular loop functor. -/
def loopSequenceFiberNatIso :
    loopSequenceFunctor.{u, v} ⋙ SSet.FibrationSequence.Geometry.fiberFunctor ≅
      strictLoopSingularFunctor := Iso.refl _

/-- Every original strict-loop degree is the complete original sequence fiber homotopy functor. -/
def strictLoopPiFunctor (n : ℕ) : PointedCGWH.{u, v} ⥤ Type v :=
  loopSequenceFunctor ⋙ SSet.FibrationSequence.Geometry.fiberPiFunctor n

/-- The genuine original native loop singular homotopy comparison is fully natural. -/
def nativeLoopSingularPiNatIso (n : ℕ) : nativeLoopPiFunctor.{u, v} n ≅ strictLoopPiFunctor n :=
  NatIso.ofComponents (fun X => (SSet.KanComplex.π.equivOfIso (nativeLoopSingularIso X)
    (nativeLoopSingularIso_hom_point X) n).toIso) (by
      intro X Y f
      apply ConcreteCategory.hom_ext
      intro q
      exact SSet.KanComplex.π.map_square
        (nativeLoopSingularIso X).hom (nativeLoopSingularIso Y).hom
        (nativeLoopSingularFunctor.map f) (strictLoopSingularFunctor.map f)
        (nativeLoopSingularIso_naturality f)
        (nativeLoopSingularIso_hom_point X) (nativeLoopSingularIso_hom_point Y)
        (singularPoint_naturality (PointedCGWH.loop.map f))
        (strictLoopSingularFunctor_map_point f) n q)

/-- The entire original based-path connecting equivalence is the full strict-loop homotopy Iso. -/
def loopConnectingPiNatIso (n : ℕ) : piFunctor.{u, v} (n + 1) ≅ strictLoopPiFunctor n :=
  NatIso.ofComponents (fun X =>
    (loopConnectingEquiv n (singularFunctor.obj X) (singularPoint X)).toIso) (by
      intro X Y f
      apply ConcreteCategory.hom_ext
      intro q
      exact (SSet.LoopShiftOriginalGeometry.loopConnectingEquiv_naturality
        (singularFunctor.map f) (singularPoint_naturality f) n q).symm)

/-- The original native one-sphere loop functor has its complete all-degree cube homotopy shift. -/
def nativeLoopPiShiftNatIso (n : ℕ) :
    PointedCGWH.loop.{u, v} ⋙ PointedCGWH.piNFunctor n ≅ PointedCGWH.piNFunctor (n + 1) :=
  Functor.isoWhiskerLeft PointedCGWH.loop (cubeSingularNatIso n) ≪≫
    nativeLoopSingularPiNatIso n ≪≫ (loopConnectingPiNatIso n).symm ≪≫
      (cubeSingularNatIso (n + 1)).symm

/-- The whole forward native shift retains all actual original comparison functions. -/
theorem nativeLoopPiShiftNatIso_hom_app (n : ℕ) (X : PointedCGWH.{u, v})
    (q : PointedCGWH.piN n (PointedCGWH.loop.obj X)) :
    (nativeLoopPiShiftNatIso n).hom.app X q =
      (cubeSingularEquiv (n + 1) X).symm
        ((loopConnectingEquiv n (singularFunctor.obj X) (singularPoint X)).symm
          (SSet.KanComplex.π.map (nativeLoopSingularIso X).hom
            (nativeLoopSingularIso_hom_point X) n
              (cubeSingularEquiv n (PointedCGWH.loop.obj X) q))) := rfl

/-- The whole inverse native shift retains all actual original inverse comparison functions. -/
theorem nativeLoopPiShiftNatIso_inv_app (n : ℕ) (X : PointedCGWH.{u, v})
    (q : PointedCGWH.piN (n + 1) X) :
    (nativeLoopPiShiftNatIso n).inv.app X q =
      (cubeSingularEquiv n (PointedCGWH.loop.obj X)).symm
        (SSet.KanComplex.π.map (nativeLoopSingularIso X).inv
          (nativeLoopSingularIso_inv_point X) n
            (loopConnectingEquiv n (singularFunctor.obj X) (singularPoint X)
              (cubeSingularEquiv (n + 1) X q))) := rfl

/-- Every whole original pointed map retains the full forward cube shift naturality. -/
theorem nativeLoopPiShiftNatIso_hom_naturality (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.loop ⋙ PointedCGWH.piNFunctor n).map f ≫
        (nativeLoopPiShiftNatIso n).hom.app Y =
      (nativeLoopPiShiftNatIso n).hom.app X ≫ (PointedCGWH.piNFunctor (n + 1)).map f :=
  (nativeLoopPiShiftNatIso n).hom.naturality f

/-- Every whole original pointed map retains the full inverse cube shift naturality. -/
theorem nativeLoopPiShiftNatIso_inv_naturality (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.piNFunctor (n + 1)).map f ≫ (nativeLoopPiShiftNatIso n).inv.app Y =
      (nativeLoopPiShiftNatIso n).inv.app X ≫
        (PointedCGWH.loop ⋙ PointedCGWH.piNFunctor n).map f :=
  (nativeLoopPiShiftNatIso n).inv.naturality f

/-- The positive native-loop homotopy object has its actual original Kan group structure. -/
instance nativeLoopPiFunctorGroup (n : ℕ) (X : PointedCGWH.{u, v}) :
    Group ((nativeLoopPiFunctor (n + 1)).obj X) := piFunctorGroup n (PointedCGWH.loop.obj X)

/-- The positive strict-loop homotopy object has its actual original Kan group structure. -/
instance strictLoopPiFunctorGroup (n : ℕ) (X : PointedCGWH.{u, v}) :
    Group ((strictLoopPiFunctor (n + 1)).obj X) :=
  inferInstanceAs
    (Group ((loopSequenceFunctor ⋙ SSet.FibrationSequence.Geometry.fiberGroupFunctor n).obj X))

/-- The full positive strict-loop homotopy construction is its genuine group functor. -/
def strictLoopPositiveFunctor (n : ℕ) : PointedCGWH.{u, v} ⥤ GrpCat.{v} :=
  loopSequenceFunctor ⋙ SSet.FibrationSequence.Geometry.fiberGroupFunctor n

/-- The entire native singular loop comparison retains its genuine positive multiplication. -/
def nativeLoopSingularPiMulEquiv (n : ℕ) (X : PointedCGWH.{u, v}) :
    (nativeLoopPiFunctor (n + 1)).obj X ≃* (strictLoopPiFunctor (n + 1)).obj X where
  toEquiv := SSet.KanComplex.π.equivOfIso (nativeLoopSingularIso X)
    (nativeLoopSingularIso_hom_point X) (n + 1)
  map_mul' := SSet.KanComplex.π.map_mul (nativeLoopSingularIso X).hom
    (nativeLoopSingularIso_hom_point X) n

/-- All original native and strict singular loop group maps form the full group natural Iso. -/
def nativeLoopSingularPositiveNatIso (n : ℕ) :
    PointedCGWH.loop.{u, v} ⋙ singularPositiveFunctor n ≅ strictLoopPositiveFunctor n :=
  NatIso.ofComponents (fun X => (nativeLoopSingularPiMulEquiv n X).toGrpIso) (by
    intro X Y f
    apply GrpCat.hom_ext
    exact MonoidHom.ext (fun q => ConcreteCategory.congr_hom
      ((nativeLoopSingularPiNatIso (n + 1)).hom.naturality f) q))

/-- The actual based-path group connecting equivalence is the full strict-loop group natural Iso. -/
def loopConnectingPositiveNatIso (n : ℕ) :
    singularPositiveFunctor.{u, v} (n + 1) ≅ strictLoopPositiveFunctor n :=
  NatIso.ofComponents (fun X =>
    (SSet.loopConnectingMulEquiv n (singularFunctor.obj X) (singularPoint X)).toGrpIso) (by
      intro X Y f
      apply GrpCat.hom_ext
      exact MonoidHom.ext (fun q => (SSet.loopConnectingMulEquiv_naturality
        (singularFunctor.map f) (singularPoint_naturality f) n q).symm))

/-- The actual original native loop cube shift is fully natural as a genuine group Iso. -/
def nativeLoopGroupShiftNatIso (n : ℕ) :
    PointedCGWH.loop.{u, v} ⋙ PointedCGWH.piNPositiveFunctor n ≅
      PointedCGWH.piNPositiveFunctor (n + 1) :=
  Functor.isoWhiskerLeft PointedCGWH.loop (cubePositiveSingularNatIso n) ≪≫
    nativeLoopSingularPositiveNatIso n ≪≫ (loopConnectingPositiveNatIso n).symm ≪≫
      (cubePositiveSingularNatIso (n + 1)).symm

/-- The full positive group shift retains the actual original forward comparison function. -/
theorem nativeLoopGroupShiftNatIso_hom_app (n : ℕ) (X : PointedCGWH.{u, v})
    (q : PointedCGWH.piN (n + 1) (PointedCGWH.loop.obj X)) :
    ((nativeLoopGroupShiftNatIso n).hom.app X).hom q =
      (cubeSingularMulEquiv (n + 1) X).symm
        ((@MulEquiv.toEquiv
            (SSet.KanComplex.π (n + 2) (singularFunctor.obj X) (singularPoint X))
            (SSet.KanComplex.π (n + 1) (SSet.loopSpace (singularFunctor.obj X) (singularPoint X))
              (originalLoopPoint (singularFunctor.obj X) (singularPoint X)))
            (inferInstance : Group (SSet.KanComplex.π (n + 2)
              (singularFunctor.obj X) (singularPoint X))).toMul
            (inferInstance : Group (SSet.KanComplex.π (n + 1)
              (SSet.loopSpace (singularFunctor.obj X) (singularPoint X))
              (originalLoopPoint (singularFunctor.obj X) (singularPoint X)))).toMul
            (SSet.loopConnectingMulEquiv n (singularFunctor.obj X) (singularPoint X))).symm
          (nativeLoopSingularPiMulEquiv n X (cubeSingularMulEquiv n (PointedCGWH.loop.obj X) q))) :=
  rfl

/-- The positive group shift has exactly the same underlying original all-degree cube function. -/
theorem nativeLoopGroupShiftNatIso_hom_eq_allDegree (n : ℕ) (X : PointedCGWH.{u, v})
    (q : PointedCGWH.piN (n + 1) (PointedCGWH.loop.obj X)) :
    ((nativeLoopGroupShiftNatIso n).hom.app X).hom q =
      (nativeLoopPiShiftNatIso (n + 1)).hom.app X q := by
  rw [nativeLoopGroupShiftNatIso_hom_app, nativeLoopPiShiftNatIso_hom_app]
  let K := singularFunctor.obj X
  let x := singularPoint X
  let a : SSet.KanComplex.π (n + 1) (SSet.loopSpace K x) (originalLoopPoint K x) :=
    SSet.KanComplex.π.map (nativeLoopSingularIso X).hom
      (nativeLoopSingularIso_hom_point X) (n + 1)
        (cubeSingularEquiv (n + 1) (PointedCGWH.loop.obj X) q)
  have h := SSet.LoopShiftOriginalGeometry.loopConnectingEquiv_positive n K x
  have hInverse : (loopConnectingEquiv (n + 1) K x).symm a =
      (@MulEquiv.toEquiv (SSet.KanComplex.π (n + 2) K x)
        (SSet.KanComplex.π (n + 1) (SSet.loopSpace K x) (originalLoopPoint K x))
        (inferInstance : Group (SSet.KanComplex.π (n + 2) K x)).toMul
        (inferInstance : Group (SSet.KanComplex.π (n + 1) (SSet.loopSpace K x)
          (originalLoopPoint K x))).toMul (SSet.loopConnectingMulEquiv n K x)).symm a :=
    congrArg (fun e : SSet.KanComplex.π (n + 2) K x ≃
      SSet.KanComplex.π (n + 1) (SSet.loopSpace K x) (originalLoopPoint K x) => e.symm a) h
  exact (congrArg (cubeSingularEquiv (n + 2) X).symm hInverse).symm

/-- Every full original native loop group map retains the entire forward group shift naturality. -/
theorem nativeLoopGroupShiftNatIso_hom_naturality (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.loop ⋙ PointedCGWH.piNPositiveFunctor n).map f ≫
        (nativeLoopGroupShiftNatIso n).hom.app Y =
      (nativeLoopGroupShiftNatIso n).hom.app X ≫ (PointedCGWH.piNPositiveFunctor (n + 1)).map f :=
  (nativeLoopGroupShiftNatIso n).hom.naturality f

/-- Every full original native loop group map retains the entire inverse group shift naturality. -/
theorem nativeLoopGroupShiftNatIso_inv_naturality (n : ℕ)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.piNPositiveFunctor (n + 1)).map f ≫ (nativeLoopGroupShiftNatIso n).inv.app Y =
      (nativeLoopGroupShiftNatIso n).inv.app X ≫
        (PointedCGWH.loop ⋙ PointedCGWH.piNPositiveFunctor n).map f :=
  (nativeLoopGroupShiftNatIso n).inv.naturality f

end PointedCGWH.NativeLoopShiftGeometry
