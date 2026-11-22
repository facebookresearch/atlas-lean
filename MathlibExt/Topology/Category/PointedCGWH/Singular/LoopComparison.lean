/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopConnectingHomotopy
import MathlibExt.Topology.Category.PointedCGWH.Singular.CubeHomotopyComparison
import MathlibExt.Topology.Category.PointedCGWH.LoopHomotopyComparison

/-!
# The whole original native one-sphere loop singular comparison

The actual original `PointedCGWH.loop = ihom sphereOne` is included and
singularized. The genuine original compact-open landing singular Iso and
strict-loop singular Iso give the entire comparison to the original
strict simplicial loop functor. Both whole maps, both original points,
and every complete original pointed-map naturality are preserved.

The raw strict-loop naturality's image-point transport is the exact
original Arrow Iso, with the actual original raw and pointed maps. No
point, loop carrier, group action or stabilization law is supplied.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed Simplicial Topology

namespace PointedCGWH.NativeLoopShiftGeometry

open PointedCGWH.SingularHomotopyGeometry
  (singularFunctor singularPoint singularPoint_naturality)
open PointedCGWH.CubeSingularGeometry (singularFunctorKanComplex)
open SSet.LoopShiftOriginalGeometry (originalLoopPoint)

/-- Equality of the whole original simplicial maps preserves their actual strict loop map. -/
theorem loopSpaceMap_original_eq {X Y : SSet.{v}} {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (f g : X ⟶ Y) (hEq : f = g) (hf : f.app _ x = y) (hg : g.app _ x = y) :
    SSet.loopSpaceMap f hf = SSet.loopSpaceMap g hg := by
  cases hEq
  rfl

/-- The full original strict simplicial loop construction of original
pointed CGWH singular spaces. -/
def strictLoopSingularFunctor : PointedCGWH.{u, v} ⥤ SSet.{v} where
  obj X := SSet.loopSpace (singularFunctor.obj X) (singularPoint X)
  map f := SSet.loopSpaceMap (singularFunctor.map f) (singularPoint_naturality f)
  map_id X :=
    (loopSpaceMap_original_eq _ _ (singularFunctor.map_id X) _ rfl).trans
      SSet.loopSpaceMap_id
  map_comp {X Y Z} f g := by
    have hPoint : (singularFunctor.map f ≫ singularFunctor.map g).app _
        (singularPoint X) = singularPoint Z := by
      change (singularFunctor.map g).app _
        ((singularFunctor.map f).app _ (singularPoint X)) = _
      rw [singularPoint_naturality, singularPoint_naturality]
    exact (loopSpaceMap_original_eq _ _ (singularFunctor.map_comp f g) _ hPoint).trans
      (SSet.loopSpaceMap_comp (singularFunctor.map f) (singularFunctor.map g)
        (singularPoint_naturality f) (singularPoint_naturality g))

/-- Every full strict-loop functor map is the actual original pointed singular strict-loop map. -/
theorem strictLoopSingularFunctor_map {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    strictLoopSingularFunctor.map f =
      SSet.loopSpaceMap (singularFunctor.map f) (singularPoint_naturality f) := rfl

/-- Every original strict-loop map preserves the exact original constant-loop point. -/
theorem strictLoopSingularFunctor_map_point {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (strictLoopSingularFunctor.map f).app _
        (originalLoopPoint (singularFunctor.obj X) (singularPoint X)) =
      originalLoopPoint (singularFunctor.obj Y) (singularPoint Y) :=
  SSet.loopSpaceMap_app_point (singularFunctor.map f) (singularPoint_naturality f)

/-- The whole original one-sphere internal-Hom functor is singularized
on its same native carrier. -/
def nativeLoopSingularFunctor : PointedCGWH.{u, v} ⥤ SSet.{v} :=
  PointedCGWH.loop ⋙ singularFunctor

/-- The exact original native compact-open landing gives its genuine full singular Iso. -/
def landingSingularIso (X : PointedCGWH.{u, v}) : nativeLoopSingularFunctor.obj X ≅
    TopCat.toSSet.obj (TopCat.of
      (LoopSpace (CGWH.cgwhToTop.obj X.right) (PointedCGWH.underlyingBasepoint X))) := by
  let h := PointedCGWH.LoopGeometry.loopLanding_singular_isIso X
  exact @asIso _ _ _ _ (TopCat.toSSet.map (PointedCGWH.loopLanding X)) h

/-- The entire forward landing Iso is the original native compact-open landing singular map. -/
theorem landingSingularIso_hom (X : PointedCGWH.{u, v}) :
    (landingSingularIso X).hom = TopCat.toSSet.map (PointedCGWH.loopLanding X) := rfl

/-- The full landing Iso keeps the same original native chosen point as the reflexive raw loop. -/
theorem landingSingularIso_hom_point (X : PointedCGWH.{u, v}) :
    (landingSingularIso X).hom.app _ (singularPoint (PointedCGWH.loop.obj X)) =
      TopCat.toSSetObj₀Equiv.symm (Path.refl (PointedCGWH.underlyingBasepoint X)) := by
  change TopCat.toSSetObj₀Equiv.symm
      (PointedCGWH.loopLanding X ((PointedCGWH.loop.obj X).hom PUnit.unit)) = _
  exact congrArg TopCat.toSSetObj₀Equiv.symm (PointedCGWH.loopLanding_basepoint X)

/-- The entire actual original native loop carrier has its genuine strict simplicial-loop Iso. -/
def nativeLoopSingularIso (X : PointedCGWH.{u, v}) :
    nativeLoopSingularFunctor.obj X ≅ strictLoopSingularFunctor.obj X :=
  landingSingularIso X ≪≫
    SSet.singularLoopIso (CGWH.cgwhToTop.obj X.right) (PointedCGWH.underlyingBasepoint X)

/-- The forward component is exactly the two original whole comparison maps. -/
theorem nativeLoopSingularIso_hom (X : PointedCGWH.{u, v}) :
    (nativeLoopSingularIso X).hom = (landingSingularIso X).hom ≫
      (SSet.singularLoopIso (CGWH.cgwhToTop.obj X.right)
        (PointedCGWH.underlyingBasepoint X)).hom := rfl

/-- The inverse component is exactly the inverses of the two original whole comparison maps. -/
theorem nativeLoopSingularIso_inv (X : PointedCGWH.{u, v}) :
    (nativeLoopSingularIso X).inv =
      (SSet.singularLoopIso (CGWH.cgwhToTop.obj X.right)
        (PointedCGWH.underlyingBasepoint X)).inv ≫ (landingSingularIso X).inv := rfl

/-- The complete original forward loop Iso preserves the same actual chosen constant-loop point. -/
theorem nativeLoopSingularIso_hom_point (X : PointedCGWH.{u, v}) :
    (nativeLoopSingularIso X).hom.app _ (singularPoint (PointedCGWH.loop.obj X)) =
      originalLoopPoint (singularFunctor.obj X) (singularPoint X) := by
  have hLoop : (SSet.singularLoopIso (CGWH.cgwhToTop.obj X.right)
      (PointedCGWH.underlyingBasepoint X)).hom.app _
        (TopCat.toSSetObj₀Equiv.symm (Path.refl (PointedCGWH.underlyingBasepoint X))) =
      originalLoopPoint (singularFunctor.obj X) (singularPoint X) := by
    rw [SSet.singularLoopIso_hom]
    exact SSet.singularLoopComparison_refl (CGWH.cgwhToTop.obj X.right)
      (PointedCGWH.underlyingBasepoint X)
  exact (congrArg ((SSet.singularLoopIso (CGWH.cgwhToTop.obj X.right)
      (PointedCGWH.underlyingBasepoint X)).hom.app _) (landingSingularIso_hom_point X)).trans hLoop

/-- The entire original inverse loop Iso retains the same chosen native loop basepoint. -/
theorem nativeLoopSingularIso_inv_point (X : PointedCGWH.{u, v}) :
    (nativeLoopSingularIso X).inv.app _
        (originalLoopPoint (singularFunctor.obj X) (singularPoint X)) =
      singularPoint (PointedCGWH.loop.obj X) := by
  rw [← nativeLoopSingularIso_hom_point X]
  change ((nativeLoopSingularIso X).hom ≫ (nativeLoopSingularIso X).inv).app _ _ = _
  rw [Iso.hom_inv_id]
  rfl

/-- The original raw strict loop map retains the actual target-point transport. -/
def rawLoopMapOfPointEq {X Y : TopCat.{v}} (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y) :
    TopCat.of (LoopSpace X x) ⟶ TopCat.of (LoopSpace Y y) :=
  TopCat.ofHom (ContinuousMap.strictLoopMap f.hom x) ≫
    (PointedCGWH.LoopGeometry.loopPointEqIso Y h).hom

/-- The image-point transport is exactly the original whole pointed strict-loop Arrow map. -/
theorem rawLoopMapOfPointEq_eq_original {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    TopCat.ofHom (PointedCGWH.strictLoopMap f) =
      rawLoopMapOfPointEq (CGWH.cgwhToTop.map f.right)
        (PointedCGWH.underlyingBasepoint_naturality f) := by
  have h := Arrow.w ((PointedCGWH.LoopGeometry.rawStrictLoopArrowIso f).hom)
  change (𝟙 _ : TopCat.of (LoopSpace (CGWH.cgwhToTop.obj X.right)
      (PointedCGWH.underlyingBasepoint X)) ⟶ _) ≫ TopCat.ofHom (PointedCGWH.strictLoopMap f) =
    TopCat.ofHom (ContinuousMap.strictLoopMap (CGWH.cgwhToTop.map f.right).hom
        (PointedCGWH.underlyingBasepoint X)) ≫
      (PointedCGWH.LoopGeometry.loopPointEqIso (CGWH.cgwhToTop.obj Y.right)
        (PointedCGWH.underlyingBasepoint_naturality f)).hom at h
  exact (Category.id_comp _).symm.trans h

/-- The entire original raw loop singular Iso has full naturality at the actual chosen points. -/
theorem rawLoopSingularIso_naturality {X Y : TopCat.{v}} (f : X ⟶ Y)
    {x : X} {y : Y} (h : f x = y) :
    TopCat.toSSet.map (rawLoopMapOfPointEq f h) ≫ (SSet.singularLoopIso Y y).hom =
      (SSet.singularLoopIso X x).hom ≫
        SSet.loopSpaceMap (TopCat.toSSet.map f)
          (show (TopCat.toSSet.map f).app _ (TopCat.toSSetObj₀Equiv.symm x) =
              TopCat.toSSetObj₀Equiv.symm y from
            congrArg TopCat.toSSetObj₀Equiv.symm h) := by
  cases h
  change TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.strictLoopMap f.hom x) ≫ 𝟙 _) ≫
      (SSet.singularLoopIso Y (f x)).hom = _
  rw [Category.comp_id]
  exact SSet.singularLoopIso_hom_naturality f.hom x

/-- All entire original pointed maps commute with the full native loop singular Iso. -/
theorem nativeLoopSingularIso_naturality {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    nativeLoopSingularFunctor.map f ≫ (nativeLoopSingularIso Y).hom =
      (nativeLoopSingularIso X).hom ≫ strictLoopSingularFunctor.map f := by
  have hLanding : nativeLoopSingularFunctor.map f ≫ (landingSingularIso Y).hom =
      (landingSingularIso X).hom ≫ TopCat.toSSet.map (TopCat.ofHom (PointedCGWH.strictLoopMap f)) :=
    (TopCat.toSSet.map_comp _ _).symm.trans
      ((congrArg TopCat.toSSet.map (PointedCGWH.loopLanding_naturality f)).trans
        (TopCat.toSSet.map_comp _ _))
  have hStrict : TopCat.toSSet.map (TopCat.ofHom (PointedCGWH.strictLoopMap f)) ≫
      (SSet.singularLoopIso (CGWH.cgwhToTop.obj Y.right)
        (PointedCGWH.underlyingBasepoint Y)).hom =
    (SSet.singularLoopIso (CGWH.cgwhToTop.obj X.right)
      (PointedCGWH.underlyingBasepoint X)).hom ≫ strictLoopSingularFunctor.map f :=
    (congrArg (fun r => TopCat.toSSet.map r ≫
      (SSet.singularLoopIso (CGWH.cgwhToTop.obj Y.right)
        (PointedCGWH.underlyingBasepoint Y)).hom)
          (rawLoopMapOfPointEq_eq_original f)).trans
      (rawLoopSingularIso_naturality (CGWH.cgwhToTop.map f.right)
        (PointedCGWH.underlyingBasepoint_naturality f))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun r => r ≫ (SSet.singularLoopIso (CGWH.cgwhToTop.obj Y.right)
        (PointedCGWH.underlyingBasepoint Y)).hom) hLanding).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun r => (landingSingularIso X).hom ≫ r) hStrict).trans
          (Category.assoc _ _ _).symm)))

/-- The entire original native and strict singular-loop functors have their full natural Iso. -/
def nativeLoopSingularNatIso : nativeLoopSingularFunctor.{u, v} ≅ strictLoopSingularFunctor :=
  NatIso.ofComponents nativeLoopSingularIso (by
    intro X Y f
    exact nativeLoopSingularIso_naturality f)

/-- The full forward natural comparison retains the actual original forward loop map. -/
theorem nativeLoopSingularNatIso_hom_app (X : PointedCGWH.{u, v}) :
    nativeLoopSingularNatIso.hom.app X = (nativeLoopSingularIso X).hom := rfl

/-- The full inverse natural comparison retains the actual original inverse loop map. -/
theorem nativeLoopSingularNatIso_inv_app (X : PointedCGWH.{u, v}) :
    nativeLoopSingularNatIso.inv.app X = (nativeLoopSingularIso X).inv := rfl

/-- Every whole inverse comparison keeps the complete original pointed-map naturality. -/
theorem nativeLoopSingularNatIso_inv_naturality {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    strictLoopSingularFunctor.map f ≫ nativeLoopSingularNatIso.inv.app Y =
      nativeLoopSingularNatIso.inv.app X ≫ nativeLoopSingularFunctor.map f :=
  nativeLoopSingularNatIso.inv.naturality f

end PointedCGWH.NativeLoopShiftGeometry
