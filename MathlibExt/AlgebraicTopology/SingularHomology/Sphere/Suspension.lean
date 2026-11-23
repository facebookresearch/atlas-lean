/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.Sphere
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.Suspension
public import MathlibExt.AlgebraicTopology.SingularHomology.ReducedNatToInt
public import MathlibExt.Topology.Category.TopCat.Suspension.Sphere
import Mathlib.Algebra.Category.Grp.AB

/-!
# Coefficient-generic sphere suspension isomorphisms

Ordinary suspension isomorphisms for spheres with arbitrary additive-group
coefficients, and reduced suspension isomorphisms in any abelian target where
singular homology satisfies excision.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicTopology

variable [UnivLE.{w, u}]

noncomputable local instance sphereSuspensionAddCommGrpAB4OfSize :
    AB4OfSize.{w} AddCommGrpCat.{u} := by
  let _ : HasFilteredColimitsOfSize.{w, w} AddCommGrpCat.{u} :=
    hasFilteredColimitsOfSize_of_univLE
  let _ : UnivLE.{u, u} := inferInstance
  let _ : AB5OfSize.{w, w} AddCommGrpCat.{u} :=
    AB5OfSize_of_univLE.{w, w, u, u} AddCommGrpCat.{u}
  let _ : HasFiniteBiproducts AddCommGrpCat.{u} :=
    Abelian.hasFiniteBiproducts
  exact AB4.of_AB5 AddCommGrpCat.{u}

/-- Ordinary sphere suspension, obtained from the abstract ordinary-homology theorem. -/
noncomputable def sphereSuspensionIso (R : AddCommGrpCat.{u}) (m k : ℕ) (hk : k ≠ 0) :
    ((singularHomologyFunctor.{w, u, u + 1} AddCommGrpCat.{u} (k + 1)).obj R).obj
        (TopCat.sphere.{w} (m + 1)) ≅
      ((singularHomologyFunctor.{w, u, u + 1} AddCommGrpCat.{u} k).obj R).obj
        (TopCat.sphere.{w} m) :=
  ((singularHomologyNatToIntIso.{w, u, u + 1} AddCommGrpCat.{u} R (k + 1)).app
      (TopCat.sphere.{w} (m + 1))).symm ≪≫
    TopPair.OrdinaryHomologyTheory.sphereSuspensionIso
      (singularHomologyIntTheory.{w, u, u + 1} R) m k hk ≪≫
    (singularHomologyNatToIntIso.{w, u, u + 1} AddCommGrpCat.{u} R k).app
      (TopCat.sphere.{w} m)

omit [UnivLE.{w, u}] in
private theorem eqToIso_hom_naturality
    {C : Type u} [Category.{v} C]
    {A B : ℤ → C} (f : ∀ z, A z ⟶ B z)
    {i j : ℤ} (h : i = j) :
    f i ≫ (eqToIso (congrArg B h)).hom =
      (eqToIso (congrArg A h)).hom ≫ f j := by
  subst j
  simp

omit [UnivLE.{w, u}] in
/-- Reduced sphere suspension: `H̃_{k+1}(S^{m+1}; R) ≅ H̃_k(S^m; R)`, uniformly in
`k`, in any abelian target where singular homology satisfies excision. -/
noncomputable def reducedSphereSuspensionIso
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] [AB4OfSize.{w} C]
    (R : C)
    [hExcisive : (singularHomologyIntData.{w, v, u} C R :
      TopPair.HomologyTheoryData.{w} C).IsExcisive]
    (m k : ℕ) :
    reducedSingularHomology.{w, v, u} C R (k + 1) (TopCat.sphere.{w} (m + 1)) ≅
      reducedSingularHomology.{w, v, u} C R k (TopCat.sphere.{w} m) := by
  let E := singularHomologyIntTheory.{w, v, u} (C := C) R
  let X := TopCat.pointedSphere.{w} m
  let Y := TopCat.pointedSphere.{w} (m + 1)
  let e := TopCat.suspensionSpherePointedIso.{w} m
  let n : ℤ := ((k + 1 : ℕ) : ℤ)
  have h : n - 1 = (k : ℤ) := by omega
  let degreeIso := eqToIso (congrArg (fun z => (E.reducedH z).obj X) h)
  simpa [X, Y, TopCat.pointedSphere] using
    ((reducedSingularHomologyNatToIntIso.{w, u, v} C R (k + 1)).app Y ≪≫
      ((E.reducedH n).mapIso e).symm ≪≫
      (E.reducedSuspensionNatIso n).app X ≪≫ degreeIso ≪≫
      ((reducedSingularHomologyNatToIntIso.{w, u, v} C R k).app X).symm)

set_option backward.isDefEq.respectTransparency false in
omit [UnivLE.{w, u}] in
/-- The reduced sphere suspension isomorphism is natural in the coefficient object. -/
theorem reducedSphereSuspensionIso_hom_naturality_coefficient
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] [AB4OfSize.{w} C]
    (hExcisive : ∀ A : C, (singularHomologyIntData.{w, v, u} C A :
      TopPair.HomologyTheoryData.{w} C).IsExcisive)
    {R S : C} (a : R ⟶ S) (m k : ℕ) :
    ((reducedSingularHomologyCoefficientFunctor.{w, v, u} C (k + 1)).map a).app
          (TopCat.sphere.{w} (m + 1)) ≫
        (reducedSphereSuspensionIso (C := C) S
          (hExcisive := hExcisive S) m k).hom =
      (reducedSphereSuspensionIso (C := C) R
        (hExcisive := hExcisive R) m k).hom ≫
        ((reducedSingularHomologyCoefficientFunctor.{w, v, u} C k).map a).app
          (TopCat.sphere.{w} m) := by
  let T := singularHomologyIntTheoryFunctor.{w, v, u} (C := C) hExcisive
  let E := singularHomologyIntTheory.{w, v, u} (C := C) R
  let F := singularHomologyIntTheory.{w, v, u} (C := C) S
  let X := TopCat.pointedSphere.{w} m
  let Y := TopCat.pointedSphere.{w} (m + 1)
  let e := TopCat.suspensionSpherePointedIso.{w} m
  let n : ℤ := ((k + 1 : ℕ) : ℤ)
  have h : n - 1 = (k : ℤ) := by omega
  let reducedSourceMap :=
    ((reducedSingularHomologyCoefficientFunctor.{w, v, u} C (k + 1)).map a).app Y.right
  let reducedTargetMap :=
    ((reducedSingularHomologyCoefficientFunctor.{w, v, u} C k).map a).app X.right
  let theorySourceMap : (E.reducedH n).obj Y ⟶ (F.reducedH n).obj Y :=
    (((T.map a).hom.homₚ n).app (PointedTopCat.pointedPair.obj Y))
  let theorySuspensionMap :
      (E.reducedH n).obj
          ((Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor).obj X) ⟶
        (F.reducedH n).obj
          ((Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor).obj X) :=
    (((T.map a).hom.homₚ n).app
      ((Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙
        PointedTopCat.pointedPair).obj X))
  let theoryBeforeDegreeMap :
      (E.reducedH (n - 1)).obj X ⟶ (F.reducedH (n - 1)).obj X :=
    (((T.map a).hom.homₚ (n - 1)).app (PointedTopCat.pointedPair.obj X))
  let theoryTargetMap :
      (E.reducedH (k : ℤ)).obj X ⟶ (F.reducedH (k : ℤ)).obj X :=
    (((T.map a).hom.homₚ (k : ℤ)).app (PointedTopCat.pointedPair.obj X))
  let sourceR := reducedSingularHomologyNatToIntObjIso C R (k + 1) Y
  let sourceS := reducedSingularHomologyNatToIntObjIso C S (k + 1) Y
  let targetR := reducedSingularHomologyNatToIntObjIso C R k X
  let targetS := reducedSingularHomologyNatToIntObjIso C S k X
  let sphereMapR := (((E.reducedH n).mapIso e).symm).hom
  let sphereMapS := (((F.reducedH n).mapIso e).symm).hom
  let suspensionMapR := (E.reducedSuspensionNatIso n).hom.app X
  let suspensionMapS := (F.reducedSuspensionNatIso n).hom.app X
  let degreeMapR := (eqToIso (congrArg (fun z => (E.reducedH z).obj X) h)).hom
  let degreeMapS := (eqToIso (congrArg (fun z => (F.reducedH z).obj X) h)).hom
  have hSource : reducedSourceMap ≫ sourceS.hom = sourceR.hom ≫ theorySourceMap := by
    simpa [reducedSourceMap, sourceR, sourceS, theorySourceMap, T, E, F, Y, n] using
      reducedSingularHomologyNatToIntIso_hom_naturality_coefficient
        C a (k + 1) Y
  have hSphere : theorySourceMap ≫ sphereMapS = sphereMapR ≫ theorySuspensionMap := by
    exact (((T.map a).hom.homₚ n).naturality
      (PointedTopCat.pointedPair.map e.inv)).symm
  have hSuspension : theorySuspensionMap ≫ suspensionMapS =
      suspensionMapR ≫ theoryBeforeDegreeMap :=
    TopPair.OrdinaryHomologyTheory.reducedSuspensionNatIso_hom_naturality_theory
      (T.map a) n X
  have hDegree : theoryBeforeDegreeMap ≫ degreeMapS =
      degreeMapR ≫ theoryTargetMap := by
    exact eqToIso_hom_naturality
      (fun z => (((T.map a).hom.homₚ z).app (PointedTopCat.pointedPair.obj X))) h
  have hTarget : reducedTargetMap ≫ targetS.hom =
      targetR.hom ≫ theoryTargetMap := by
    simpa [reducedTargetMap, targetR, targetS, theoryTargetMap, T, E, F, X] using
      reducedSingularHomologyNatToIntIso_hom_naturality_coefficient
        C a k X
  have hTargetInv : theoryTargetMap ≫ targetS.inv =
      targetR.inv ≫ reducedTargetMap := by
    apply (cancel_epi targetR.hom).mp
    rw [← Category.assoc, ← hTarget]
    simp
  change reducedSourceMap ≫ (reducedSphereSuspensionIso (C := C) S
      (hExcisive := hExcisive S) m k).hom =
    (reducedSphereSuspensionIso (C := C) R
      (hExcisive := hExcisive R) m k).hom ≫ reducedTargetMap
  rw [show (reducedSphereSuspensionIso (C := C) S
      (hExcisive := hExcisive S) m k).hom =
      sourceS.hom ≫ sphereMapS ≫ suspensionMapS ≫ degreeMapS ≫ targetS.inv by
    simp [reducedSphereSuspensionIso, sourceS, sphereMapS, suspensionMapS, degreeMapS,
      targetS, F, Y, X, e, n, TopCat.pointedSphere]]
  rw [show (reducedSphereSuspensionIso (C := C) R
      (hExcisive := hExcisive R) m k).hom =
      sourceR.hom ≫ sphereMapR ≫ suspensionMapR ≫ degreeMapR ≫ targetR.inv by
    simp [reducedSphereSuspensionIso, sourceR, sphereMapR, suspensionMapR, degreeMapR,
      targetR, E, Y, X, e, n, TopCat.pointedSphere]]
  calc
    reducedSourceMap ≫
        (sourceS.hom ≫ sphereMapS ≫ suspensionMapS ≫ degreeMapS ≫ targetS.inv) =
      (reducedSourceMap ≫ sourceS.hom) ≫ sphereMapS ≫ suspensionMapS ≫
        degreeMapS ≫ targetS.inv := by
      simp only [Category.assoc]
    _ = (sourceR.hom ≫ theorySourceMap) ≫ sphereMapS ≫ suspensionMapS ≫
        degreeMapS ≫ targetS.inv := by
      rw [hSource]
    _ = sourceR.hom ≫ (theorySourceMap ≫ sphereMapS) ≫ suspensionMapS ≫
        degreeMapS ≫ targetS.inv := by
      simp only [Category.assoc]
    _ = sourceR.hom ≫ (sphereMapR ≫ theorySuspensionMap) ≫ suspensionMapS ≫
        degreeMapS ≫ targetS.inv := by
      rw [hSphere]
    _ = sourceR.hom ≫ sphereMapR ≫ (theorySuspensionMap ≫ suspensionMapS) ≫
        degreeMapS ≫ targetS.inv := by
      simp only [Category.assoc]
    _ = sourceR.hom ≫ sphereMapR ≫ (suspensionMapR ≫ theoryBeforeDegreeMap) ≫
        degreeMapS ≫ targetS.inv := by
      rw [hSuspension]
    _ = sourceR.hom ≫ sphereMapR ≫ suspensionMapR ≫
        (theoryBeforeDegreeMap ≫ degreeMapS) ≫ targetS.inv := by
      simp only [Category.assoc]
    _ = sourceR.hom ≫ sphereMapR ≫ suspensionMapR ≫
        (degreeMapR ≫ theoryTargetMap) ≫ targetS.inv := by
      rw [hDegree]
    _ = sourceR.hom ≫ sphereMapR ≫ suspensionMapR ≫ degreeMapR ≫
        (theoryTargetMap ≫ targetS.inv) := by
      simp only [Category.assoc]
    _ = sourceR.hom ≫ sphereMapR ≫ suspensionMapR ≫ degreeMapR ≫
        (targetR.inv ≫ reducedTargetMap) := by
      rw [hTargetInv]
    _ = (sourceR.hom ≫ sphereMapR ≫ suspensionMapR ≫ degreeMapR ≫ targetR.inv) ≫
        reducedTargetMap := by
      simp only [Category.assoc]

/-- Reduced sphere suspension, natural in the coefficient object. -/
noncomputable def reducedSphereSuspensionCoefficientNatIso (m k : ℕ) :
    reducedSingularHomologyCoefficientFunctor.{w, u, u + 1}
          AddCommGrpCat.{u} (k + 1) ⋙
        (evaluation TopCat.{w} AddCommGrpCat.{u}).obj
          (TopCat.sphere.{w} (m + 1)) ≅
      reducedSingularHomologyCoefficientFunctor.{w, u, u + 1}
          AddCommGrpCat.{u} k ⋙
        (evaluation TopCat.{w} AddCommGrpCat.{u}).obj
          (TopCat.sphere.{w} m) :=
  NatIso.ofComponents
    (fun R => reducedSphereSuspensionIso R m k)
    (fun {_ _} a => reducedSphereSuspensionIso_hom_naturality_coefficient
      (C := AddCommGrpCat.{u}) (fun _ => inferInstance) a m k)

end AlgebraicTopology
