/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.ReducedCoefficientFunctor
public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeCoefficientFunctor
public import MathlibExt.Topology.Category.PointedTopCat
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.Reduced
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerTheory
public import MathlibExt.AlgebraicTopology.SingularHomology.ReducedNatToInt

/-!
# Pointed relative and reduced singular homology

Kernel-defined reduced singular homology is canonically isomorphic to the
relative singular homology of the pointed pair.  The proof compares both
models with the kernel of the terminal map in integer-graded singular
homology, so it applies uniformly in degree zero.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]


set_option backward.isDefEq.respectTransparency false in
private noncomputable def pointedRelativeReducedKernelNatToIntIso
    (R : C) (n : ℕ) (X : PointedTopCat.{w}) :
    kernel ((singularHomologyIntFunctor C R (n : ℤ)).map
      (TopCat.isTerminalPUnit.from X.right)) ≅
      kernel ((singularHomologyAugmentation C R n).app X.right) :=
  kernel.mapIso
    (f := (singularHomologyIntFunctor C R (n : ℤ)).map
      (TopCat.isTerminalPUnit.from X.right))
    ((singularHomologyAugmentation C R n).app X.right)
    ((singularHomologyNatToIntIso C R n).app X.right)
    (show (singularHomologyIntFunctor C R (n : ℤ)).obj (TopCat.of PUnit) ≅
        (pointSingularHomologyFunctor C R n).obj X.right from
      (singularHomologyNatToIntIso C R n).app (TopCat.of PUnit))
    ((singularHomologyNatToIntIso C R n).hom.naturality
      (TopCat.isTerminalPUnit.from X.right))

private noncomputable def pointedRelativeReducedIntegerIso
    (R : C) (n : ℕ) (X : PointedTopCat.{w}) :
    reducedSingularHomology C R n X.right ≅
      ((singularHomologyIntData C R).reducedH (n : ℤ)).obj X :=
  (reducedSingularHomologyObjIso C R n X.right ≪≫
    (pointedRelativeReducedKernelNatToIntIso C R n X).symm) ≪≫
    (TopPair.HomologyTheoryData.IsExact.reducedHKernelIsoToPoint
      (singularHomologyIntData C R) (n : ℤ) X).symm

set_option backward.isDefEq.respectTransparency false in
private theorem pointedRelativeReducedIntegerIso_hom_comp_reducedToPointedH
    (R : C) (n : ℕ) (X : PointedTopCat.{w}) :
    (pointedRelativeReducedIntegerIso C R n X).hom ≫
        (TopPair.HomologyTheoryData.IsExact.reducedToPointedH
          (singularHomologyIntData C R) (n : ℤ)).app X =
      (reducedSingularHomologyι C R n).app X.right ≫
        (singularHomologyNatToIntIso C R n).inv.app X.right := by
  let e0 := reducedSingularHomologyObjIso C R n X.right
  let eAbs := (singularHomologyNatToIntIso C R n).app X.right
  let ePoint :=
    (singularHomologyNatToIntIso C R n).app (TopCat.of PUnit)
  let aInt := (singularHomologyIntFunctor C R (n : ℤ)).map
    (TopCat.isTerminalPUnit.from X.right)
  let aNat := (singularHomologyAugmentation C R n).app X.right
  let e1 := pointedRelativeReducedKernelNatToIntIso C R n X
  let e2 : ((singularHomologyIntData C R).reducedH (n : ℤ)).obj X ≅
      kernel aInt :=
    TopPair.HomologyTheoryData.IsExact.reducedHKernelIsoToPoint
      (singularHomologyIntData C R) (n : ℤ) X
  let j : ((singularHomologyIntData C R).reducedH (n : ℤ)).obj X ⟶
      (singularHomologyIntFunctor C R (n : ℤ)).obj X.right :=
    (TopPair.HomologyTheoryData.IsExact.reducedToPointedH
      (singularHomologyIntData C R) (n : ℤ)).app X
  have h2 : e2.inv ≫ j = kernel.ι aInt := by
    apply e2.inv_comp_eq.mpr
    change j = e2.hom ≫ kernel.ι aInt
    exact
      (TopPair.HomologyTheoryData.IsExact.reducedHKernelIsoToPoint_hom_ι
        (singularHomologyIntData C R) (n : ℤ) X).symm
  have h0 : e0.hom ≫ kernel.ι aNat =
      (reducedSingularHomologyι C R n).app X.right :=
    reducedSingularHomologyObjIso_hom_ι C R n X.right
  have h1hom : e1.hom ≫ kernel.ι aNat =
      kernel.ι aInt ≫ eAbs.hom := by
    dsimp only [e1, pointedRelativeReducedKernelNatToIntIso]
    simp only [kernel.mapIso_hom, kernel.map]
    rw [kernel.lift_ι]
  have h1inv : e1.inv ≫ kernel.ι aInt =
      kernel.ι aNat ≫ eAbs.inv := by
    apply (cancel_epi e1.hom).mp
    calc
      e1.hom ≫ (e1.inv ≫ kernel.ι aInt) =
          kernel.ι aInt := by simp
      _ = (kernel.ι aInt ≫ eAbs.hom) ≫ eAbs.inv := by simp
      _ = (e1.hom ≫ kernel.ι aNat) ≫ eAbs.inv := by rw [h1hom]
      _ = e1.hom ≫ (kernel.ι aNat ≫ eAbs.inv) := by
        simp only [Category.assoc]
  change (((e0 ≪≫ e1.symm) ≪≫ e2.symm).hom ≫ j) = _
  simp only [Iso.trans_hom, Iso.symm_hom]
  erw [Category.assoc, h2]
  rw [Category.assoc, h1inv, ← Category.assoc, h0]
  rfl

private noncomputable def pointedRelativeReducedSingularHomologyIso
    (R : C) (n : ℕ) (X : PointedTopCat.{w}) :
    reducedSingularHomology C R n X.right ≅
      (relativeSingularHomologyFunctor C R n).obj
        (PointedTopCat.pointedPair.obj X) :=
  pointedRelativeReducedIntegerIso C R n X ≪≫
    (relativeSingularHomologyNatToIntIso C R n).app
      (PointedTopCat.pointedPair.obj X)

set_option backward.isDefEq.respectTransparency false in
private theorem pointedRelativeReducedSingularHomologyIso_hom
    (R : C) (n : ℕ) (X : PointedTopCat.{w}) :
    (pointedRelativeReducedSingularHomologyIso C R n X).hom =
      (reducedSingularHomologyι C R n).app X.right ≫
        HomologicalComplex.homologyMap
          (relativeSingularChainQuotient C R
            (PointedTopCat.pointedPair.obj X)) n := by
  let E := singularHomologyIntData C R
  let P := PointedTopCat.pointedPair.obj X
  let k := pointedRelativeReducedIntegerIso C R n X
  let eAbs := (singularHomologyNatToIntIso C R n).app X.right
  let eRel := (relativeSingularHomologyNatToIntIso C R n).app P
  let j := (TopPair.HomologyTheoryData.IsExact.reducedToPointedH
    E (n : ℤ)).app X
  let t := E.toRelative (n : ℤ) P
  have hk : k.hom ≫ j =
      (reducedSingularHomologyι C R n).app X.right ≫ eAbs.inv :=
    pointedRelativeReducedIntegerIso_hom_comp_reducedToPointedH C R n X
  have hj : j ≫ t = 𝟙 ((E.reducedH (n : ℤ)).obj X) :=
    TopPair.HomologyTheoryData.IsExact.reducedToPointedH_app_comp_toRelative
      E (n : ℤ) X
  have hq : eAbs.inv ≫ t ≫ eRel.hom =
      HomologicalComplex.homologyMap
        (relativeSingularChainQuotient C R P) n :=
    singularHomologyIntData_toRelative_natAgreement C R n P
  change k.hom ≫ eRel.hom = _
  calc
    k.hom ≫ eRel.hom =
        k.hom ≫ 𝟙 _ ≫ eRel.hom := by simp
    _ = k.hom ≫ (j ≫ t) ≫ eRel.hom := by rw [hj]
    _ = (k.hom ≫ j) ≫ t ≫ eRel.hom := by
      simp only [Category.assoc]
    _ = ((reducedSingularHomologyι C R n).app X.right ≫
          eAbs.inv) ≫ t ≫ eRel.hom := by rw [hk]
    _ = (reducedSingularHomologyι C R n).app X.right ≫
        (eAbs.inv ≫ t ≫ eRel.hom) := by
      simp only [Category.assoc]
    _ = (reducedSingularHomologyι C R n).app X.right ≫
        HomologicalComplex.homologyMap
          (relativeSingularChainQuotient C R P) n := by rw [hq]

set_option backward.isDefEq.respectTransparency false in
/-- Kernel-defined reduced singular homology is naturally isomorphic to
relative singular homology of the pointed pair. -/
noncomputable def pointedRelativeReducedSingularHomologyNatIso
    (R : C) (n : ℕ) :
    Under.forget (TopCat.of PUnit) ⋙
        reducedSingularHomologyFunctor C R n ≅
      PointedTopCat.pointedPair ⋙
        relativeSingularHomologyFunctor C R n := by
  let q : TopPair.proj₁ ⋙ (singularHomologyFunctor C n).obj R ⟶
      relativeSingularHomologyFunctor C R n := by
    change (TopPair.proj₁ ⋙ (singularChainComplexFunctor C).obj R) ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n ⟶
      relativeSingularChainFunctor C R ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n
    exact Functor.whiskerRight (relativeSingularChainQuotientNatTrans C R)
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n)
  let α : Under.forget (TopCat.of PUnit) ⋙
        reducedSingularHomologyFunctor C R n ⟶
      PointedTopCat.pointedPair ⋙
        relativeSingularHomologyFunctor C R n :=
    Functor.whiskerLeft (Under.forget (TopCat.of PUnit))
        (reducedSingularHomologyι C R n) ≫
      Functor.whiskerLeft PointedTopCat.pointedPair q
  letI (X : PointedTopCat.{w}) : IsIso (α.app X) := by
    have h : (pointedRelativeReducedSingularHomologyIso C R n X).hom =
        α.app X :=
      pointedRelativeReducedSingularHomologyIso_hom C R n X
    rw [← h]
    infer_instance
  exact NatIso.ofComponents (fun X => asIso (α.app X))
    (fun f => α.naturality f)

/-- The forward component is the reduced inclusion followed by the canonical
absolute-to-relative quotient map on homology. -/
@[simp]
theorem pointedRelativeReducedSingularHomologyNatIso_hom_app
    (R : C) (n : ℕ) (X : PointedTopCat.{w}) :
    (pointedRelativeReducedSingularHomologyNatIso C R n).hom.app X =
      (reducedSingularHomologyι C R n).app X.right ≫
        HomologicalComplex.homologyMap
          (relativeSingularChainQuotient C R
            (PointedTopCat.pointedPair.obj X)) n :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse pointed relative/reduced comparison first returns to relative
integer grading and then uses the inverse reduced Nat-to-Int coordinate. -/
@[simp]
theorem pointedRelativeReducedSingularHomologyNatIso_inv_app
    (R : C) [AB4OfSize.{w} C]
    [(singularHomologyIntData C R :
      TopPair.HomologyTheoryData.{w} C).IsExcisive]
    (n : ℕ) (X : PointedTopCat.{w}) :
    (pointedRelativeReducedSingularHomologyNatIso C R n).inv.app X =
      (relativeSingularHomologyNatToIntIso C R n).inv.app
          (PointedTopCat.pointedPair.obj X) ≫
        (reducedSingularHomologyNatToIntObjIso C R n X).inv := by
  let eNat :=
    (pointedRelativeReducedSingularHomologyNatIso C R n).app X
  let eCore := pointedRelativeReducedSingularHomologyIso C R n X
  let eRed := reducedSingularHomologyNatToIntObjIso C R n X
  let eRel := (relativeSingularHomologyNatToIntIso C R n).app
    (PointedTopCat.pointedPair.obj X)
  let j := (TopPair.HomologyTheoryData.IsExact.reducedToPointedH
    (singularHomologyIntData C R) (n : ℤ)).app X
  let _ : Mono j := by
    dsimp only [j,
      TopPair.HomologyTheoryData.IsExact.reducedToPointedH]
    infer_instance
  have hNatCore : eNat = eCore := by
    apply Iso.ext
    change
      (pointedRelativeReducedSingularHomologyNatIso C R n).hom.app X =
        (pointedRelativeReducedSingularHomologyIso C R n X).hom
    exact
      (pointedRelativeReducedSingularHomologyNatIso_hom_app C R n X).trans
        (pointedRelativeReducedSingularHomologyIso_hom C R n X).symm
  have hIntegerHom :
      (pointedRelativeReducedIntegerIso C R n X).hom = eRed.hom := by
    apply (cancel_mono j).1
    dsimp only [j]
    exact
      (pointedRelativeReducedIntegerIso_hom_comp_reducedToPointedH
        C R n X).trans
        (reducedSingularHomologyNatToIntObjIso_hom_comp_reducedToPointedH
          C R n X).symm
  have hInteger :
      pointedRelativeReducedIntegerIso C R n X = eRed :=
    Iso.ext hIntegerHom
  have hCoreRed : eCore = eRed ≪≫ eRel := by
    dsimp only [eCore, eRel,
      pointedRelativeReducedSingularHomologyIso]
    rw [hInteger]
  change eNat.inv = eRel.inv ≫ eRed.inv
  rw [hNatCore, hCoreRed]
  rfl

private theorem singularHomologyNatToIntIso_inv_naturality_coefficient
    {R S : C} (a : R ⟶ S) (n : ℕ) (X : TopCat.{w}) :
    ((singularHomologyFunctor C n).map a).app X ≫
        (singularHomologyNatToIntIso C S n).inv.app X =
      (singularHomologyNatToIntIso C R n).inv.app X ≫
        ((singularHomologyIntCoefficientFunctor
          (C := C) (n : ℤ)).map a).app X := by
  let eR := (singularHomologyNatToIntIso C R n).app X
  let eS := (singularHomologyNatToIntIso C S n).app X
  let fInt := ((singularHomologyIntCoefficientFunctor
    (C := C) (n : ℤ)).map a).app X
  let fNat := ((singularHomologyFunctor C n).map a).app X
  have h : fInt ≫ eS.hom = eR.hom ≫ fNat :=
    homologyIso_extendDownNatToInt_naturality
      (((singularChainComplexFunctor C).map a).app X) n
  apply (cancel_epi eR.hom).mp
  rw [← Category.assoc, ← h]
  dsimp only [eR, eS, fInt]
  simp

private theorem relativeSingularHomologyNatToIntIso_hom_naturality_coefficient
    {R S : C} (a : R ⟶ S) (n : ℕ) (P : TopPair.{w}) :
    ((relativeSingularHomologyIntCoefficientFunctor
        (C := C) (n : ℤ)).map a).app P ≫
        (relativeSingularHomologyNatToIntIso C S n).hom.app P =
      (relativeSingularHomologyNatToIntIso C R n).hom.app P ≫
        ((relativeSingularHomologyCoefficientFunctor
          (C := C) n).map a).app P := by
  exact homologyIso_extendDownNatToInt_naturality
    (((relativeSingularChainComplexFunctor (C := C)).map a).app P) n

set_option backward.isDefEq.respectTransparency false in
private theorem pointedRelativeReducedIntegerIso_hom_naturality_coefficient
    {R S : C} (a : R ⟶ S) (n : ℕ) (X : PointedTopCat.{w}) :
    ((reducedSingularHomologyCoefficientFunctor C n).map a).app X.right ≫
        (pointedRelativeReducedIntegerIso C S n X).hom =
      (pointedRelativeReducedIntegerIso C R n X).hom ≫
        ((relativeSingularHomologyIntCoefficientFunctor
          (C := C) (n : ℤ)).map a).app
            (PointedTopCat.pointedPair.obj X) := by
  let P := PointedTopCat.pointedPair.obj X
  let E_R := singularHomologyIntData C R
  let E_S := singularHomologyIntData C S
  let φ := singularHomologyIntDataHom C a
  let redMap :=
    ((reducedSingularHomologyCoefficientFunctor C n).map a).app X.right
  let natMap := ((singularHomologyFunctor C n).map a).app X.right
  let natPointMap :=
    ((singularHomologyFunctor C n).map a).app (TopCat.of PUnit)
  let intMap := ((singularHomologyIntCoefficientFunctor
    (C := C) (n : ℤ)).map a).app X.right
  let intPointMap := ((singularHomologyIntCoefficientFunctor
    (C := C) (n : ℤ)).map a).app (TopCat.of PUnit)
  let intRelMap := ((relativeSingularHomologyIntCoefficientFunctor
    (C := C) (n : ℤ)).map a).app P
  let aNatR := (singularHomologyAugmentation C R n).app X.right
  let aNatS := (singularHomologyAugmentation C S n).app X.right
  let aIntR := (singularHomologyIntFunctor C R (n : ℤ)).map
    (TopCat.isTerminalPUnit.from X.right)
  let aIntS := (singularHomologyIntFunctor C S (n : ℤ)).map
    (TopCat.isTerminalPUnit.from X.right)
  have hNatAug : aNatR ≫ natPointMap = natMap ≫ aNatS := by
    exact (congr_app
      ((singularHomologyAugmentationCoefficient C n).naturality a)
      X.right).symm
  have hIntAug : aIntR ≫ intPointMap = intMap ≫ aIntS := by
    exact (φ.hom (n : ℤ)).naturality
      (TopCat.isTerminalPUnit.from X.right)
  let kernelNatMap := kernel.map aNatR aNatS natMap natPointMap hNatAug
  let kernelIntMap := kernel.map aIntR aIntS intMap intPointMap hIntAug
  let e0R := reducedSingularHomologyObjIso C R n X.right
  let e0S := reducedSingularHomologyObjIso C S n X.right
  let eAbsR := (singularHomologyNatToIntIso C R n).app X.right
  let eAbsS := (singularHomologyNatToIntIso C S n).app X.right
  let ePointR :=
    (singularHomologyNatToIntIso C R n).app (TopCat.of PUnit)
  let ePointS :=
    (singularHomologyNatToIntIso C S n).app (TopCat.of PUnit)
  let e1R : kernel aIntR ≅ kernel aNatR :=
    kernel.mapIso (f := aIntR) aNatR eAbsR ePointR
      ((singularHomologyNatToIntIso C R n).hom.naturality
        (TopCat.isTerminalPUnit.from X.right))
  let e1S : kernel aIntS ≅ kernel aNatS :=
    kernel.mapIso (f := aIntS) aNatS eAbsS ePointS
      ((singularHomologyNatToIntIso C S n).hom.naturality
        (TopCat.isTerminalPUnit.from X.right))
  let e2R := TopPair.HomologyTheoryData.IsExact.reducedHKernelIsoToPoint
    E_R (n : ℤ) X
  let e2S := TopPair.HomologyTheoryData.IsExact.reducedHKernelIsoToPoint
    E_S (n : ℤ) X
  have h0 : redMap ≫ e0S.hom = e0R.hom ≫ kernelNatMap := by
    apply (cancel_mono (kernel.ι aNatS)).mp
    calc
      (redMap ≫ e0S.hom) ≫ kernel.ι aNatS =
          redMap ≫ (e0S.hom ≫ kernel.ι aNatS) := by
        simp only [Category.assoc]
      _ = redMap ≫ (reducedSingularHomologyι C S n).app X.right := by
        rw [reducedSingularHomologyObjIso_hom_ι]
      _ = (reducedSingularHomologyι C R n).app X.right ≫ natMap := by
        exact congr_app
          (reducedSingularHomologyCoefficientMap_comp_ι C n a) X.right
      _ = (e0R.hom ≫ kernel.ι aNatR) ≫ natMap := by
        rw [reducedSingularHomologyObjIso_hom_ι]
      _ = e0R.hom ≫ (kernel.ι aNatR ≫ natMap) := by
        simp only [Category.assoc]
      _ = e0R.hom ≫ (kernelNatMap ≫ kernel.ι aNatS) := by
        dsimp only [kernelNatMap, kernel.map]
        rw [kernel.lift_ι]
      _ = (e0R.hom ≫ kernelNatMap) ≫ kernel.ι aNatS := by
        simp only [Category.assoc]
  have hAbs : natMap ≫ eAbsS.inv = eAbsR.inv ≫ intMap :=
    singularHomologyNatToIntIso_inv_naturality_coefficient C a n X.right
  have h1R : e1R.inv ≫ kernel.ι aIntR =
      kernel.ι aNatR ≫ eAbsR.inv := by
    dsimp only [e1R]
    simp only [kernel.mapIso_inv, kernel.map, kernel.lift_ι]
  have h1S : e1S.inv ≫ kernel.ι aIntS =
      kernel.ι aNatS ≫ eAbsS.inv := by
    dsimp only [e1S]
    simp only [kernel.mapIso_inv, kernel.map, kernel.lift_ι]
  have h1 : kernelNatMap ≫ e1S.inv =
      e1R.inv ≫ kernelIntMap := by
    apply (cancel_mono (kernel.ι aIntS)).mp
    calc
      (kernelNatMap ≫ e1S.inv) ≫ kernel.ι aIntS =
          kernelNatMap ≫ (e1S.inv ≫ kernel.ι aIntS) := by
        simp only [Category.assoc]
      _ = kernelNatMap ≫ (kernel.ι aNatS ≫ eAbsS.inv) := by
        rw [h1S]
      _ = (kernelNatMap ≫ kernel.ι aNatS) ≫ eAbsS.inv := by
        simp only [Category.assoc]
      _ = (kernel.ι aNatR ≫ natMap) ≫ eAbsS.inv := by
        dsimp only [kernelNatMap, kernel.map]
        rw [kernel.lift_ι]
      _ = kernel.ι aNatR ≫ (natMap ≫ eAbsS.inv) := by
        simp only [Category.assoc]
      _ = kernel.ι aNatR ≫ (eAbsR.inv ≫ intMap) := by
        rw [hAbs]
      _ = (kernel.ι aNatR ≫ eAbsR.inv) ≫ intMap := by
        simp only [Category.assoc]
      _ = (e1R.inv ≫ kernel.ι aIntR) ≫ intMap := by
        rw [h1R]
      _ = e1R.inv ≫ (kernel.ι aIntR ≫ intMap) := by
        simp only [Category.assoc]
      _ = e1R.inv ≫ (kernelIntMap ≫ kernel.ι aIntS) := by
        dsimp only [kernelIntMap, kernel.map]
        rw [kernel.lift_ι]
      _ = (e1R.inv ≫ kernelIntMap) ≫ kernel.ι aIntS := by
        simp only [Category.assoc]
  have h2hom : e2R.hom ≫ kernelIntMap =
      intRelMap ≫ e2S.hom := by
    exact TopPair.HomologyTheoryData.IsExact.reducedHKernelIsoToPoint_hom_naturality_theory
      φ (n : ℤ) X
  have h2 : kernelIntMap ≫ e2S.inv = e2R.inv ≫ intRelMap := by
    apply (cancel_epi e2R.hom).mp
    rw [← Category.assoc, h2hom]
    simp
  change redMap ≫ ((e0S.hom ≫ e1S.inv) ≫ e2S.inv) =
    ((e0R.hom ≫ e1R.inv) ≫ e2R.inv) ≫ intRelMap
  calc
    redMap ≫ ((e0S.hom ≫ e1S.inv) ≫ e2S.inv) =
        ((redMap ≫ e0S.hom) ≫ e1S.inv) ≫ e2S.inv := by
      simp only [Category.assoc]
    _ = ((e0R.hom ≫ kernelNatMap) ≫ e1S.inv) ≫ e2S.inv := by
      rw [h0]
    _ = (e0R.hom ≫ (kernelNatMap ≫ e1S.inv)) ≫ e2S.inv := by
      simp only [Category.assoc]
    _ = (e0R.hom ≫ (e1R.inv ≫ kernelIntMap)) ≫ e2S.inv := by
      rw [h1]
    _ = (e0R.hom ≫ e1R.inv) ≫ (kernelIntMap ≫ e2S.inv) := by
      simp only [Category.assoc]
    _ = (e0R.hom ≫ e1R.inv) ≫ (e2R.inv ≫ intRelMap) := by
      rw [h2]
    _ = ((e0R.hom ≫ e1R.inv) ≫ e2R.inv) ≫ intRelMap := by
      simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem pointedRelativeReducedSingularHomologyIso_hom_naturality_coefficient
    {R S : C} (a : R ⟶ S) (n : ℕ) (X : PointedTopCat.{w}) :
    ((reducedSingularHomologyCoefficientFunctor C n).map a).app X.right ≫
        (pointedRelativeReducedSingularHomologyIso C S n X).hom =
      (pointedRelativeReducedSingularHomologyIso C R n X).hom ≫
        ((relativeSingularHomologyCoefficientFunctor (C := C) n).map a).app
          (PointedTopCat.pointedPair.obj X) := by
  let P := PointedTopCat.pointedPair.obj X
  let intRelMap := ((relativeSingularHomologyIntCoefficientFunctor
    (C := C) (n : ℤ)).map a).app P
  let natRelMap := ((relativeSingularHomologyCoefficientFunctor
    (C := C) n).map a).app P
  let eRelR := (relativeSingularHomologyNatToIntIso C R n).app P
  let eRelS := (relativeSingularHomologyNatToIntIso C S n).app P
  have hk :
      (reducedSingularHomologyCoefficientMap C n a).app X.right ≫
          (pointedRelativeReducedIntegerIso C S n X).hom =
        (pointedRelativeReducedIntegerIso C R n X).hom ≫ intRelMap :=
    pointedRelativeReducedIntegerIso_hom_naturality_coefficient C a n X
  have hRel : intRelMap ≫ eRelS.hom = eRelR.hom ≫ natRelMap :=
    relativeSingularHomologyNatToIntIso_hom_naturality_coefficient
      C a n P
  change (reducedSingularHomologyCoefficientMap C n a).app X.right ≫
      ((pointedRelativeReducedIntegerIso C S n X).hom ≫ eRelS.hom) =
    ((pointedRelativeReducedIntegerIso C R n X).hom ≫ eRelR.hom) ≫
      natRelMap
  rw [← Category.assoc, hk, Category.assoc, hRel, ← Category.assoc]

/-- The pointed relative/reduced comparison is natural in the coefficient
object. -/
theorem pointedRelativeReducedSingularHomologyNatIso_hom_naturality_coefficient
    {R S : C} (a : R ⟶ S) (n : ℕ) (X : PointedTopCat.{w}) :
    ((reducedSingularHomologyCoefficientFunctor C n).map a).app X.right ≫
        (pointedRelativeReducedSingularHomologyNatIso C S n).hom.app X =
      (pointedRelativeReducedSingularHomologyNatIso C R n).hom.app X ≫
        ((relativeSingularHomologyCoefficientFunctor (C := C) n).map a).app
          (PointedTopCat.pointedPair.obj X) := by
  rw [pointedRelativeReducedSingularHomologyNatIso_hom_app,
    pointedRelativeReducedSingularHomologyNatIso_hom_app,
    ← pointedRelativeReducedSingularHomologyIso_hom C R n X,
    ← pointedRelativeReducedSingularHomologyIso_hom C S n X]
  exact pointedRelativeReducedSingularHomologyIso_hom_naturality_coefficient
    C a n X

end AlgebraicTopology
