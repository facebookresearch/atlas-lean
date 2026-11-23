/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.Reduced
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerTheory
public import MathlibExt.AlgebraicTopology.SingularHomology.ReducedCoefficientFunctor

/-!
# Reduced singular homology under the Nat-to-Int grading extension

Nat-graded reduced singular homology agrees naturally with reduced homology
for the integer-graded singular homology theory in every nonnegative degree.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace AlgebraicTopology

variable (C : Type u) [Category.{v} C] [Abelian C]
variable [HasCoproducts.{w} C] [AB4OfSize.{w} C]

/-- The component comparison from Nat-graded reduced singular homology to
reduced homology in the integer-graded singular theory. -/
noncomputable def reducedSingularHomologyNatToIntObjIso
    (R : C) [hExcisive : (singularHomologyIntData C R).IsExcisive]
    (n : ℕ) (X : PointedTopCat.{w}) :
    reducedSingularHomology C R n X.right ≅
      ((singularHomologyIntTheory (C := C) R).reducedH (n : ℤ)).obj X :=
  reducedSingularHomologyObjIso C R n X.right ≪≫
    (kernel.mapIso
      (f := (singularHomologyIntFunctor C R (n : ℤ)).map
        (TopCat.isTerminalPUnit.from X.right))
      ((singularHomologyFunctor C n).obj R |>.map
        (TopCat.isTerminalPUnit.from X.right))
      ((singularHomologyNatToIntIso C R n).app X.right)
      ((singularHomologyNatToIntIso C R n).app (TopCat.of PUnit))
      ((singularHomologyNatToIntIso C R n).hom.naturality
        (TopCat.isTerminalPUnit.from X.right))).symm ≪≫
    (TopPair.HomologyTheoryData.IsExact.reducedHKernelIsoToPoint
      (singularHomologyIntTheory (C := C) R).obj (n : ℤ) X).symm

set_option backward.isDefEq.respectTransparency false in
/-- The component comparison intertwines the inclusions into Nat- and
Int-graded absolute homology. -/
theorem reducedSingularHomologyNatToIntObjIso_hom_comp_reducedToPointedH
    (R : C) [hExcisive : (singularHomologyIntData C R).IsExcisive]
    (n : ℕ) (X : PointedTopCat.{w}) :
    (reducedSingularHomologyNatToIntObjIso C R n X).hom ≫
        (TopPair.HomologyTheoryData.IsExact.reducedToPointedH
          (singularHomologyIntTheory (C := C) R).obj (n : ℤ)).app X =
      (reducedSingularHomologyι C R n).app X.right ≫
        (singularHomologyNatToIntIso C R n).inv.app X.right := by
  let e0 := reducedSingularHomologyObjIso C R n X.right
  let e1 := kernel.mapIso
    (f := (singularHomologyIntFunctor C R (n : ℤ)).map
      (TopCat.isTerminalPUnit.from X.right))
    ((singularHomologyFunctor C n).obj R |>.map
      (TopCat.isTerminalPUnit.from X.right))
    ((singularHomologyNatToIntIso C R n).app X.right)
    ((singularHomologyNatToIntIso C R n).app (TopCat.of PUnit))
    ((singularHomologyNatToIntIso C R n).hom.naturality
      (TopCat.isTerminalPUnit.from X.right))
  let e2 := TopPair.HomologyTheoryData.IsExact.reducedHKernelIsoToPoint
    (singularHomologyIntTheory (C := C) R).obj (n : ℤ) X
  let j := (TopPair.HomologyTheoryData.IsExact.reducedToPointedH
    (singularHomologyIntTheory (C := C) R).obj (n : ℤ)).app X
  have h2 : e2.inv ≫ j = kernel.ι
      ((singularHomologyIntFunctor C R (n : ℤ)).map
        (TopCat.isTerminalPUnit.from X.right)) := by
    apply e2.inv_comp_eq.mpr
    change j = e2.hom ≫ kernel.ι
      (((singularHomologyIntTheory (C := C) R).obj.H (n : ℤ)).map
        (TopCat.isTerminalPUnit.from X.right))
    exact (TopPair.HomologyTheoryData.IsExact.reducedHKernelIsoToPoint_hom_ι
      (singularHomologyIntTheory (C := C) R).obj (n : ℤ) X).symm
  have h0 : e0.hom ≫ kernel.ι
      ((singularHomologyAugmentation C R n).app X.right) =
      (reducedSingularHomologyι C R n).app X.right :=
    reducedSingularHomologyObjIso_hom_ι C R n X.right
  change ((e0 ≪≫ e1.symm ≪≫ e2.symm).hom ≫ j) = _
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [h2]
  dsimp only [e1]
  simp only [Functor.comp_obj, kernel.mapIso_inv, Iso.app_inv, kernel.lift_ι,
    equalizer_as_kernel]
  have h0' : e0.hom ≫ kernel.ι
      (((singularHomologyFunctor C n).obj R).map
        (TopCat.isTerminalPUnit.from X.right)) =
      (reducedSingularHomologyι C R n).app X.right := h0
  rw [← Category.assoc, h0']

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the component comparison in pointed spaces. -/
theorem reducedSingularHomologyNatToIntObjIso_hom_naturality
    (R : C) [hExcisive : (singularHomologyIntData C R).IsExcisive]
    (n : ℕ) {X Y : PointedTopCat.{w}} (f : X ⟶ Y) :
    (reducedSingularHomologyFunctor C R n).map f.right ≫
        (reducedSingularHomologyNatToIntObjIso C R n Y).hom =
      (reducedSingularHomologyNatToIntObjIso C R n X).hom ≫
        ((singularHomologyIntTheory (C := C) R).reducedH (n : ℤ)).map f := by
  let E := singularHomologyIntTheory (C := C) R
  let reducedMap := (reducedSingularHomologyFunctor C R n).map f.right
  let natMap := ((singularHomologyFunctor C n).obj R).map f.right
  let intMap := (singularHomologyIntFunctor C R (n : ℤ)).map f.right
  let theoryReducedMap := (E.reducedH (n : ℤ)).map f
  let jX := (TopPair.HomologyTheoryData.IsExact.reducedToPointedH
    E.obj (n : ℤ)).app X
  let jY := (TopPair.HomologyTheoryData.IsExact.reducedToPointedH
    E.obj (n : ℤ)).app Y
  let _ : Mono jY := by
    dsimp only [jY, TopPair.HomologyTheoryData.IsExact.reducedToPointedH]
    infer_instance
  have hReduced := (reducedSingularHomologyι C R n).naturality f.right
  change reducedMap ≫ (reducedSingularHomologyι C R n).app Y.right =
    (reducedSingularHomologyι C R n).app X.right ≫ natMap at hReduced
  have hNatToInt := (singularHomologyNatToIntIso C R n).inv.naturality f.right
  change natMap ≫ (singularHomologyNatToIntIso C R n).inv.app Y.right =
    (singularHomologyNatToIntIso C R n).inv.app X.right ≫ intMap at hNatToInt
  have hTheory := (TopPair.HomologyTheoryData.IsExact.reducedToPointedH
    E.obj (n : ℤ)).naturality f |>.symm
  change jX ≫ intMap = theoryReducedMap ≫ jY at hTheory
  apply (cancel_mono jY).mp
  calc
    (reducedMap ≫ (reducedSingularHomologyNatToIntObjIso C R n Y).hom) ≫ jY =
        reducedMap ≫
          ((reducedSingularHomologyNatToIntObjIso C R n Y).hom ≫ jY) := by
      simp only [Category.assoc]
    _ = reducedMap ≫
        ((reducedSingularHomologyι C R n).app Y.right ≫
          (singularHomologyNatToIntIso C R n).inv.app Y.right) := by
      rw [reducedSingularHomologyNatToIntObjIso_hom_comp_reducedToPointedH]
    _ = (reducedMap ≫ (reducedSingularHomologyι C R n).app Y.right) ≫
        (singularHomologyNatToIntIso C R n).inv.app Y.right := by
      simp only [Category.assoc]
    _ = ((reducedSingularHomologyι C R n).app X.right ≫ natMap) ≫
        (singularHomologyNatToIntIso C R n).inv.app Y.right := by rw [hReduced]
    _ = (reducedSingularHomologyι C R n).app X.right ≫
        (natMap ≫ (singularHomologyNatToIntIso C R n).inv.app Y.right) := by
      simp only [Category.assoc]
    _ = (reducedSingularHomologyι C R n).app X.right ≫
        ((singularHomologyNatToIntIso C R n).inv.app X.right ≫ intMap) := by
      rw [hNatToInt]
    _ = ((reducedSingularHomologyι C R n).app X.right ≫
          (singularHomologyNatToIntIso C R n).inv.app X.right) ≫ intMap := by
      simp only [Category.assoc]
    _ = (((reducedSingularHomologyNatToIntObjIso C R n X).hom ≫ jX) ≫
        intMap) := by
      rw [reducedSingularHomologyNatToIntObjIso_hom_comp_reducedToPointedH]
    _ = (reducedSingularHomologyNatToIntObjIso C R n X).hom ≫
        (jX ≫ intMap) := by simp only [Category.assoc]
    _ = (reducedSingularHomologyNatToIntObjIso C R n X).hom ≫
        (theoryReducedMap ≫ jY) := by rw [hTheory]
    _ = ((reducedSingularHomologyNatToIntObjIso C R n X).hom ≫
        theoryReducedMap) ≫ jY := by simp only [Category.assoc]

/-- Nat-graded reduced singular homology is naturally isomorphic to reduced
homology in the integer-graded singular theory. -/
noncomputable def reducedSingularHomologyNatToIntIso
    (R : C) [hExcisive : (singularHomologyIntData C R).IsExcisive]
    (n : ℕ) :
    Under.forget (TopCat.of PUnit) ⋙ reducedSingularHomologyFunctor C R n ≅
      (singularHomologyIntTheory (C := C) R).reducedH (n : ℤ) :=
  NatIso.ofComponents
    (fun X ↦ reducedSingularHomologyNatToIntObjIso C R n X)
    (fun f ↦ reducedSingularHomologyNatToIntObjIso_hom_naturality C R n f)

@[simp]
theorem reducedSingularHomologyNatToIntIso_app
    (R : C) [hExcisive : (singularHomologyIntData C R).IsExcisive]
    (n : ℕ) (X : PointedTopCat.{w}) :
    (reducedSingularHomologyNatToIntIso C R n).app X =
      reducedSingularHomologyNatToIntObjIso C R n X :=
  rfl

omit [AB4OfSize.{w} C] in
private theorem singularHomologyNatToIntIso_inv_naturality_coefficient
    {R S : C} (a : R ⟶ S) (n : ℕ) (X : TopCat.{w}) :
    ((singularHomologyFunctor C n).map a).app X ≫
        (singularHomologyNatToIntIso C S n).inv.app X =
      (singularHomologyNatToIntIso C R n).inv.app X ≫
        ((singularHomologyIntCoefficientFunctor (C := C) (n : ℤ)).map a).app X := by
  let eR := (singularHomologyNatToIntIso C R n).app X
  let eS := (singularHomologyNatToIntIso C S n).app X
  let fInt := ((singularHomologyIntCoefficientFunctor (C := C) (n : ℤ)).map a).app X
  let fNat := ((singularHomologyFunctor C n).map a).app X
  have h : fInt ≫ eS.hom = eR.hom ≫ fNat :=
    homologyIso_extendDownNatToInt_naturality
      (((singularChainComplexFunctor C).map a).app X) n
  apply (cancel_epi eR.hom).mp
  rw [← Category.assoc, ← h]
  dsimp only [eR, eS, fInt]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the reduced Nat-to-Int comparison in the coefficient
object. -/
theorem reducedSingularHomologyNatToIntIso_hom_naturality_coefficient
    [hExcisive : ∀ T : C, (singularHomologyIntData C T).IsExcisive]
    {R S : C} (a : R ⟶ S) (n : ℕ) (X : PointedTopCat.{w}) :
    ((reducedSingularHomologyCoefficientFunctor C n).map a).app X.right ≫
        (reducedSingularHomologyNatToIntObjIso C S n X).hom =
      (reducedSingularHomologyNatToIntObjIso C R n X).hom ≫
        (((singularHomologyIntTheoryFunctor
          (C := C) hExcisive).map a).hom.homₚ (n : ℤ)).app
            (PointedTopCat.pointedPair.obj X) := by
  change (reducedSingularHomologyCoefficientMap C n a).app X.right ≫
      (reducedSingularHomologyNatToIntObjIso C S n X).hom = _
  let T := singularHomologyIntTheoryFunctor (C := C) hExcisive
  let f := (T.map a).hom
  let reducedMap := (reducedSingularHomologyCoefficientMap C n a).app X.right
  let natMap := ((singularHomologyFunctor C n).map a).app X.right
  let intMap := ((singularHomologyIntCoefficientFunctor
    (C := C) (n : ℤ)).map a).app X.right
  let theoryReducedMap := (f.homₚ (n : ℤ)).app (PointedTopCat.pointedPair.obj X)
  let jR := (TopPair.HomologyTheoryData.IsExact.reducedToPointedH
    (singularHomologyIntTheory (C := C) R).obj (n : ℤ)).app X
  let jS := (TopPair.HomologyTheoryData.IsExact.reducedToPointedH
    (singularHomologyIntTheory (C := C) S).obj (n : ℤ)).app X
  let _ : Mono jS := by
    dsimp only [jS, TopPair.HomologyTheoryData.IsExact.reducedToPointedH]
    infer_instance
  have hReduced := congr_app
    (reducedSingularHomologyCoefficientMap_comp_ι C n a) X.right
  change reducedMap ≫ (reducedSingularHomologyι C S n).app X.right =
    (reducedSingularHomologyι C R n).app X.right ≫ natMap at hReduced
  have hNatToInt : natMap ≫
        (singularHomologyNatToIntIso C S n).inv.app X.right =
      (singularHomologyNatToIntIso C R n).inv.app X.right ≫ intMap :=
    singularHomologyNatToIntIso_inv_naturality_coefficient C a n X.right
  have hTheory :=
    TopPair.HomologyTheoryData.IsExact.reducedToPointedH_naturality_theory
      f (n : ℤ) X
  change jR ≫ intMap = theoryReducedMap ≫ jS at hTheory
  apply (cancel_mono jS).mp
  calc
    (reducedMap ≫ (reducedSingularHomologyNatToIntObjIso C S n X).hom) ≫ jS =
        reducedMap ≫
          ((reducedSingularHomologyNatToIntObjIso C S n X).hom ≫ jS) := by
      simp only [Category.assoc]
    _ = reducedMap ≫
        ((reducedSingularHomologyι C S n).app X.right ≫
          (singularHomologyNatToIntIso C S n).inv.app X.right) := by
      rw [reducedSingularHomologyNatToIntObjIso_hom_comp_reducedToPointedH]
    _ = (reducedMap ≫ (reducedSingularHomologyι C S n).app X.right) ≫
        (singularHomologyNatToIntIso C S n).inv.app X.right := by
      simp only [Category.assoc]
    _ = ((reducedSingularHomologyι C R n).app X.right ≫ natMap) ≫
        (singularHomologyNatToIntIso C S n).inv.app X.right := by rw [hReduced]
    _ = (reducedSingularHomologyι C R n).app X.right ≫
        (natMap ≫ (singularHomologyNatToIntIso C S n).inv.app X.right) := by
      simp only [Category.assoc]
    _ = (reducedSingularHomologyι C R n).app X.right ≫
        ((singularHomologyNatToIntIso C R n).inv.app X.right ≫ intMap) := by
      rw [hNatToInt]
    _ = ((reducedSingularHomologyι C R n).app X.right ≫
          (singularHomologyNatToIntIso C R n).inv.app X.right) ≫ intMap := by
      simp only [Category.assoc]
    _ = (((reducedSingularHomologyNatToIntObjIso C R n X).hom ≫ jR) ≫
        intMap) := by
      rw [reducedSingularHomologyNatToIntObjIso_hom_comp_reducedToPointedH]
    _ = (reducedSingularHomologyNatToIntObjIso C R n X).hom ≫
        (jR ≫ intMap) := by simp only [Category.assoc]
    _ = (reducedSingularHomologyNatToIntObjIso C R n X).hom ≫
        (theoryReducedMap ≫ jS) := by rw [hTheory]
    _ = ((reducedSingularHomologyNatToIntObjIso C R n X).hom ≫
        theoryReducedMap) ≫ jS := by simp only [Category.assoc]

end AlgebraicTopology
