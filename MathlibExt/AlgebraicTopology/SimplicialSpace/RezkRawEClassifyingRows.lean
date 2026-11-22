/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.DiscreteCodiscreteSpaceClosed
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCompletionRaw
import MathlibExt.AlgebraicTopology.SimplicialSpace.WalkingEUnitDwyerKan
import MathlibExt.AlgebraicTopology.SimplicialSet.RezkRawEFiniteRows
import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexCoordinates

/-!
# Original raw E rows through the whole classifying-power comparison

Every object and map uses the SAME D(Jm), chosen whole power, and raw diagonal.
No supplied row Iso, contraction, CSS weak-equivalence or completion outcome is
an input. The scalar and whole adjunction foundations are separate proof units.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open scoped Simplicial SimplicialSpace.Cartesian
namespace SimplicialSpace.RezkRawEClassifyingRows
open DiscreteCodiscreteSpaceClosed RezkCompletionRaw SSet.RezkRawEFiniteRows

/-- The original full-J nerve is the literal codiscrete nerve through every ordered vertex tuple. -/
def scalarCoefficientIso (n : SimplexCategory) :
    SSet.FreeGroupoidSimplex.J.{u}.obj n ≅
      CategoryTheory.Codiscrete.functorToSSet.obj (ULift.{u} (Fin (n.len + 1))) :=
  NatIso.ofComponents (fun a => Equiv.toIso
    ((SSet.FreeGroupoidSimplex.simplexVertexEquiv n a.unop.len).trans
      ((Equiv.piCongrRight (fun _ => (Equiv.ulift (α := Fin (n.len + 1))).symm)).trans
        CategoryTheory.Codiscrete.equivFun.symm))) (by
    intro a b θ
    apply ConcreteCategory.hom_ext
    intro x
    apply CategoryTheory.Codiscrete.equivFun.injective
    funext i
    rfl)

/-- Every original site map sends the actual lifted vertex v to delta(v). -/
theorem scalarCoefficientIso_site {n m : SimplexCategory} (δ : n ⟶ m) :
    SSet.FreeGroupoidSimplex.J.{u}.map δ ≫ (scalarCoefficientIso m).hom =
      (scalarCoefficientIso n).hom ≫ CategoryTheory.Codiscrete.functorToSSet.map
        (↾fun v : ULift.{u} (Fin (n.len + 1)) => ULift.up (δ v.down)) := by
  apply SSet.hom_ext
  intro a
  apply ConcreteCategory.hom_ext
  intro x
  apply CategoryTheory.Codiscrete.equivFun.injective
  funext i
  exact congrArg ULift.up
    (congrFun (SSet.FreeGroupoidSimplex.simplexVertexEquiv_site δ a.unop.len x) i)

/-- The coefficient is the SAME original D(Jn), through the actually constructed full nerve Iso. -/
def coefficientIso (n : SimplexCategory) :
    coefficient.{u}.obj n ≅ codiscreteSpaceFunctor.obj (ULift.{u} (Fin (n.len + 1))) :=
  discreteInnerFunctor.mapIso (scalarCoefficientIso n)

/-- The actual discrete-inner coefficient Iso is natural for every original site map. -/
theorem coefficientIso_site {n m : SimplexCategory} (δ : n ⟶ m) :
    coefficient.{u}.map δ ≫ (coefficientIso m).hom =
      (coefficientIso n).hom ≫ codiscreteSpaceFunctor.map
        (↾fun v : ULift.{u} (Fin (n.len + 1)) => ULift.up (δ v.down)) := by
  change discreteInnerFunctor.map (SSet.FreeGroupoidSimplex.J.map δ) ≫
      discreteInnerFunctor.map (scalarCoefficientIso m).hom =
    discreteInnerFunctor.map (scalarCoefficientIso n).hom ≫
      discreteInnerFunctor.map (CategoryTheory.Codiscrete.functorToSSet.map _)
  rw [← Functor.map_comp, ← Functor.map_comp, scalarCoefficientIso_site]

/-- Only the literal lifted Hom coordinates are normalized; the coefficient carrier is unchanged. -/
def liftedFunctionEquiv (n : SimplexCategory) :
    (ULift.{u} (Fin (n.len + 1)) → ULift.{u} Bool) ≃
      (Fin (n.len + 1) → ULift.{u} Bool) where
  toFun f := fun v => f (ULift.up v)
  invFun f := fun v => f v.down
  left_inv f := by funext v; cases v; rfl
  right_inv f := rfl

private def liftedInternalHomEquiv (n : SimplexCategory) :
    ((ihom (ULift.{u} (Fin (n.len + 1)))).obj (ULift.{u} Bool)) ≃
      (Fin (n.len + 1) → ULift.{u} Bool) :=
  TypeCat.homEquiv.trans (liftedFunctionEquiv n)

/-- The whole chosen power comparison precedes every outer-row or inner-simplex evaluation. -/
def classifyingPowerIso (n : SimplexCategory) :
    (powerDiagram WalkingEUnit.coherentSpace.{u}).obj (op n) ≅
      codiscreteSpaceFunctor.obj (Fin (n.len + 1) → ULift.{u} Bool) :=
  ((internalHom.mapIso (coefficientIso n).op).app WalkingEUnit.coherentSpace).symm ≪≫
    (wholePowerIso (ULift.{u} (Fin (n.len + 1))) (ULift.{u} Bool)).symm ≪≫
    codiscreteSpaceFunctor.mapIso (Equiv.toIso (liftedInternalHomEquiv n))

set_option backward.isDefEq.respectTransparency false in
/-- Coefficient contravariance is retained for every original operator, even when it moves zero. -/
theorem classifyingPowerIso_coefficient {n m : SimplexCategoryᵒᵖ} (δ : n ⟶ m) :
    (powerDiagram WalkingEUnit.coherentSpace.{u}).map δ ≫ (classifyingPowerIso m.unop).hom =
    (classifyingPowerIso n.unop).hom ≫ codiscreteSpaceFunctor.map
      (↾fun f : Fin (n.unop.len + 1) → ULift.{u} Bool => f ∘ δ.unop.toOrderHom) := by
  let b : ULift.{u} (Fin (m.unop.len + 1)) ⟶ ULift.{u} (Fin (n.unop.len + 1)) :=
    ↾fun v => ULift.up (δ.unop v.down)
  have hi : (coefficientIso m.unop).inv ≫ coefficient.map δ.unop =
      codiscreteSpaceFunctor.map b ≫ (coefficientIso n.unop).inv := by
    apply (cancel_mono (coefficientIso n.unop).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      coefficientIso_site, Iso.inv_hom_id_assoc]
    rfl
  have hp := congrArg (fun f => (pre f).app WalkingEUnit.coherentSpace.{u}) hi
  simp only [pre_map, NatTrans.comp_app] at hp
  have hc : (pre (codiscreteSpaceFunctor.map b)).app
      (codiscreteSpaceFunctor.obj (ULift.{u} Bool)) ≫
      (wholePowerIso (ULift.{u} (Fin (m.unop.len + 1))) (ULift.{u} Bool)).inv =
    (wholePowerIso (ULift.{u} (Fin (n.unop.len + 1))) (ULift.{u} Bool)).inv ≫
      codiscreteSpaceFunctor.map ((pre b).app (ULift.{u} Bool)) := by
    apply (cancel_epi (wholePowerIso (ULift.{u} (Fin (n.unop.len + 1)))
      (ULift.{u} Bool)).hom).1
    rw [← Category.assoc, wholePowerIso_source]
    simp only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id]
  have hn : (pre b).app (ULift.{u} Bool) ≫
      (Equiv.toIso (liftedInternalHomEquiv m.unop)).hom =
    (Equiv.toIso (liftedInternalHomEquiv n.unop)).hom ≫
      (↾fun f : Fin (n.unop.len + 1) → ULift.{u} Bool => f ∘ δ.unop.toOrderHom) := by
    apply ConcreteCategory.hom_ext
    intro f
    funext v
    rfl
  have h : (pre (coefficient.map δ.unop)).app WalkingEUnit.coherentSpace ≫
      ((pre (coefficientIso m.unop).inv).app WalkingEUnit.coherentSpace ≫
        (wholePowerIso (ULift.{u} (Fin (m.unop.len + 1))) (ULift.{u} Bool)).inv ≫
          codiscreteSpaceFunctor.map (Equiv.toIso (liftedInternalHomEquiv m.unop)).hom) =
    ((pre (coefficientIso n.unop).inv).app WalkingEUnit.coherentSpace ≫
        (wholePowerIso (ULift.{u} (Fin (n.unop.len + 1))) (ULift.{u} Bool)).inv ≫
          codiscreteSpaceFunctor.map (Equiv.toIso (liftedInternalHomEquiv n.unop)).hom) ≫
      codiscreteSpaceFunctor.map
        (↾fun f : Fin (n.unop.len + 1) → ULift.{u} Bool => f ∘ δ.unop.toOrderHom) := by
    rw [← Category.assoc, hp]
    have hc' : (pre (codiscreteSpaceFunctor.map b)).app WalkingEUnit.coherentSpace ≫
        (wholePowerIso (ULift.{u} (Fin (m.unop.len + 1))) (ULift.{u} Bool)).inv =
      (wholePowerIso (ULift.{u} (Fin (n.unop.len + 1))) (ULift.{u} Bool)).inv ≫
        codiscreteSpaceFunctor.map ((pre b).app (ULift.{u} Bool)) := hc
    calc
      _ = (pre (coefficientIso n.unop).inv).app WalkingEUnit.coherentSpace ≫
          (((pre (codiscreteSpaceFunctor.map b)).app WalkingEUnit.coherentSpace ≫
            (wholePowerIso (ULift.{u} (Fin (m.unop.len + 1))) (ULift.{u} Bool)).inv) ≫
            codiscreteSpaceFunctor.map (Equiv.toIso (liftedInternalHomEquiv m.unop)).hom) :=
        (Category.assoc _ _ _).trans (congrArg (fun f =>
          (pre (coefficientIso n.unop).inv).app WalkingEUnit.coherentSpace ≫ f)
          (Category.assoc _ _ _).symm)
      _ = _ := by
        rw [hc']
        simp only [Category.assoc]
        rw [← Functor.map_comp, hn, Functor.map_comp]
  exact h

private theorem curry_snd_pre {A D W : SimplicialSpace.{u}} (f : D ⟶ A) :
    curry (CartesianMonoidalCategory.snd A W) ≫ (pre f).app W =
      curry (CartesianMonoidalCategory.snd D W) := by
  rw [curry_pre_app, CartesianMonoidalCategory.whiskerRight_snd]

private theorem wholeConstant (A B : Type u) :
    curry (CartesianMonoidalCategory.snd (codiscreteSpaceFunctor.obj A)
      (codiscreteSpaceFunctor.obj B)) ≫ (wholePowerIso A B).inv =
      codiscreteSpaceFunctor.map (curry (CartesianMonoidalCategory.snd A B)) := by
  have h := wholePowerIso_curry A B B (CartesianMonoidalCategory.snd A B)
  rw [CartesianMonoidalCategory.inv_prodComparison_map_snd] at h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    (congrArg (fun g => g ≫ (wholePowerIso A B).inv) h).symm

/-- The classifying power comparison carries the SAME original constant section. -/
theorem classifyingPowerIso_constantSection (n : SimplexCategory) :
    (constantPowerSection WalkingEUnit.coherentSpace.{u}).app (op n) ≫
      (classifyingPowerIso n).hom =
    codiscreteSpaceFunctor.map
      (↾fun b : ULift.{u} Bool => fun _ : Fin (n.len + 1) => b) := by
  let A := ULift.{u} (Fin (n.len + 1))
  let B := ULift.{u} Bool
  have h : curry (CartesianMonoidalCategory.snd (coefficient.obj n)
      WalkingEUnit.coherentSpace) ≫
      ((pre (coefficientIso n).inv).app WalkingEUnit.coherentSpace ≫
        (wholePowerIso A B).inv ≫
          codiscreteSpaceFunctor.map (Equiv.toIso (liftedInternalHomEquiv n)).hom) =
      codiscreteSpaceFunctor.map
        (↾fun b : ULift.{u} Bool => fun _ : Fin (n.len + 1) => b) := by
    rw [← Category.assoc, curry_snd_pre]
    have hc := wholeConstant A B
    have hn : curry (CartesianMonoidalCategory.snd A B) ≫
        (Equiv.toIso (liftedInternalHomEquiv n)).hom =
        (↾fun b : ULift.{u} Bool => fun _ : Fin (n.len + 1) => b) := rfl
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun _f => _f ≫ codiscreteSpaceFunctor.map
        (Equiv.toIso (liftedInternalHomEquiv n)).hom) hc).trans
          ((codiscreteSpaceFunctor.map_comp _ _).symm.trans
            (congrArg codiscreteSpaceFunctor.map hn)))
  exact h

/-- Transposition retains every entry of the original outer/inner matrix. -/
def matrixTranspose (k n : ℕ) :
    (Fin (k + 1) → Fin (n + 1) → ULift.{u} Bool) ≃
      (Fin (n + 1) → Fin (k + 1) → ULift.{u} Bool) where
  toFun f := fun i j => f j i
  invFun f := fun i j => f j i
  left_inv _f := rfl
  right_inv _f := rfl

/-- Every raw diagonal simplex is compared through the whole power Iso before tuple
transposition. -/
def rawRowEquiv (k : SimplexCategoryᵒᵖ) (n : ℕ) :
    ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.obj k).obj (op ⦋n⦌) ≃
      (rowNerve.{u} k.unop.len).obj (op ⦋n⦌) :=
  let evaluationAt : SimplicialSpace.{u} ⥤ Type u :=
    forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj k ⋙
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌)
  ((evaluationAt.mapIso (classifyingPowerIso ⦋n⦌)).toEquiv).trans
    (CategoryTheory.Codiscrete.equivFun.trans
      ((matrixTranspose k.unop.len n).trans CategoryTheory.Codiscrete.equivFun.symm))

private theorem rawRowEquiv_coordinate (k : SimplexCategoryᵒᵖ) (n : ℕ)
    (x : ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.obj k).obj (op ⦋n⦌))
    (i : Fin (n + 1)) (j : Fin (k.unop.len + 1)) :
    ((rawRowEquiv k n x).obj i).as j =
      (((((classifyingPowerIso ⦋n⦌).hom.hom.app k).app (op ⦋n⦌)) x).obj j).as i := rfl

private theorem rowNerve_map_coordinate (k : ℕ) {n m : ℕ}
    (θ : ⦋n⦌ ⟶ ⦋m⦌) (x : (rowNerve.{u} k).obj (op ⦋m⦌))
    (i : Fin (n + 1)) (j : Fin (k + 1)) :
    (((rowNerve k).map θ.op x).obj i).as j = (x.obj (θ i)).as j := rfl

set_option maxRecDepth 4096 in
/-- The actual diagonal uses both inner and coefficient maps; both are retained in this equation. -/
theorem rawRowEquiv_inner (k : SimplexCategoryᵒᵖ) {n m : ℕ}
    (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (x : ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.obj k).obj (op ⦋m⦌)) :
    rawRowEquiv k n ((rawCompletion WalkingEUnit.coherentSpace).diagram.obj k |>.map θ.op x) =
      (rowNerve k.unop.len).map θ.op (rawRowEquiv k m x) := by
  have hcoeff := congrArg (fun f => (f.hom.app k).app (op ⦋n⦌))
    (classifyingPowerIso_coefficient (θ.op))
  have hinner := congrArg (fun f => f x)
    (((classifyingPowerIso ⦋m⦌).hom.hom.app k).naturality θ.op)
  change ((classifyingPowerIso ⦋m⦌).hom.hom.app k).app (op ⦋n⦌)
      (((powerDiagram WalkingEUnit.coherentSpace).obj (op ⦋m⦌)).diagram.obj k |>.map θ.op x) =
    ((classifyingPowerIso ⦋m⦌).hom.hom.app k).app (op ⦋m⦌) x at hinner
  let t := (codiscreteSpaceFunctor.map
    (↾fun f : Fin (m + 1) → ULift.{u} Bool => f ∘ θ.toOrderHom)).hom.app k
  have hc := congrArg (fun f => f
    (((powerDiagram WalkingEUnit.coherentSpace).obj (op ⦋m⦌)).diagram.obj k |>.map θ.op x)) hcoeff
  have hboth := hc.trans (congrArg (t.app (op ⦋n⦌)) hinner)
  apply CategoryTheory.Codiscrete.equivFun.injective
  funext i
  funext j
  change ((rawRowEquiv k n _).obj i).as j =
    (((rowNerve k.unop.len).map θ.op (rawRowEquiv k m x)).obj i).as j
  rw [rawRowEquiv_coordinate, rowNerve_map_coordinate, rawRowEquiv_coordinate]
  exact congrArg (fun y => (y.obj j).as i) hboth

set_option maxRecDepth 4096 in
/-- The comparison is a whole row Iso for every original outer degree. -/
def rawRowIso (k : SimplexCategoryᵒᵖ) :
    (rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.obj k ≅ rowNerve k.unop.len :=
  NatIso.ofComponents (fun n => Equiv.toIso (rawRowEquiv k n.unop.len)) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro x
    exact rawRowEquiv_inner k θ.unop x)

set_option maxRecDepth 4096 in
/-- Every original outer operator is retained by the same whole row Iso. -/
theorem rawRowIso_outer {k l : SimplexCategoryᵒᵖ} (κ : k ⟶ l) :
    (rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.map κ ≫ (rawRowIso l).hom =
      (rawRowIso k).hom ≫ rowMap κ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  have h := congrArg (fun f => f.app n x)
    ((classifyingPowerIso n.unop).hom.hom.naturality κ)
  apply CategoryTheory.Codiscrete.equivFun.injective
  funext i
  funext j
  change ((rawRowEquiv l n.unop.len
      (((rawCompletion WalkingEUnit.coherentSpace).diagram.map κ).app n x)).obj i).as j =
    ((rawRowEquiv k n.unop.len x).obj i).as (κ.unop j)
  rw [rawRowEquiv_coordinate, rawRowEquiv_coordinate]
  exact congrArg (fun y => (y.obj j).as i) h

/-- The actual row coaugmentation is the whole constant-vector map in every inner degree. -/
def rowConstantUnit (k : SimplexCategoryᵒᵖ) :
    WalkingEUnit.coherentSpace.{u}.diagram.obj k ⟶ rowNerve k.unop.len where
  app n := ↾fun x => CategoryTheory.Codiscrete.functor
    (fun _ : Fin (n.unop.len + 1) => CategoryTheory.Codiscrete.equivFun x)
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply CategoryTheory.Codiscrete.equivFun.injective
    funext i
    rfl

set_option maxRecDepth 4096 in
/-- This is the SAME original raw unit; both the whole row and every inner simplex are retained. -/
theorem rawRowIso_originalUnit (k : SimplexCategoryᵒᵖ) :
    (rawCompletionUnit WalkingEUnit.coherentSpace.{u}).hom.app k ≫ (rawRowIso k).hom =
      rowConstantUnit k := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  have h := congrArg (fun f => ((f.hom.app k).app n) x)
    (classifyingPowerIso_constantSection n.unop)
  apply CategoryTheory.Codiscrete.equivFun.injective
  funext i
  funext j
  change ((rawRowEquiv k n.unop.len
      (((rawCompletionUnit WalkingEUnit.coherentSpace).hom.app k).app n x)).obj i).as j =
    Codiscrete.equivFun x j
  rw [rawRowEquiv_coordinate]
  exact congrArg (fun y => (y.obj j).as i) h

private theorem transportedContraction_endpoint {X R I : SSet.{u}}
    (e : X ≅ R) (h : R ⨯ I ⟶ R) (i : I.obj (op ⦋0⦌)) (t : R ⟶ R)
    (ht : prod.lift (𝟙 R) (SSet.const i) ≫ h = t) :
    prod.lift (𝟙 X) (SSet.const i) ≫
        (prod.map e.hom (𝟙 I) ≫ h ≫ e.inv) = e.hom ≫ t ≫ e.inv := by
  simp only [prod.lift_map_assoc, Category.id_comp, Category.comp_id]
  have hl : prod.lift e.hom (SSet.const i) =
      e.hom ≫ prod.lift (𝟙 R) (SSet.const i) := by
    rw [prod.comp_lift, Category.comp_id, SSet.comp_const]
  calc
    _ = (e.hom ≫ prod.lift (𝟙 R) (SSet.const i)) ≫ h ≫ e.inv :=
      congrArg (fun f => f ≫ h ≫ e.inv) hl
    _ = e.hom ≫ (prod.lift (𝟙 R) (SSet.const i) ≫ h) ≫ e.inv := by
      simp only [Category.assoc]
    _ = e.hom ≫ t ≫ e.inv := by rw [ht]

/-- The actual row contraction is transported through the internally constructed whole row Iso. -/
def rawRowContraction (k : SimplexCategoryᵒᵖ) :
    ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.obj k) ⨯ SSet.coherentIso.{u} ⟶
      (rawCompletion WalkingEUnit.coherentSpace).diagram.obj k :=
  prod.map (rawRowIso k).hom (𝟙 SSet.coherentIso.{u}) ≫
    rowContraction k.unop.len ≫ (rawRowIso k).inv

/-- The basepoint is the actual inverse image of the original all-false coherent vector. -/
def rawRowBase (k : SimplexCategoryᵒᵖ) :
    ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.obj k).obj (op ⦋0⦌) :=
  (rawRowIso k).inv.app (op ⦋0⦌) (rowBase k.unop.len)

/-- Both contraction endpoints hold as whole maps in EVERY original outer row. -/
theorem rawRowContraction_endpoints (k : SimplexCategoryᵒᵖ) :
    prod.lift (𝟙 ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.obj k))
        (SSet.const SSet.coherentIso.x₀) ≫ rawRowContraction k =
      SSet.const (rawRowBase k) ∧
    prod.lift (𝟙 ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.obj k))
        (SSet.const SSet.coherentIso.x₁) ≫ rawRowContraction k =
      𝟙 ((rawCompletion WalkingEUnit.coherentSpace).diagram.obj k) := by
  constructor
  · exact (transportedContraction_endpoint (rawRowIso k) (rowContraction k.unop.len)
      SSet.coherentIso.x₀ (SSet.const (rowBase k.unop.len))
      (rowContraction_endpoints k.unop.len).1).trans
        (by simp only [SSet.comp_const, SSet.const_comp, rawRowBase])
  · exact (transportedContraction_endpoint (rawRowIso k) (rowContraction k.unop.len)
      SSet.coherentIso.x₁ (𝟙 _) (rowContraction_endpoints k.unop.len).2).trans
        (by simp only [Category.id_comp, Iso.hom_inv_id])

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
/-- The SAME actual contraction remains natural for every original outer operator. -/
theorem rawRowContraction_outer {k l : SimplexCategoryᵒᵖ} (κ : k ⟶ l) :
    prod.map ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.map κ)
        (𝟙 SSet.coherentIso.{u}) ≫ rawRowContraction l =
      rawRowContraction k ≫ (rawCompletion WalkingEUnit.coherentSpace).diagram.map κ := by
  have hi : (rawRowIso k).inv ≫ (rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.map κ =
      rowMap κ ≫ (rawRowIso l).inv := by
    apply (cancel_mono (rawRowIso l).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [rawRowIso_outer, Iso.inv_hom_id_assoc]
  have hf :
      prod.map ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.map κ)
          (𝟙 SSet.coherentIso.{u}) ≫ prod.map (rawRowIso.{u} l).hom (𝟙 _) =
        prod.map (rawRowIso.{u} k).hom (𝟙 _) ≫ prod.map (rowMap.{u} κ) (𝟙 _) := by
    rw [prod.map_map, prod.map_map]
    simp only [Category.id_comp]
    rw [rawRowIso_outer]
  change
    prod.map ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.map κ) (𝟙 _) ≫
      (prod.map (rawRowIso.{u} l).hom (𝟙 _) ≫ rowContraction l.unop.len ≫
        (rawRowIso l).inv) =
    (prod.map (rawRowIso.{u} k).hom (𝟙 _) ≫ rowContraction k.unop.len ≫
      (rawRowIso k).inv) ≫ (rawCompletion WalkingEUnit.coherentSpace).diagram.map κ
  calc
    _ = (prod.map ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.map κ) (𝟙 _) ≫
          prod.map (rawRowIso.{u} l).hom (𝟙 _)) ≫ rowContraction l.unop.len ≫
            (rawRowIso l).inv := by simp only [Category.assoc]
    _ = (prod.map (rawRowIso.{u} k).hom (𝟙 _) ≫ prod.map (rowMap.{u} κ) (𝟙 _)) ≫
          rowContraction l.unop.len ≫ (rawRowIso l).inv :=
      congrArg (fun f => f ≫ rowContraction.{u} l.unop.len ≫ (rawRowIso l).inv) hf
    _ = prod.map (rawRowIso.{u} k).hom (𝟙 _) ≫
          (prod.map (rowMap.{u} κ) (𝟙 _) ≫ rowContraction l.unop.len) ≫
            (rawRowIso l).inv := by simp only [Category.assoc]
    _ = prod.map (rawRowIso.{u} k).hom (𝟙 _) ≫
          (rowContraction k.unop.len ≫ rowMap.{u} κ) ≫ (rawRowIso l).inv := by
      rw [rowContraction_outer]
    _ = _ := by
      simp only [Category.assoc]
      rw [← hi]

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
/-- The genuine weak terminal map follows only after the full row Iso and explicit coherent
contraction. -/
theorem rawE_row_terminal_weak (k : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences
      (terminal.from ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.obj k)) := by
  have h := rowNerve_terminal_weak.{u} k.unop.len
  have heq : terminal.from ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.obj k) =
      (rawRowIso.{u} k).hom ≫ terminal.from (rowNerve.{u} k.unop.len) := Subsingleton.elim _ _
  exact (congrArg
    (fun f : ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.obj k) ⟶ ⊤_ SSet.{u} =>
      SSet.realizationWeakEquivalences f) heq).mpr
    (MorphismProperty.RespectsIso.precomp
      SSet.realizationWeakEquivalences (rawRowIso k).hom _ h)

/-- The k=0 row is the original full E, through the one-coordinate finite product. -/
theorem rawE_zero_row_weak :
    SSet.realizationWeakEquivalences
      (terminal.from ((rawCompletion WalkingEUnit.coherentSpace.{u}).diagram.obj (op ⦋0⦌))) := by
  exact rawE_row_terminal_weak (op ⦋0⦌)


end SimplicialSpace.RezkRawEClassifyingRows
