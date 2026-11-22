/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionFreeIntervalAction
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionReflection

/-!
# Actual suspension coefficient interchange on arbitrary pointed factors

The proved original two-circle interval action is tensored with an arbitrary
pointed object and conjugated by the actual associator. Its entire ordinary
homotopy is fixed at the original selected basepoint. On the image of the
original suspension group map, the genuine coefficient interchange therefore
acts as inversion. All cube representatives, group maps and coordinate
actions retain the original native constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology
open scoped MonoidalClosed CGWH.limits unitInterval

namespace PointedCGWH.SuspensionCoefficientInterchangeGeometry

open PointedCGWH.SuspensionCoefficientGeometry
open PointedCGWH.SuspensionFreeIntervalGeometry
open PointedCGWH.SuspensionReflectionGeometry
open PointedCGWH.CubeColimitGeometry

/-- Extend the complete pointed time action by the actual tensor with an arbitrary factor. -/
def extendPointedAction {D C : PointedCGWH.{u, v}} (H : D ⊗ C ⟶ C)
    (X : PointedCGWH.{u, v}) : D ⊗ (C ⊗ X) ⟶ C ⊗ X :=
  (α_ D C X).inv ≫ H ▷ X

/-- Every original endpoint of the extended action is the tensor of the original endpoint map. -/
theorem extendPointedAction_endpoint {D C : PointedCGWH.{u, v}} (H : D ⊗ C ⟶ C)
    (X : PointedCGWH.{u, v}) (i : (𝟙_ PointedCGWH) ⟶ D) :
    (λ_ (C ⊗ X)).inv ≫ i ▷ (C ⊗ X) ≫ extendPointedAction H X =
      ((λ_ C).inv ≫ i ▷ C ≫ H) ▷ X := by
  rw [extendPointedAction, associator_inv_naturality_left_assoc]
  have hu : (λ_ (C ⊗ X)).inv ≫ (α_ (𝟙_ PointedCGWH) C X).inv = (λ_ C).inv ▷ X := by
    monoidal
  simpa only [Category.assoc, comp_whiskerRight] using
    congrArg (fun f => f ≫ (i ▷ C) ▷ X ≫ H ▷ X) hu

private theorem conjugatePointedAction_endpoint {D C C' : PointedCGWH.{u, v}}
    (H : D ⊗ C ⟶ C) (e : C' ≅ C) (i : (𝟙_ PointedCGWH) ⟶ D) :
    (λ_ C').inv ≫ i ▷ C' ≫ D ◁ e.hom ≫ H ≫ e.inv =
      e.hom ≫ ((λ_ C).inv ≫ i ▷ C ≫ H) ≫ e.inv := by
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  simp only [Category.assoc]

/-- The complete coefficient permutation keeps both original associators and inverse braiding. -/
def coefficientSwap (X : PointedCGWH.{u, v}) :
    PointedCGWH.sphereOne ⊗ (PointedCGWH.sphereOne ⊗ X) ⟶
      PointedCGWH.sphereOne ⊗ (PointedCGWH.sphereOne ⊗ X) :=
  (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne X).inv ≫
    (β_ PointedCGWH.sphereOne PointedCGWH.sphereOne).inv ▷ X ≫
      (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne X).hom

/-- The actual extended action retains the whole original two-circle coefficient association. -/
def coefficientExtendedAction (X : PointedCGWH.{u, v}) :
    freePointed CGWH.interval ⊗ (PointedCGWH.sphereOne ⊗ (PointedCGWH.sphereOne ⊗ X)) ⟶
      PointedCGWH.sphereOne ⊗ (PointedCGWH.sphereOne ⊗ X) :=
  freePointed CGWH.interval ◁ (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne X).inv ≫
    extendPointedAction coefficientPointedAction X ≫
      (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne X).hom

/-- The entire original zero endpoint is reflection of the first actual suspension coefficient. -/
theorem coefficientExtendedAction_zero (X : PointedCGWH.{u, v}) :
    (λ_ (PointedCGWH.sphereOne ⊗ (PointedCGWH.sphereOne ⊗ X))).inv ≫
      ((Under.costar CGWH.point).map CGWH.intervalZero) ▷
        (PointedCGWH.sphereOne ⊗ (PointedCGWH.sphereOne ⊗ X)) ≫ coefficientExtendedAction X =
      circleReflection ▷ (PointedCGWH.sphereOne ⊗ X) := by
  let i : (𝟙_ PointedCGWH.{u, v}) ⟶ freePointed CGWH.interval :=
    (Under.costar CGWH.point).map CGWH.intervalZero
  have he := conjugatePointedAction_endpoint (extendPointedAction coefficientPointedAction X)
    (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne X).symm i
  have ht := extendPointedAction_endpoint coefficientPointedAction X i
  have h₀ := congrArg (fun f => f ▷ X) coefficientPointedAction_zero.{u, v}
  have hc := congrArg (fun f =>
    (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne X).inv ≫ f ≫
      (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne X).hom) (ht.trans h₀)
  have hr : (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne X).inv ≫
      (circleReflection ▷ PointedCGWH.sphereOne) ▷ X ≫
        (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne X).hom =
      circleReflection ▷ (PointedCGWH.sphereOne ⊗ X) := by
    rw [associator_naturality_left, Iso.inv_hom_id_assoc]
  have hfinal := he.trans (hc.trans hr)
  simpa only [i, coefficientExtendedAction, Iso.symm_hom, Iso.symm_inv, Category.assoc] using hfinal

/-- The entire original one endpoint is the full actual suspension coefficient swap. -/
theorem coefficientExtendedAction_one (X : PointedCGWH.{u, v}) :
    (λ_ (PointedCGWH.sphereOne ⊗ (PointedCGWH.sphereOne ⊗ X))).inv ≫
      ((Under.costar CGWH.point).map CGWH.intervalOne) ▷
        (PointedCGWH.sphereOne ⊗ (PointedCGWH.sphereOne ⊗ X)) ≫ coefficientExtendedAction X =
      coefficientSwap X := by
  let i : (𝟙_ PointedCGWH.{u, v}) ⟶ freePointed CGWH.interval :=
    (Under.costar CGWH.point).map CGWH.intervalOne
  have he := conjugatePointedAction_endpoint (extendPointedAction coefficientPointedAction X)
    (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne X).symm i
  have ht := extendPointedAction_endpoint coefficientPointedAction X i
  have h₁ := congrArg (fun f => f ▷ X) coefficientPointedAction_one.{u, v}
  have hc := congrArg (fun f =>
    (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne X).inv ≫ f ≫
      (α_ PointedCGWH.sphereOne PointedCGWH.sphereOne X).hom) (ht.trans h₁)
  have hfinal := he.trans hc
  simpa only [i, coefficientExtendedAction, coefficientSwap, Iso.symm_hom, Iso.symm_inv,
    Category.assoc] using hfinal

/-- The actual coefficient swap and first-circle reflection are based-homotopic for every factor. -/
def coefficientInterchangeHomotopy (X : PointedCGWH.{u, v}) : ContinuousMap.HomotopyRel
    (ConcreteCategory.hom (C := CGWH.{u, v})
      (circleReflection ▷ (PointedCGWH.sphereOne ⊗ X)).right)
    (ConcreteCategory.hom (C := CGWH.{u, v}) (coefficientSwap X).right)
    {underlyingBasepoint (PointedCGWH.sphereOne ⊗ (PointedCGWH.sphereOne ⊗ X))} :=
  freeIntervalHomotopyRel _ _ (coefficientExtendedAction X)
    (coefficientExtendedAction_zero X) (coefficientExtendedAction_one X)

/-- An entire ordinary based homotopy retains both actual cube-map representatives and boundary. -/
theorem cubeMap_homotopic_of_basedHomotopyRel (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f₀ f₁ : X ⟶ Y)
    (H : ContinuousMap.HomotopyRel
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₀.right)
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₁.right) {underlyingBasepoint X})
    (p : GenLoop (Fin n) (CGWH.cgwhToTop.obj X.right) (underlyingBasepoint X)) :
    GenLoop.Homotopic (cubeMap n f₀ p) (cubeMap n f₁ p) := by
  have h₀ : (ConcreteCategory.hom (C := CGWH.{u, v}) f₀.right).comp p.1 =
      (cubeMap n f₀ p).1 := by
    ext q
    exact (cubeMap_apply n f₀ p q).symm
  have h₁ : (ConcreteCategory.hom (C := CGWH.{u, v}) f₁.right).comp p.1 =
      (cubeMap n f₁ p).1 := by
    ext q
    exact (cubeMap_apply n f₁ p q).symm
  refine ⟨{ toHomotopy := (H.toHomotopy.compContinuousMap p.1).cast h₀ h₁, prop' := ?_ }⟩
  intro t q hq
  change H (t, p.1 q) = (cubeMap n f₀ p).1 q
  have hp : p.1 q ∈ ({underlyingBasepoint X} : Set (CGWH.cgwhToTop.obj X.right)) := by
    rw [Set.mem_singleton_iff]
    exact GenLoop.boundary p q hq
  exact (H.eq_fst t hp).trans (cubeMap_apply n f₀ p q).symm

/-- The full original homotopy-group map is unchanged by an entire actual based homotopy. -/
theorem piNMap_eq_of_basedHomotopyRel (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f₀ f₁ : X ⟶ Y)
    (H : ContinuousMap.HomotopyRel
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₀.right)
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₁.right) {underlyingBasepoint X}) :
    piNMap n f₀ = piNMap n f₁ := by
  funext a
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  rw [piNMap_mk, piNMap_mk]
  exact Quotient.sound (cubeMap_homotopic_of_basedHomotopyRel n f₀ f₁ H p)

/-- The whole actual positive group map is unchanged by the original based homotopy. -/
theorem piNPositiveMap_eq_of_basedHomotopyRel (k : ℕ) {X Y : PointedCGWH.{u, v}}
    (f₀ f₁ : X ⟶ Y)
    (H : ContinuousMap.HomotopyRel
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₀.right)
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₁.right) {underlyingBasepoint X}) :
    piNPositiveMap k f₀ = piNPositiveMap k f₁ := by
  ext a
  simp only [piNPositiveMap_apply]
  exact congrFun (piNMap_eq_of_basedHomotopyRel (k + 1) f₀ f₁ H) a

/-- The genuine suspension coefficient swap inverts the original suspension image for every k. -/
theorem coefficientSwap_suspensionImage (k : ℕ) (X : PointedCGWH.{u, v})
    (a : piN (k + 1) (PointedCGWH.sphereOne ⊗ X)) :
    (piNPositiveMap (k + 1) (coefficientSwap X)).hom
        (((spaceSuspensionGroupMap k).app (PointedCGWH.sphereOne ⊗ X)).hom a) =
      (((spaceSuspensionGroupMap k).app (PointedCGWH.sphereOne ⊗ X)).hom a)⁻¹ := by
  have h := piNPositiveMap_eq_of_basedHomotopyRel (k + 1)
    (circleReflection ▷ (PointedCGWH.sphereOne ⊗ X)) (coefficientSwap X)
    (coefficientInterchangeHomotopy X)
  have h' := congrArg (fun f => f.hom
    (((spaceSuspensionGroupMap k).app (PointedCGWH.sphereOne ⊗ X)).hom a)) h.symm
  exact h'.trans (spaceSuspensionGroupMap_reflection k (PointedCGWH.sphereOne ⊗ X) a)

end PointedCGWH.SuspensionCoefficientInterchangeGeometry
