/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHHornIntervalComparison
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHHornTensorAction
public import MathlibExt.Topology.Category.CGWH.IntervalActionHomotopy

/-!
# Ordinary homotopies from actual freely based interval actions

The actual free summand and native smash quotient restrict the pointed action.
The computed unit retains both endpoints and the full fixed-source equation.
The oriented native interval comparison and the existing path-landing API give
joint ordinary continuity without any coefficient compactness or model input.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory

namespace PointedCGWH

private def intervalFreeCore :
    (Under.costar CGWH.point.{u, v}).CoreMonoidal := by
  letI : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.costarCoreMonoidal CGWH.point CGWH.point_isTerminal

private def pointUnitIso : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
  CGWH.point_isTerminal.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit

/-- The inclusion of a CGWH space into the underlying freely pointed space. -/
def freeSummand (A : CGWH.{u, v}) :
    A ⟶ ((Under.costar CGWH.point).obj A).right := coprod.inr

private def unitSummand :
    CGWH.point.{u, v} ⟶ (𝟙_ PointedCGWH.{u, v}).right := coprod.inr

/-- The quotient map from the underlying tensor to the pointed smash product. -/
def intervalQuotient (X Y : PointedCGWH.{u, v}) :
    X.right ⊗ Y.right ⟶ (X ⊗ Y).right :=
  (CategoryTheory.Pointed.smashPresentation CGWH.point CGWH.point_isTerminal X Y).2.1.inl

private theorem intervalQuotient_natural {X X' Y Y' : PointedCGWH.{u, v}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    intervalQuotient X Y ≫ (f ⊗ₘ g).right =
      (f.right ⊗ₘ g.right) ≫ intervalQuotient X' Y' := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.smashQuotient_naturality
    CGWH.point CGWH.point_isTerminal f g

private theorem intervalUnit_inv_free :
    freeSummand (𝟙_ CGWH.{u, v}) ≫ intervalFreeCore.εIso.inv.right =
      pointUnitIso.inv ≫ unitSummand := by
  have he : (Under.costarAdjForget CGWH.point.{u, v}).homEquiv
      (𝟙_ CGWH) (𝟙_ PointedCGWH) intervalFreeCore.εIso.inv =
        pointUnitIso.inv ≫ unitSummand := by
    change ((Under.costarAdjForget CGWH.point).homEquiv _ _)
      (((Under.costarAdjForget CGWH.point).homEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at he
  change (Under.costarAdjForget CGWH.point).unit.app (𝟙_ CGWH) ≫
    intervalFreeCore.εIso.inv.right = _ at he
  have hu : (Under.costarAdjForget CGWH.point.{u, v}).unit.app (𝟙_ CGWH) =
      freeSummand (𝟙_ CGWH) := by
    simp [freeSummand, Under.costarAdjForget, Adjunction.comp_unit_app,
      algebraEquivUnder, algebraToUnder, underToAlgebra, coprodMonad, Monad.adj]
  rw [hu] at he
  exact he

private theorem intervalUnit_hom_free :
    unitSummand.{u, v} ≫ intervalFreeCore.εIso.hom.right =
      pointUnitIso.hom ≫ freeSummand (𝟙_ CGWH) := by
  let e := intervalFreeCore.{u, v}.εIso
  have hi : e.hom.right ≫ e.inv.right = 𝟙 _ :=
    congrArg (fun f : 𝟙_ PointedCGWH.{u, v} ⟶ 𝟙_ PointedCGWH => f.right) e.hom_inv_id
  let _ : IsIso e.inv.right := (Under.forget CGWH.point).map_isIso e.inv
  apply (cancel_mono e.inv.right).1
  change (unitSummand ≫ e.hom.right) ≫ e.inv.right =
    (pointUnitIso.hom ≫ freeSummand (𝟙_ CGWH)) ≫ e.inv.right
  simp only [Category.assoc, hi, Category.comp_id]
  change unitSummand = pointUnitIso.hom ≫ freeSummand (𝟙_ CGWH) ≫
    intervalFreeCore.εIso.inv.right
  rw [intervalUnit_inv_free, Iso.hom_inv_id_assoc]

private theorem intervalEndpoint_free (t : unitInterval) :
    unitSummand.{u, v} ≫ (freePointIntervalEndpoint t).right =
      pointUnitIso.hom ≫ CGWH.homotopyIntervalEndpoint t ≫
        freeSummand CGWH.homotopyInterval := by
  change unitSummand ≫ intervalFreeCore.εIso.hom.right ≫
    ((Under.costar CGWH.point).map (CGWH.homotopyIntervalEndpoint t)).right = _
  rw [← Category.assoc, intervalUnit_hom_free]
  change (pointUnitIso.hom ≫ coprod.inr) ≫
    coprod.map (𝟙 CGWH.point) (CGWH.homotopyIntervalEndpoint t) =
      pointUnitIso.hom ≫ CGWH.homotopyIntervalEndpoint t ≫ coprod.inr
  simp only [Category.assoc, coprod.inr_map]

private theorem intervalCollapse_free :
    freeSummand CGWH.homotopyInterval.{u, v} ≫ freePointIntervalCollapse.right =
      CartesianMonoidalCategory.toUnit CGWH.homotopyInterval ≫
        pointUnitIso.inv ≫ unitSummand := by
  change coprod.inr ≫ coprod.map (𝟙 CGWH.point)
    (CartesianMonoidalCategory.toUnit CGWH.homotopyInterval) ≫
      intervalFreeCore.εIso.inv.right = _
  erw [coprod.inr_map_assoc]
  change CartesianMonoidalCategory.toUnit CGWH.homotopyInterval ≫
    freeSummand (𝟙_ CGWH) ≫ intervalFreeCore.εIso.inv.right = _
  rw [intervalUnit_inv_free]

private theorem intervalLeftUnitor_inv_free (X : PointedCGWH.{u, v}) :
    (λ_ X).inv.right = (λ_ X.right).inv ≫ (pointUnitIso.inv ▷ X.right) ≫
      (unitSummand ▷ X.right) ≫ intervalQuotient (𝟙_ PointedCGWH) X := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.smashLeftUnitor_inv_free
    CGWH.point CGWH.point_isTerminal X

@[reassoc]
private theorem intervalLeftUnitor_free_hom (X : PointedCGWH.{u, v}) :
    (pointUnitIso.inv ▷ X.right) ≫ (unitSummand ▷ X.right) ≫
      intervalQuotient (𝟙_ PointedCGWH) X ≫ (λ_ X).hom.right = (λ_ X.right).hom := by
  have hi : (λ_ X).inv.right ≫ (λ_ X).hom.right = 𝟙 _ :=
    congrArg (fun f : X ⟶ X => f.right) (λ_ X).inv_hom_id
  calc
    _ = (λ_ X.right).hom ≫ (λ_ X).inv.right ≫ (λ_ X).hom.right := by
      rw [intervalLeftUnitor_inv_free]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by rw [hi, Category.comp_id]

/-- Restrict through the literal free summand and actual native smash quotient. -/
def freePointIntervalUnderlyingAction {X Y : PointedCGWH.{u, v}}
    (H : (Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ X ⟶ Y) :
    CGWH.homotopyInterval ⊗ X.right ⟶ Y.right :=
  (freeSummand CGWH.homotopyInterval ▷ X.right) ≫
    intervalQuotient ((Under.costar CGWH.point).obj CGWH.homotopyInterval) X ≫ H.right

private theorem intervalEndpoint_quotient (X : PointedCGWH.{u, v}) (t : unitInterval) :
    (λ_ X).inv.right ≫ (freePointIntervalEndpoint t ⊗ₘ 𝟙 X).right =
      (λ_ X.right).inv ≫ (CGWH.homotopyIntervalEndpoint t ▷ X.right) ≫
        (freeSummand CGWH.homotopyInterval ▷ X.right) ≫
          intervalQuotient ((Under.costar CGWH.point).obj CGWH.homotopyInterval) X := by
  have he := congrArg (fun f : CGWH.point.{u, v} ⟶
    ((Under.costar CGWH.point).obj CGWH.homotopyInterval).right => pointUnitIso.inv ≫ f)
      (intervalEndpoint_free.{u, v} t)
  simp only [Iso.inv_hom_id_assoc] at he
  have hq := intervalQuotient_natural (freePointIntervalEndpoint t) (𝟙 X)
  simp only [Under.id_right] at hq
  calc
    _ = (λ_ X.right).inv ≫ (pointUnitIso.inv ▷ X.right) ≫
        (unitSummand ▷ X.right) ≫ intervalQuotient (𝟙_ PointedCGWH) X ≫
          (freePointIntervalEndpoint t ⊗ₘ 𝟙 X).right := by
      rw [intervalLeftUnitor_inv_free]
      simp only [Category.assoc]
    _ = (λ_ X.right).inv ≫
        ((pointUnitIso.inv ≫ unitSummand ≫ (freePointIntervalEndpoint t).right) ▷ X.right) ≫
          intervalQuotient ((Under.costar CGWH.point).obj CGWH.homotopyInterval) X := by
      rw [hq]
      simp only [tensorHom_id, comp_whiskerRight, Category.assoc]
    _ = _ := by rw [he]; simp only [comp_whiskerRight, Category.assoc]

/-- Preserve the complete native endpoint from the original pointed endpoint equation. -/
theorem freePointIntervalUnderlyingAction_endpoint {X Y : PointedCGWH.{u, v}}
    (H : (Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ X ⟶ Y)
    (t : unitInterval) (f : X ⟶ Y)
    (he : (λ_ X).inv ≫ (freePointIntervalEndpoint t ⊗ₘ 𝟙 X) ≫ H = f) :
    (λ_ X.right).inv ≫ (CGWH.homotopyIntervalEndpoint t ⊗ₘ 𝟙 X.right) ≫
      freePointIntervalUnderlyingAction H = f.right := by
  have h := congrArg (fun g : X ⟶ Y => g.right) he
  simp only [Under.comp_right] at h
  have hd := congrArg (fun g : X.right ⟶
    ((Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ X).right => g ≫ H.right)
      (intervalEndpoint_quotient X t)
  calc
    _ = ((λ_ X).inv.right ≫ (freePointIntervalEndpoint t ⊗ₘ 𝟙 X).right) ≫ H.right := by
      simpa only [freePointIntervalUnderlyingAction, tensorHom_id, Category.assoc] using hd.symm
    _ = f.right := by simpa only [Category.assoc] using h

/-- Preserve the entire original source-fixing equation through the actual underlying quotient. -/
theorem freePointIntervalUnderlyingAction_fix {S X Y : PointedCGWH.{u, v}}
    (H : (Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ X ⟶ Y)
    (i : S ⟶ X) (j : S ⟶ Y)
    (hfix : (𝟙 _ ⊗ₘ i) ≫ H =
      (freePointIntervalCollapse ⊗ₘ 𝟙 S) ≫ (λ_ S).hom ≫ j) :
    (𝟙 CGWH.homotopyInterval ⊗ₘ i.right) ≫ freePointIntervalUnderlyingAction H =
      (CartesianMonoidalCategory.toUnit CGWH.homotopyInterval ⊗ₘ 𝟙 S.right) ≫
        (λ_ S.right).hom ≫ j.right := by
  have hf := congrArg (fun f : (Under.costar CGWH.point).obj
    CGWH.homotopyInterval ⊗ S ⟶ Y => f.right) hfix
  simp only [Under.comp_right] at hf
  have hn : intervalQuotient ((Under.costar CGWH.point).obj CGWH.homotopyInterval) S ≫
      (𝟙 ((Under.costar CGWH.point).obj CGWH.homotopyInterval) ⊗ₘ i).right =
    (((Under.costar CGWH.point).obj CGWH.homotopyInterval).right ◁ i.right) ≫
      intervalQuotient ((Under.costar CGWH.point).obj CGWH.homotopyInterval) X := by
    simpa only [Under.id_right, id_tensorHom] using intervalQuotient_natural
      (𝟙 ((Under.costar CGWH.point).obj CGWH.homotopyInterval)) i
  have hnH := congrArg (fun g :
    ((Under.costar CGWH.point).obj CGWH.homotopyInterval).right ⊗ S.right ⟶
      ((Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ X).right => g ≫ H.right) hn
  simp only [Category.assoc] at hnH
  have hc : intervalQuotient ((Under.costar CGWH.point).obj CGWH.homotopyInterval) S ≫
      (freePointIntervalCollapse ⊗ₘ 𝟙 S).right =
    (freePointIntervalCollapse.right ▷ S.right) ≫ intervalQuotient (𝟙_ PointedCGWH) S := by
    simpa only [Under.id_right, tensorHom_id] using
      intervalQuotient_natural freePointIntervalCollapse (𝟙 S)
  have hcR := congrArg (fun g :
    ((Under.costar CGWH.point).obj CGWH.homotopyInterval).right ⊗ S.right ⟶
      (𝟙_ PointedCGWH ⊗ S).right => g ≫ (λ_ S).hom.right ≫ j.right) hc
  simp only [Category.assoc] at hcR
  unfold freePointIntervalUnderlyingAction
  simp only [id_tensorHom, tensorHom_id]
  rw [whisker_exchange_assoc, ← hnH, hf, hcR]
  rw [← comp_whiskerRight_assoc, intervalCollapse_free]
  simp only [comp_whiskerRight, Category.assoc]
  rw [intervalLeftUnitor_free_hom_assoc]

/-- Change only the interval through the actual oriented inverse native comparison. -/
def freePointIntervalOrdinaryAction {X Y : PointedCGWH.{u, v}}
    (H : (Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ X ⟶ Y) :
    CGWH.interval ⊗ X.right ⟶ Y.right :=
  (CGWH.homotopyIntervalIsoInterval.inv ▷ X.right) ≫ freePointIntervalUnderlyingAction H

private theorem intervalComparison_inv_zero :
    (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ CGWH.intervalZero) ≫
      CGWH.homotopyIntervalIsoInterval.inv = CGWH.homotopyIntervalEndpoint 0 := by
  rw [← CGWH.homotopyIntervalIsoInterval_zero, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem intervalComparison_inv_one :
    (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ CGWH.intervalOne) ≫
      CGWH.homotopyIntervalIsoInterval.inv = CGWH.homotopyIntervalEndpoint 1 := by
  rw [← CGWH.homotopyIntervalIsoInterval_one, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem ordinaryIntervalAction_endpoint {X Y : PointedCGWH.{u, v}}
    (H : (Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ X ⟶ Y)
    (t : unitInterval) (e : 𝟙_ CGWH.{u, v} ⟶ CGWH.interval)
    (he : e ≫ CGWH.homotopyIntervalIsoInterval.inv = CGWH.homotopyIntervalEndpoint t)
    (f : X ⟶ Y)
    (hf : (λ_ X).inv ≫ (freePointIntervalEndpoint t ⊗ₘ 𝟙 X) ≫ H = f) :
    (λ_ X.right).inv ≫ (e ▷ X.right) ≫ freePointIntervalOrdinaryAction H = f.right := by
  unfold freePointIntervalOrdinaryAction
  calc
    _ = (λ_ X.right).inv ≫ ((e ≫ CGWH.homotopyIntervalIsoInterval.inv) ▷ X.right) ≫
        freePointIntervalUnderlyingAction H := by
      simp only [comp_whiskerRight, Category.assoc]
    _ = _ := by
      rw [he]
      simpa only [tensorHom_id] using freePointIntervalUnderlyingAction_endpoint H t f hf

private theorem ordinaryIntervalAction_fix {S X Y : PointedCGWH.{u, v}}
    (H : (Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ X ⟶ Y)
    (i : S ⟶ X) (j : S ⟶ Y)
    (hfix : (𝟙 _ ⊗ₘ i) ≫ H =
      (freePointIntervalCollapse ⊗ₘ 𝟙 S) ≫ (λ_ S).hom ≫ j) :
    (𝟙 CGWH.interval ⊗ₘ i.right) ≫ freePointIntervalOrdinaryAction H =
      (CartesianMonoidalCategory.toUnit CGWH.interval ⊗ₘ 𝟙 S.right) ≫
        (λ_ S.right).hom ≫ j.right := by
  have hr := freePointIntervalUnderlyingAction_fix H i j hfix
  simp only [id_tensorHom, tensorHom_id] at hr ⊢
  unfold freePointIntervalOrdinaryAction
  rw [whisker_exchange_assoc, hr, ← comp_whiskerRight_assoc]
  have hc : CGWH.homotopyIntervalIsoInterval.inv ≫
      CartesianMonoidalCategory.toUnit CGWH.homotopyInterval =
        CartesianMonoidalCategory.toUnit CGWH.interval :=
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  rw [hc]

/-- The actual pointed endpoint data gives an ordinary jointly continuous homotopy. -/
def freePointIntervalActionHomotopy {X Y : PointedCGWH.{u, v}}
    (f₀ f₁ : X ⟶ Y)
    (H : (Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ X ⟶ Y)
    (h₀ : (λ_ X).inv ≫ (freePointIntervalEndpoint 0 ⊗ₘ 𝟙 X) ≫ H = f₀)
    (h₁ : (λ_ X).inv ≫ (freePointIntervalEndpoint 1 ⊗ₘ 𝟙 X) ≫ H = f₁) :
    ContinuousMap.Homotopy
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₀.right)
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₁.right) :=
  CGWH.intervalActionHomotopy f₀.right f₁.right (freePointIntervalOrdinaryAction H)
    (by exact ordinaryIntervalAction_endpoint H 0 _ intervalComparison_inv_zero f₀ h₀)
    (by exact ordinaryIntervalAction_endpoint H 1 _ intervalComparison_inv_one f₁ h₁)

/-- The ordinary homotopy retains the actual native transpose and path landing formula. -/
theorem freePointIntervalActionHomotopy_apply {X Y : PointedCGWH.{u, v}}
    (f₀ f₁ : X ⟶ Y)
    (H : (Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ X ⟶ Y)
    (h₀ : (λ_ X).inv ≫ (freePointIntervalEndpoint 0 ⊗ₘ 𝟙 X) ≫ H = f₀)
    (h₁ : (λ_ X).inv ≫ (freePointIntervalEndpoint 1 ⊗ₘ 𝟙 X) ≫ H = f₁)
    (t : unitInterval) (x : X.right) :
    freePointIntervalActionHomotopy f₀ f₁ H h₀ h₁ (t, x) =
      CGWH.pathLanding Y.right (MonoidalClosed.curry (freePointIntervalOrdinaryAction H) x)
        (TopCat.I.homeomorph.symm t) := rfl

/-- Every original source point remains fixed at every ordinary homotopy time. -/
theorem freePointIntervalActionHomotopy_fixed {S X Y : PointedCGWH.{u, v}}
    (f₀ f₁ : X ⟶ Y)
    (H : (Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ X ⟶ Y)
    (h₀ : (λ_ X).inv ≫ (freePointIntervalEndpoint 0 ⊗ₘ 𝟙 X) ≫ H = f₀)
    (h₁ : (λ_ X).inv ≫ (freePointIntervalEndpoint 1 ⊗ₘ 𝟙 X) ≫ H = f₁)
    (i : S ⟶ X) (j : S ⟶ Y)
    (hfix : (𝟙 _ ⊗ₘ i) ≫ H =
      (freePointIntervalCollapse ⊗ₘ 𝟙 S) ≫ (λ_ S).hom ≫ j)
    (t : unitInterval) (s : S.right) :
    freePointIntervalActionHomotopy f₀ f₁ H h₀ h₁ (t, i.right s) = j.right s := by
  exact CGWH.intervalActionHomotopy_fixed f₀.right f₁.right
    (freePointIntervalOrdinaryAction H)
    (ordinaryIntervalAction_endpoint H 0 _ intervalComparison_inv_zero f₀ h₀)
    (ordinaryIntervalAction_endpoint H 1 _ intervalComparison_inv_one f₁ h₁)
    i.right j.right (ordinaryIntervalAction_fix H i j hfix) t s

/-- The same original action and fixing data gives a relative homotopy on the full source image. -/
def freePointIntervalActionHomotopyRel {S X Y : PointedCGWH.{u, v}}
    (f₀ f₁ : X ⟶ Y)
    (H : (Under.costar CGWH.point).obj CGWH.homotopyInterval ⊗ X ⟶ Y)
    (h₀ : (λ_ X).inv ≫ (freePointIntervalEndpoint 0 ⊗ₘ 𝟙 X) ≫ H = f₀)
    (h₁ : (λ_ X).inv ≫ (freePointIntervalEndpoint 1 ⊗ₘ 𝟙 X) ≫ H = f₁)
    (i : S ⟶ X) (j : S ⟶ Y)
    (hfix : (𝟙 _ ⊗ₘ i) ≫ H =
      (freePointIntervalCollapse ⊗ₘ 𝟙 S) ≫ (λ_ S).hom ≫ j) :
    ContinuousMap.HomotopyRel
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₀.right)
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₁.right)
      (Set.range (ConcreteCategory.hom (C := CGWH.{u, v}) i.right)) :=
  CGWH.intervalActionHomotopyRel f₀.right f₁.right (freePointIntervalOrdinaryAction H)
    (by exact ordinaryIntervalAction_endpoint H 0 _ intervalComparison_inv_zero f₀ h₀)
    (by exact ordinaryIntervalAction_endpoint H 1 _ intervalComparison_inv_one f₁ h₁)
    i.right j.right (by exact ordinaryIntervalAction_fix H i j hfix)

end PointedCGWH
