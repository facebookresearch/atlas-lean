/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBasepointChange

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace TopCat

#check @TopCat.homotopyFiberBasepointChange_id_homotopy.{u}
#check @TopCat.homotopyFiberBasepointChange_comp_homotopy.{u}

example {X B : TopCat.{u}} (f : X ⟶ B) (b : B) :
    TopCat.homotopyFiberBasepointChange_id_homotopy f b =
      TopCat.homotopyFiberBasepointChangeIdHomotopy f b := rfl

example {X B : TopCat.{u}} (f : X ⟶ B) {b₀ b₁ b₂ : B}
    (p : Path b₀ b₁) (q : Path b₁ b₂) :
    TopCat.homotopyFiberBasepointChange_comp_homotopy f p q =
      TopCat.homotopyFiberBasepointChangeCompHomotopy f p q := rfl

private def testFiberRootPath
    {X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (z : homotopyFiber f b) :
    Path (f (homotopyFiberToTotal f b z)) b where
  toFun s := homotopyFiberPath f b z (TopCat.I.homeomorph.symm s)
  continuous_toFun :=
    (homotopyFiberPath f b z).continuous.comp
      TopCat.I.homeomorph.symm.continuous
  source' := by
    have h := ConcreteCategory.congr_hom
      (homotopyPullbackPath_evalZero f
        (TopCat.const (X := TopCat.of PUnit) b)) z
    exact h
  target' := by
    have hOne : TopCat.I.homeomorph.symm (1 : unitInterval) =
        (1 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    have h := ConcreteCategory.congr_hom
      (homotopyPullbackPath_evalOne f
        (TopCat.const (X := TopCat.of PUnit) b)) z
    change homotopyFiberPath f b z
      (TopCat.I.homeomorph.symm 1) = b
    rw [hOne]
    exact h

section Symbolic

variable {X B : TopCat.{u}} (f : X ⟶ B)
variable {b₀ b₁ b₂ : B}

example (q : Path b₀ b₁) :
    homotopyFiber f b₀ ⟶ homotopyFiber f b₁ :=
  homotopyFiberBasepointChange f q

example (q : Path b₀ b₁) :
    homotopyFiberBasepointChange f q ≫ homotopyFiberToTotal f b₁ =
      homotopyFiberToTotal f b₀ := by
  apply homotopyFiberBasepointChange_toTotal

example (q : Path b₀ b₁) (z : homotopyFiber f b₀)
    (t : TopCat.I.{u}) :
    homotopyFiberPath f b₁ (homotopyFiberBasepointChange f q z) t =
      ((testFiberRootPath f b₀ z).trans q) (TopCat.I.homeomorph t) := by
  simpa [testFiberRootPath] using
    homotopyFiberBasepointChange_path f q z t

example : ContinuousMap.Homotopy
    (homotopyFiberBasepointChange f (Path.refl b₀)).hom
    ((𝟙 (homotopyFiber f b₀) :
      homotopyFiber f b₀ ⟶ homotopyFiber f b₀).hom) :=
  homotopyFiberBasepointChangeIdHomotopy f b₀

example (q₀₁ : Path b₀ b₁) (q₁₂ : Path b₁ b₂) :
    ContinuousMap.Homotopy
      (homotopyFiberBasepointChange f q₀₁ ≫
        homotopyFiberBasepointChange f q₁₂).hom
      (homotopyFiberBasepointChange f (q₀₁.trans q₁₂)).hom :=
  homotopyFiberBasepointChangeCompHomotopy f q₀₁ q₁₂

example {A : TopCat.{u}}
    (source target : A ⟶ homotopyFiber f b₀)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1)
    (htotal : source ≫ homotopyFiberToTotal f b₀ =
      target ≫ homotopyFiberToTotal f b₀)
    (hpath : ∀ (a : A) (t : TopCat.I.{u}),
      (source ≫ homotopyFiberPath f b₀) a t =
        (target ≫ homotopyFiberPath f b₀) a
          (TopCat.I.homeomorph.symm (r (TopCat.I.homeomorph t)))) :
    ContinuousMap.Homotopy source.hom target.hom :=
  homotopyFiberReparamHomotopy f b₀ source target r hr hr0 hr1
    htotal hpath

end Symbolic

section Concrete

private abbrev Interval : TopCat.{0} := TopCat.of unitInterval
private abbrev Point : TopCat.{0} := TopCat.of PUnit

private def zeroMap : Point ⟶ Interval := TopCat.const 0

private def intervalPath : Path (0 : Interval) (1 : Interval) where
  toFun := id
  continuous_toFun := continuous_id
  source' := rfl
  target' := rfl

example : homotopyFiber zeroMap 0 ⟶ homotopyFiber zeroMap 1 :=
  homotopyFiberBasepointChange zeroMap intervalPath

example : homotopyFiber zeroMap 1 ⟶ homotopyFiber zeroMap 0 :=
  homotopyFiberBasepointChange zeroMap intervalPath.symm

example : ContinuousMap.Homotopy
    (homotopyFiberBasepointChange zeroMap intervalPath ≫
      homotopyFiberBasepointChange zeroMap intervalPath.symm).hom
    (homotopyFiberBasepointChange zeroMap
      (intervalPath.trans intervalPath.symm)).hom :=
  homotopyFiberBasepointChangeCompHomotopy zeroMap
    intervalPath intervalPath.symm

example : ContinuousMap.Homotopy
    (homotopyFiberBasepointChange zeroMap
      (Path.refl (0 : Interval))).hom
    ((𝟙 (homotopyFiber zeroMap 0) :
      homotopyFiber zeroMap 0 ⟶ homotopyFiber zeroMap 0).hom) :=
  homotopyFiberBasepointChangeIdHomotopy zeroMap 0

end Concrete

section UniverseOne

variable {X B : TopCat.{1}} (f : X ⟶ B)
variable {b₀ b₁ b₂ : B}

example (q : Path b₀ b₁) :
    homotopyFiber f b₀ ⟶ homotopyFiber f b₁ :=
  homotopyFiberBasepointChange f q

example (q : Path b₀ b₁) :
    homotopyFiberBasepointChange f q ≫ homotopyFiberToTotal f b₁ =
      homotopyFiberToTotal f b₀ := by
  apply homotopyFiberBasepointChange_toTotal

example (q : Path b₀ b₁) (z : homotopyFiber f b₀)
    (t : TopCat.I.{1}) :
    homotopyFiberPath f b₁ (homotopyFiberBasepointChange f q z) t =
      ((testFiberRootPath f b₀ z).trans q) (TopCat.I.homeomorph t) := by
  simpa [testFiberRootPath] using
    homotopyFiberBasepointChange_path f q z t

example : ContinuousMap.Homotopy
    (homotopyFiberBasepointChange f (Path.refl b₀)).hom
    ((𝟙 (homotopyFiber f b₀) :
      homotopyFiber f b₀ ⟶ homotopyFiber f b₀).hom) :=
  homotopyFiberBasepointChangeIdHomotopy f b₀

example (q₀₁ : Path b₀ b₁) (q₁₂ : Path b₁ b₂) :
    ContinuousMap.Homotopy
      (homotopyFiberBasepointChange f q₀₁ ≫
        homotopyFiberBasepointChange f q₁₂).hom
      (homotopyFiberBasepointChange f (q₀₁.trans q₁₂)).hom :=
  homotopyFiberBasepointChangeCompHomotopy f q₀₁ q₁₂

end UniverseOne

section UniverseZero

variable {X B : TopCat.{0}} (f : X ⟶ B)
variable {b₀ b₁ b₂ : B}

example (q : Path b₀ b₁) :
    homotopyFiber f b₀ ⟶ homotopyFiber f b₁ :=
  homotopyFiberBasepointChange f q

example (q : Path b₀ b₁) :
    homotopyFiberBasepointChange f q ≫ homotopyFiberToTotal f b₁ =
      homotopyFiberToTotal f b₀ := by
  apply homotopyFiberBasepointChange_toTotal

example (q : Path b₀ b₁) (z : homotopyFiber f b₀)
    (t : TopCat.I.{0}) :
    homotopyFiberPath f b₁ (homotopyFiberBasepointChange f q z) t =
      ((testFiberRootPath f b₀ z).trans q) (TopCat.I.homeomorph t) := by
  simpa [testFiberRootPath] using
    homotopyFiberBasepointChange_path f q z t

example : ContinuousMap.Homotopy
    (homotopyFiberBasepointChange f (Path.refl b₀)).hom
    ((𝟙 (homotopyFiber f b₀) :
      homotopyFiber f b₀ ⟶ homotopyFiber f b₀).hom) :=
  homotopyFiberBasepointChangeIdHomotopy f b₀

example (q₀₁ : Path b₀ b₁) (q₁₂ : Path b₁ b₂) :
    ContinuousMap.Homotopy
      (homotopyFiberBasepointChange f q₀₁ ≫
        homotopyFiberBasepointChange f q₁₂).hom
      (homotopyFiberBasepointChange f (q₀₁.trans q₁₂)).hom :=
  homotopyFiberBasepointChangeCompHomotopy f q₀₁ q₁₂

end UniverseZero

/-! Private implementation names do not escape the public import. -/

/-- error: Unknown constant `TopCat.fiberRootPath` -/
#guard_msgs (error) in
#check TopCat.fiberRootPath

/-- error: Unknown constant `TopCat.appendFiberPath` -/
#guard_msgs (error) in
#check TopCat.appendFiberPath

/-- error: Unknown constant `TopCat.reparamPathFamily` -/
#guard_msgs (error) in
#check TopCat.reparamPathFamily

/-- error: Unknown constant `TopCat.homotopyFiberReparamLift` -/
#guard_msgs (error) in
#check TopCat.homotopyFiberReparamLift

/-- error: Unknown constant `TopCat.homotopyFiberReparamHomotopyAux` -/
#guard_msgs (error) in
#check TopCat.homotopyFiberReparamHomotopyAux

/-- error: Unknown constant `TopCat.transReflReparam` -/
#guard_msgs (error) in
#check TopCat.transReflReparam

/-- error: Unknown constant `TopCat.assocReparam` -/
#guard_msgs (error) in
#check TopCat.assocReparam

#check homotopyFiberBasepointChange
#check homotopyFiberBasepointChange_toTotal
#check homotopyFiberBasepointChange_path
#check homotopyFiberBasepointChangeIdHomotopy
#check homotopyFiberBasepointChangeCompHomotopy
#check @homotopyFiberReparamHomotopy.{u}
#check @homotopyFiberReparamHomotopy.{1}
#check @homotopyFiberReparamHomotopy.{0}

#print axioms homotopyFiberBasepointChange
#print axioms homotopyFiberBasepointChange_toTotal
#print axioms homotopyFiberBasepointChange_path
#print axioms homotopyFiberBasepointChangeIdHomotopy
#print axioms homotopyFiberBasepointChangeCompHomotopy
#print axioms homotopyFiberReparamHomotopy

end TopCat
