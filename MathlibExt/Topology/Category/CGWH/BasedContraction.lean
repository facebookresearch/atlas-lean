/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.CGWH.PathLanding
import MathlibExt.Topology.Category.TopCat.ContractionLoopHomotopyEquiv

/-!
# Based contractions in CGWH

A based contraction is native path data from every point to a chosen point,
fixed at that point.  Native path landing turns it into the existing ordinary
`TopCat.BasedContraction`.  No contraction is inferred from bare
contractibility.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Topology

namespace CGWH

/-- A native contraction of `E` to the chosen point `e`, fixed at `e`. -/
structure BasedContraction (E : CGWH.{u, v})
    (e : CGWH.point.{u, v} ⟶ E) where
  path : E ⟶ CGWH.path.obj E
  evalZero : path ≫ CGWH.pathEvalZero.app E = 𝟙 E
  evalOne : path ≫ CGWH.pathEvalOne.app E =
    CGWH.point_isTerminal.from E ≫ e
  fixed : e ≫ path = e ≫ CGWH.pathConstant.app E

namespace BasedContraction

variable {E B : CGWH.{u, v}} {e : CGWH.point.{u, v} ⟶ E}

/-- Project a based contraction path along a morphism. -/
noncomputable def projectedPath (H : BasedContraction E e) (p : E ⟶ B) :
    E ⟶ CGWH.path.obj B :=
  H.path ≫ CGWH.path.map p

/-- A projected contraction path starts at the projected point. -/
theorem projectedPath_evalZero (H : BasedContraction E e) (p : E ⟶ B) :
    H.projectedPath p ≫ CGWH.pathEvalZero.app B = p := by
  unfold projectedPath
  rw [Category.assoc, CGWH.pathEvalZero.naturality]
  rw [← Category.assoc, H.evalZero, Category.id_comp]
  simp only [Functor.id_map]

/-- A projected contraction path ends at its chosen target point. -/
theorem projectedPath_evalOne (H : BasedContraction E e) (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) (over : e ≫ p = b) :
    H.projectedPath p ≫ CGWH.pathEvalOne.app B =
      CGWH.point_isTerminal.from E ≫ b := by
  unfold projectedPath
  rw [Category.assoc, CGWH.pathEvalOne.naturality]
  simp only [Functor.id_map]
  rw [← Category.assoc, H.evalOne, Category.assoc, over]

/-- The projected contraction path remains constant at the chosen point. -/
theorem projectedPath_fixed (H : BasedContraction E e) (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) (over : e ≫ p = b) :
    e ≫ H.projectedPath p = b ≫ CGWH.pathConstant.app B := by
  unfold projectedPath
  rw [← Category.assoc, H.fixed, Category.assoc]
  rw [← CGWH.pathConstant.naturality]
  simp only [Functor.id_map]
  rw [← Category.assoc, over]

/-- Land a native based contraction as an ordinary compact-open TopCat
contraction. -/
noncomputable def toTopCat (H : BasedContraction E e) :
    TopCat.BasedContraction (CGWH.cgwhToTop.obj E) (e PUnit.unit) where
  homotopy :=
    { toFun := fun z =>
        CGWH.pathLanding E (H.path z.2) (TopCat.I.homeomorph.symm z.1)
      continuous_toFun := by
        let landed : CGWH.cgwhToTop.obj E ⟶
            TopCat.pathObject (CGWH.cgwhToTop.obj E) :=
          CGWH.cgwhToTop.map H.path ≫ CGWH.pathLanding E
        exact landed.hom.uncurry.continuous.comp
          (continuous_snd.prodMk
            (TopCat.I.homeomorph.symm.continuous.comp continuous_fst))
      map_zero_left := by
        intro x
        have hz : TopCat.I.homeomorph.symm (0 : unitInterval) =
            (0 : TopCat.I.{v}) := by
          apply TopCat.I.homeomorph.injective
          simp
        rw [hz]
        have hLanding := ConcreteCategory.congr_hom
          (CGWH.pathLanding_evalZero E) (H.path x)
        have hNative := ConcreteCategory.congr_hom H.evalZero x
        exact hLanding.trans hNative
      map_one_left := by
        intro x
        have ho : TopCat.I.homeomorph.symm (1 : unitInterval) =
            (1 : TopCat.I.{v}) := by
          apply TopCat.I.homeomorph.injective
          simp
        rw [ho]
        have hLanding := ConcreteCategory.congr_hom
          (CGWH.pathLanding_evalOne E) (H.path x)
        have hNative := ConcreteCategory.congr_hom H.evalOne x
        exact hLanding.trans hNative }
  fixed := by
    intro t
    let pt : (CGWH.point.{u, v} : Type v) := by
      change PUnit.{v + 1}
      exact PUnit.unit
    have hfixed := ConcreteCategory.congr_hom H.fixed pt
    change H.path (e pt) = CGWH.pathConstant.app E (e pt) at hfixed
    change CGWH.pathLanding E (H.path (e pt))
      (TopCat.I.homeomorph.symm t) = e pt
    rw [hfixed, CGWH.pathLanding_constant_apply]

/-- Carrier formula for the ordinary homotopy underlying `toTopCat`. -/
@[simp]
theorem toTopCat_homotopy_apply (H : BasedContraction E e)
    (t : unitInterval) (x : E) :
    H.toTopCat.homotopy (t, x) =
      CGWH.pathLanding E (H.path x) (TopCat.I.homeomorph.symm t) :=
  rfl

end BasedContraction

end CGWH
