/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogCurveFamilies
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The concrete category of log structures on a fixed marked nodal family

Arrows are actual base/curve log-sheaf maps over the identity ring maps,
compatible with the fixed projection. The basic log curve is its initial
object, so extra unrelated base log factors are excluded by the output
universal property. References: F. Kato, log smooth curves;
Gross--Siebert arXiv:1102.4322v2, §1.2 and the universal basic-curve discussion.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.BasicLogCurves
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EtaleLogDiagrams
open MathlibExt.AlgebraicGeometry.SmallEtaleGeometry
open MathlibExt.AlgebraicGeometry.LogCurveFamilies
open MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

variable [InverseImageTheory.{0}]
variable {T : Scheme.{0}} {n g : ℕ} {F : MarkedFamily T n g}

structure CurveHom (C D : LogCurve F) where
  baseMap : C.baseLog ⟶ D.baseLog
  curveMap : C.curveLog ⟶ D.curveLog
  projection : baseMap.hom.left ≫ D.projection.left = C.projection.left ≫
    ((etaleBaseChange F.π).sheafPushforwardContinuous CommMonCat
      T.smallEtaleTopology F.X.smallEtaleTopology).map curveMap.hom.left

@[ext] theorem CurveHom.ext {C D : LogCurve F} {a b : CurveHom C D}
    (hb : a.baseMap = b.baseMap) (hc : a.curveMap = b.curveMap) : a = b := by
  cases a; cases b; cases hb; cases hc; rfl

instance : Category (LogCurve F) where
  Hom C D := CurveHom C D
  id C := ⟨𝟙 _, 𝟙 _, by simp⟩
  comp a b := ⟨a.baseMap ≫ b.baseMap, a.curveMap ≫ b.curveMap, by
    change (a.baseMap.hom.left ≫ b.baseMap.hom.left) ≫ _ =
      _ ≫ ((etaleBaseChange F.π).sheafPushforwardContinuous CommMonCat
        T.smallEtaleTopology F.X.smallEtaleTopology).map (a.curveMap.hom.left ≫ b.curveMap.hom.left)
    rw [Category.assoc, b.projection, ← Category.assoc, a.projection,
      Category.assoc, ← _root_.CategoryTheory.Functor.map_comp]⟩
  id_comp a := by apply CurveHom.ext <;> simp
  comp_id a := by apply CurveHom.ext <;> simp
  assoc a b c := by apply CurveHom.ext <;> exact Category.assoc _ _ _

/-- The constructor's output is a universal log curve, not an arbitrary
choice of additional log factors on the same ordinary family. -/
structure BasicLogCurve (F : MarkedFamily T n g) where
  curve : LogCurve F
  initial : IsInitial curve

end MathlibExt.AlgebraicGeometry.BasicLogCurves
