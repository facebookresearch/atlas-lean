/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Category
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SerreFiberLoop
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The entire original native pointed-Serre sequence functor

The actual full subcategory of original pointed fibrations retains every
whole original Arrow square. Its original singular functor constructs the
same genuine pointed Kan fibration sequence, and every square retains both
actual singular maps and both original chosen points. All identity and
composition laws follow from the original singular functor.

No fibration, point, exactness or model dictionary is supplied beyond the
actual original pointed fibration membership.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory Simplicial

namespace PointedCGWH.SerreSequenceGeometry

/-- The actual property is membership in the original native pointed fibration class. -/
def fibrationArrowProperty : ObjectProperty (Arrow PointedCGWH.{u, v}) :=
  fun F => fibrations PointedCGWH.{u, v} F.hom

/-- Objects and all whole original squares in the actual native pointed-fibration subcategory. -/
abbrev FibrationArrow := (fibrationArrowProperty.{u, v}).FullSubcategory

/-- The actual full Arrow inclusion forgets only the proved original fibration membership. -/
def arrowFunctor : FibrationArrow.{u, v} ⥤ Arrow PointedCGWH.{u, v} :=
  (fibrationArrowProperty.{u, v}).ι

/-- The same original Arrow object has its actual original native fibration instance. -/
instance originalFibration (F : FibrationArrow.{u, v}) : Fibration F.obj.hom :=
  (HomotopicalAlgebra.fibration_iff F.obj.hom).mpr F.property

/-- The actual underlying CGWH map is the same original native Serre fibration. -/
instance underlyingFibration (F : FibrationArrow.{u, v}) : Fibration F.obj.hom.right :=
  (PointedCGWH.fibration_iff F.obj.hom).mp inferInstance

/-- The entire original underlying singular functor retains its actual native CGWH inclusion. -/
abbrev underlyingSingularFunctor : CGWH.{u, v} ⥤ SSet.{v} :=
  CGWH.cgwhToTop ⋙ TopCat.toSSet

/-- The original whole native pointed fibration has its actual chosen-point singular sequence. -/
def sequence (F : FibrationArrow.{u, v}) : SSet.FibrationSequence.{v} :=
  PointedCGWH.FiberGeometry.nativeSerreFibrationSequence F.obj.hom.right
    F.obj.right.hom F.obj.left.hom (Under.w F.obj.hom)

/-- The actual original sequence projection is the literal original whole singular map. -/
theorem sequence_projection (F : FibrationArrow.{u, v}) :
    (sequence F).p = underlyingSingularFunctor.map F.obj.hom.right := rfl

/-- Every whole original native square gives both actual singular maps and both original points. -/
def sequenceMap {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    SSet.FibrationSequenceHom (sequence F) (sequence G) where
  totalMap := underlyingSingularFunctor.map q.hom.left.right
  baseMap := underlyingSingularFunctor.map q.hom.right.right
  comm := by
    have h : q.hom.left.right ≫ G.obj.hom.right = F.obj.hom.right ≫ q.hom.right.right := by
      simpa only [Under.comp_right] using
        congrArg (fun (a : F.obj.left ⟶ G.obj.right) => a.right) (Arrow.w q.hom)
    change underlyingSingularFunctor.map q.hom.left.right ≫
        underlyingSingularFunctor.map G.obj.hom.right =
      underlyingSingularFunctor.map F.obj.hom.right ≫
        underlyingSingularFunctor.map q.hom.right.right
    rw [← underlyingSingularFunctor.map_comp, ← underlyingSingularFunctor.map_comp, h]
  total_pt := by
    change TopCat.toSSetObj₀Equiv.symm (q.hom.left.right (F.obj.left.hom PUnit.unit)) =
      TopCat.toSSetObj₀Equiv.symm (G.obj.left.hom PUnit.unit)
    exact congrArg TopCat.toSSetObj₀Equiv.symm
      (ConcreteCategory.congr_hom (Under.w q.hom.left) PUnit.unit)
  base_pt := by
    change TopCat.toSSetObj₀Equiv.symm (q.hom.right.right (F.obj.right.hom PUnit.unit)) =
      TopCat.toSSetObj₀Equiv.symm (G.obj.right.hom PUnit.unit)
    exact congrArg TopCat.toSSetObj₀Equiv.symm
      (ConcreteCategory.congr_hom (Under.w q.hom.right) PUnit.unit)

/-- The full original singular sequence square has the exact original total-space map. -/
theorem sequenceMap_total {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (sequenceMap q).totalMap = underlyingSingularFunctor.map q.hom.left.right := rfl

/-- The full original singular sequence square has the exact original base-space map. -/
theorem sequenceMap_base {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (sequenceMap q).baseMap = underlyingSingularFunctor.map q.hom.right.right := rfl

/-- All actual original pointed fibrations and whole original squares form
the true sequence functor. -/
def sequenceFunctor : FibrationArrow.{u, v} ⥤ SSet.FibrationSequence.{v} where
  obj F := sequence F
  map q := sequenceMap q
  map_id F := by
    apply SSet.FibrationSequence.Geometry.hom_ext
    · change underlyingSingularFunctor.map (𝟙 F.obj.left.right) = 𝟙 _
      exact underlyingSingularFunctor.map_id F.obj.left.right
    · change underlyingSingularFunctor.map (𝟙 F.obj.right.right) = 𝟙 _
      exact underlyingSingularFunctor.map_id F.obj.right.right
  map_comp q r := by
    apply SSet.FibrationSequence.Geometry.hom_ext
    · change underlyingSingularFunctor.map (q.hom.left.right ≫ r.hom.left.right) =
        underlyingSingularFunctor.map q.hom.left.right ≫
          underlyingSingularFunctor.map r.hom.left.right
      exact underlyingSingularFunctor.map_comp q.hom.left.right r.hom.left.right
    · change underlyingSingularFunctor.map (q.hom.right.right ≫ r.hom.right.right) =
        underlyingSingularFunctor.map q.hom.right.right ≫
          underlyingSingularFunctor.map r.hom.right.right
      exact underlyingSingularFunctor.map_comp q.hom.right.right r.hom.right.right

/-- The whole sequence functor keeps the exact original pointed total-space vertex. -/
theorem sequenceFunctor_total_point (F : FibrationArrow.{u, v}) :
    (sequenceFunctor.obj F).e =
      TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv F.obj.left.right F.obj.left.hom) := rfl

/-- The whole sequence functor keeps the exact original pointed base-space vertex. -/
theorem sequenceFunctor_base_point (F : FibrationArrow.{u, v}) :
    (sequenceFunctor.obj F).b =
      TopCat.toSSetObj₀Equiv.symm (CGWH.pointHomEquiv F.obj.right.right F.obj.right.hom) := rfl

/-- Every whole original source square preserves the exact original total-space point. -/
theorem sequenceFunctor_map_total_point {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (sequenceFunctor.map q).totalMap.app _ (sequence F).e = (sequence G).e :=
  (sequenceFunctor.map q).total_pt

/-- Every whole original source square preserves the exact original base-space point. -/
theorem sequenceFunctor_map_base_point {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (sequenceFunctor.map q).baseMap.app _ (sequence F).b = (sequence G).b :=
  (sequenceFunctor.map q).base_pt

end PointedCGWH.SerreSequenceGeometry
