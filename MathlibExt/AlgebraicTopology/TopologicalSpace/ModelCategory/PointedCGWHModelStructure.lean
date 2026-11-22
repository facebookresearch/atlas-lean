/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.Under
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelStructure
public import MathlibExt.Topology.Category.PointedCGWH.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# The model structure on pointed CGWH spaces

This file specializes the generic model structure on an undercategory to
pointed compactly generated weak Hausdorff spaces.  The named model value and
all three morphism classes are inherited from the underlying CGWH category.
Fibrancy is detected on the underlying object, while cofibrancy is exactly
the condition that the basepoint arrow is a cofibration.

The model value is not an instance.  Opening `CGWH.modelCategory` selects the
base model, after which the generic conditional undercategory instance
supplies the pointed model.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH

/-- The model structure on pointed CGWH spaces obtained from the generic
model structure on an undercategory.  This is a named value, not a second
model-category instance. -/
@[instance_reducible]
noncomputable def modelCategory :
    ModelCategory PointedCGWH.{u, v} :=
  HomotopicalAlgebra.ModelCategory.under CGWH.point

/-- A pointed map is a cofibration exactly when its right component is a
cofibration of CGWH spaces. -/
theorem cofibration_iff {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.right :=
  HomotopicalAlgebra.cofibrations_under_iff CGWH.point f

/-- A pointed map is a fibration exactly when its right component is a
fibration of CGWH spaces. -/
theorem fibration_iff {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.right :=
  HomotopicalAlgebra.fibrations_under_iff CGWH.point f

/-- A pointed map is a weak equivalence exactly when its right component is
a weak equivalence of CGWH spaces. -/
theorem weakEquivalence_iff {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.right :=
  HomotopicalAlgebra.weakEquivalences_under_iff CGWH.point f

/-- A pointed CGWH space is fibrant exactly when its underlying CGWH space is
fibrant. -/
theorem isFibrant_iff (X : PointedCGWH.{u, v}) :
    IsFibrant X ↔ IsFibrant X.right := by
  let T : PointedCGWH.{u, v} := Under.mk (𝟙 CGWH.point)
  let hT : IsTerminal T :=
    IsTerminal.ofUniqueHom
      (fun Y => Under.homMk
        (CGWH.point_isTerminal.from Y.right)
        (CGWH.point_isTerminal.hom_ext _ _))
      (fun _ f => Under.UnderMorphism.ext
        (CGWH.point_isTerminal.hom_ext f.right _))
  let p : X ⟶ T := Under.homMk
    (CGWH.point_isTerminal.from X.right)
    (CGWH.point_isTerminal.hom_ext _ _)
  calc
    IsFibrant X ↔ Fibration p :=
      HomotopicalAlgebra.isFibrant_iff_of_isTerminal p hT
    _ ↔ Fibration p.right := fibration_iff p
    _ ↔ Fibration (CGWH.point_isTerminal.from X.right) := by rfl
    _ ↔ IsFibrant X.right :=
      (HomotopicalAlgebra.isFibrant_iff_of_isTerminal
        (CGWH.point_isTerminal.from X.right)
        CGWH.point_isTerminal).symm

/-- A pointed CGWH space is cofibrant exactly when its basepoint arrow is a
cofibration. -/
theorem isCofibrant_iff (X : PointedCGWH.{u, v}) :
    IsCofibrant X ↔ cofibrations CGWH.{u, v} X.hom := by
  calc
    IsCofibrant X ↔ Cofibration (Under.mkIdInitial.to X) :=
      HomotopicalAlgebra.isCofibrant_iff_of_isInitial
        (Under.mkIdInitial.to X) Under.mkIdInitial
    _ ↔ Cofibration (Under.mkIdInitial.to X).right :=
      cofibration_iff (Under.mkIdInitial.to X)
    _ ↔ cofibrations CGWH.{u, v} X.hom := by
      rw [HomotopicalAlgebra.cofibration_iff,
        Under.mkIdInitial_to_right]

namespace modelCategory

/-- Every pointed CGWH space is fibrant in the selected inherited model
structure. -/
theorem allObjectsFibrant (X : PointedCGWH.{u, v}) : IsFibrant X :=
  (PointedCGWH.isFibrant_iff X).mpr
    (CGWH.modelCategory.allObjectsFibrant X.right)

end modelCategory

end PointedCGWH
