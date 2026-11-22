/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure

/-!
# The homotopy category of pointed CGWH spaces

This file specializes the generic model-category homotopy category to the
selected model structure on pointed compactly generated weak Hausdorff spaces.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH

/-- The homotopy category of pointed CGWH spaces. -/
abbrev HomotopyCategory :=
  HomotopicalAlgebra.HomotopyCategory PointedCGWH.{u, v}

/-- The canonical functor from pointed CGWH spaces to their homotopy category. -/
abbrev toHomotopyCategory :
    PointedCGWH.{u, v} ⥤ HomotopyCategory.{u, v} :=
  HomotopicalAlgebra.toHomotopyCategory PointedCGWH.{u, v}

/-- A pointed CGWH map belongs to the weak-equivalence property exactly when
its image in the homotopy category is invertible. -/
theorem weakEquivalences_iff_isIso_toHomotopyCategory_map
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    weakEquivalences PointedCGWH.{u, v} f ↔
      IsIso (toHomotopyCategory.map f) :=
  HomotopicalAlgebra.weakEquivalence_iff_isIso_toHomotopyCategory_map f

/-- A pointed CGWH map carries the `WeakEquivalence` typeclass exactly when
its image in the homotopy category is invertible. -/
theorem weakEquivalence_iff_isIso_toHomotopyCategory_map
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ IsIso (toHomotopyCategory.map f) :=
  (HomotopicalAlgebra.weakEquivalence_iff f).trans
    (weakEquivalences_iff_isIso_toHomotopyCategory_map f)

end PointedCGWH
