/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.CompactFreePoint
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Actual cofibrations under proper compactification

The complete inherited functions and topology are retained.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Filter
open TopologicalSpace Topology
open HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH

/-- Original free basepoint addition preserves the selected actual CGWH cofibrations. -/
theorem costar_preserves_cofibration {X Y : CGWH.{u, v}} (f : X ⟶ Y) [Cofibration f] :
    Cofibration ((Under.costar CGWH.point.{u, v}).map f) := by
  rw [HomotopicalAlgebra.cofibrations_under_iff CGWH.point]
  change Cofibration (coprod.map (𝟙 CGWH.point.{u, v}) f)
  infer_instance

/-- The original proper compactification of a compact CGWH cofibration is a based cofibration. -/
theorem onePointMapOfProper_compact_cofibration {X Y : CGWH.{u, v}}
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    (f : X ⟶ Y) [Cofibration f]
    (hf : Tendsto f (coclosedCompact X) (coclosedCompact Y)) :
    Cofibration (PointedCGWH.onePointMapOfProper.{u, v}
      (ConcreteCategory.hom (C := CGWH.{u, v}) f) hf) := by
  rw [HomotopicalAlgebra.cofibration_iff]
  exact ((cofibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (compactFreePointMapArrowIso f hf)).mp
      ((HomotopicalAlgebra.cofibration_iff _).mp (costar_preserves_cofibration f))

end PointedCGWH
