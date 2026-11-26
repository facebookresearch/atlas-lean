/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.LogarithmicGeometryFineCharacteristic

/-!
# Sharpness from fine saturated charts

The fine-characteristic theorem implies sharpness for log structures
admitting fine saturated charts, and fineness from fine charts alone.
-/

namespace MathlibExtTest.AlgebraicGeometry.LogarithmicGeometryFineCharacteristic

open CategoryTheory
open MathlibExt.AlgebraicGeometry.LogStructures

universe u v

example {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (O : RingSheaf J) (L : LogStructure J O) (fs : HasFineSaturatedCharts J L)
    (p : J.Point.{max u v}) : IsSharpMonoid (characteristicAt J L p) := by
  have fine : HasFineCharts J L := by
    intro U
    obtain ⟨I, V, f, hcov, hc⟩ := fs U
    refine ⟨I, V, f, hcov, ?_⟩
    intro i
    obtain ⟨P, hP, hchart⟩ := hc i
    exact ⟨P, hP.1, hchart⟩
  exact (WantedExt.AlgebraicGeometry.LogarithmicGeometryWanted.fine_characteristic
    J O L fine p).2

example {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (O : RingSheaf J) (L : LogStructure J O) (fine : HasFineCharts J L)
    (p : J.Point.{max u v}) : IsFineMonoid (characteristicAt J L p) :=
  (WantedExt.AlgebraicGeometry.LogarithmicGeometryWanted.fine_characteristic
    J O L fine p).1

end MathlibExtTest.AlgebraicGeometry.LogarithmicGeometryFineCharacteristic
