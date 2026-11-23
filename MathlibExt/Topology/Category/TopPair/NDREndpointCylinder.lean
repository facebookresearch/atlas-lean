/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.IntervalBoundaryNDR
public import MathlibExt.Topology.Category.TopPair.NDRProduct

/-!
# Endpoint-relative cylinder boundary data

For an embedded pair `A → X`, this file packages controlled NDR data on
`(∂I × X) ∪ (I × A) ⊆ I × X`. It is the endpoint-relative
homotopy-extension boundary used to correct a homotopy while fixing both time
endpoints.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology

universe u

namespace TopPair

/-- The endpoint-cylinder boundary of an embedded pair. The interval is the
left factor, so the ambient object is literally `I × X`. -/
abbrev endpointCylinderBoundaryPair (P : TopPair.{u}) : TopPair.{u} :=
  prodObj intervalBoundaryPair P

@[simp]
theorem range_endpointCylinderBoundaryPair_map (P : TopPair.{u}) :
    Set.range (endpointCylinderBoundaryPair P).map =
      (Set.range (intervalBoundaryPair.{u}).map).unionProd
        (Set.range P.map) :=
  range_prodObj_map intervalBoundaryPair P

theorem mem_range_endpointCylinderBoundaryPair_map_iff
    (P : TopPair.{u}) (z : (endpointCylinderBoundaryPair P).fst) :
    z ∈ Set.range (endpointCylinderBoundaryPair P).map ↔
      ((z.1 : TopCat.I.{u}) = (0 : TopCat.I.{u}) ∨
        (z.1 : TopCat.I.{u}) = (1 : TopCat.I.{u})) ∨
        (z.2 : P.fst) ∈ Set.range P.map := by
  rw [range_endpointCylinderBoundaryPair_map]
  constructor
  · intro hz
    have hz' :
        (z.1 : TopCat.I.{u}) ∈
            Set.range (intervalBoundaryPair.{u}).map ∨
          (z.2 : P.fst) ∈ Set.range P.map :=
      Set.mem_unionProd.mp hz
    rcases hz' with hzI | hzP
    · left
      exact (mem_range_intervalBoundaryPair_map_iff
        (z.1 : TopCat.I.{u})).1 hzI
    · exact Or.inr hzP
  · intro hz
    apply Set.mem_unionProd.mpr
    rcases hz with hzI | hzP
    · left
      exact (mem_range_intervalBoundaryPair_map_iff
        (z.1 : TopCat.I.{u})).2 hzI
    · exact Or.inr hzP

namespace NDRData

variable {P : TopPair.{u}} (d : NDRData P)

/-- Product NDR data on the endpoint-cylinder boundary. -/
noncomputable def endpointCylinderBoundaryData :
    NDRData (endpointCylinderBoundaryPair P) :=
  (intervalBoundaryNDRData.{u}).prod d

@[simp]
theorem endpointCylinderBoundaryData_control_apply
    (z : (endpointCylinderBoundaryPair P).fst) :
    d.endpointCylinderBoundaryData.control z =
      (intervalBoundaryNDRData.{u}).control z.1 * d.control z.2 :=
  prod_control_apply _ _ _

/-- NDR data on `A → X` supplies endpoint-relative homotopy extension on
`(∂I × X) ∪ (I × A) → I × X`. -/
theorem endpointRelativeHurewicz (d : NDRData P) :
    TopCat.IsHurewiczCofibration (endpointCylinderBoundaryPair P).map :=
  TopPair.StandardNDRData.isHurewiczCofibration
    (endpointCylinderBoundaryData d).toStandard

end NDRData

end TopPair

end
