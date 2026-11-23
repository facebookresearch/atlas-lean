/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ClosedBall.NDR
public import MathlibExt.Topology.Category.TopPair.NDREndpointCylinder

/-!
# Interval–disk boundary pairs

The boundary of `I × Dⁿ` is represented literally as
`(∂I × Dⁿ) ∪ (I × Sⁿ⁻¹)`.  This file gives that existing endpoint-cylinder
construction a model-specific name and supplies its controlled NDR data.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory MonoidalCategory Topology

universe u

namespace Topology.CWComplex

/-- The literal boundary pair of the interval product with the classical `n`-disk. -/
abbrev intervalDiskPair (n : ℕ) : TopPair.{u} :=
  TopPair.endpointCylinderBoundaryPair (classicalCellDiskPair.{u} n)

theorem intervalDiskPair_fst (n : ℕ) :
    (intervalDiskPair.{u} n).fst =
      TopCat.I.{u} ⊗ (classicalCellDiskPair.{u} n).fst :=
  rfl

/-- The interval–disk boundary is the union of the two endpoint faces and the cylindrical rim. -/
theorem range_intervalDiskPair_map (n : ℕ) :
    Set.range (intervalDiskPair.{u} n).map =
      (Set.range (TopPair.intervalBoundaryPair.{u}).map).unionProd
        (Set.range (classicalCellDiskPair.{u} n).map) :=
  TopPair.range_endpointCylinderBoundaryPair_map (classicalCellDiskPair.{u} n)

/-- Pointwise membership in the interval–disk boundary. -/
theorem mem_range_intervalDiskPair_map_iff
    (n : ℕ) (z : (intervalDiskPair.{u} n).fst) :
    z ∈ Set.range (intervalDiskPair.{u} n).map ↔
      ((z.1 : TopCat.I.{u}) = (0 : TopCat.I.{u}) ∨
        (z.1 : TopCat.I.{u}) = (1 : TopCat.I.{u})) ∨
        (z.2 : (classicalCellDiskPair.{u} n).fst) ∈
          Set.range (classicalCellDiskPair.{u} n).map :=
  TopPair.mem_range_endpointCylinderBoundaryPair_map_iff
    (classicalCellDiskPair.{u} n) z

/-- The literal interval–disk boundary is nonempty in every dimension. -/
noncomputable instance intervalDiskPair_nonempty_snd (n : ℕ) :
    Nonempty (intervalDiskPair.{u} n).snd := by
  let x : (classicalCellDiskPair.{u} n).fst :=
    ULift.up ⟨(0 : Fin n → ℝ), by simp [Metric.mem_closedBall]⟩
  refine ⟨⟨((0 : TopCat.I.{u}), x), ?_⟩⟩
  exact Set.mem_unionProd.mpr <| Or.inl <|
    (TopPair.mem_range_intervalBoundaryPair_map_iff
      (0 : TopCat.I.{u})).2 (Or.inl rfl)

/-- Controlled NDR data for the literal boundary of `I × Dⁿ`. -/
noncomputable def intervalDiskPairNDRData (n : ℕ) :
    TopPair.NDRData (intervalDiskPair.{u} n) :=
  (classicalCellDiskPairNDRData.{u} n).endpointCylinderBoundaryData

/-- Chosen good-pair data for the literal boundary of `I × Dⁿ`. -/
noncomputable def intervalDiskPairGoodPairData (n : ℕ) :
    TopPair.GoodPairData (intervalDiskPair.{u} n) :=
  (intervalDiskPairNDRData.{u} n).toGoodPairData

/-- The boundary inclusion of `I × Dⁿ` is a Hurewicz cofibration. -/
theorem intervalDiskPair_isHurewiczCofibration (n : ℕ) :
    TopCat.IsHurewiczCofibration (intervalDiskPair.{u} n).map :=
  (classicalCellDiskPairNDRData.{u} n).endpointRelativeHurewicz

end Topology.CWComplex

end
