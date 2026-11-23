/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.SingleObj

/-!
# Consumers of actual realization CW and vertex data

Exercise the actual disk inclusion, the empty realization, and the selected
vertex pair. The group nerve has repeated vertices in its nondegenerate cells;
the construction requires no nonsingularity or supplied well-pointedness data.
-/

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial

noncomputable section

universe u

example {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    TopCat.RelativeCWComplex (SSet.toTop.map i) :=
  SSet.realizationRelativeCWComplexOfMono i

example (X : SSet.{u}) : TopCat.CWComplex (SSet.toTop.obj X) :=
  SSet.realizationCWComplex X

example (X : SSet.{u}) : Topology.CWComplex (Set.univ : Set (SSet.toTop.obj X)) :=
  inferInstance

example {X : SSet.{u}} (v : X _⦋0⦌) :
    ∃ j : Topology.CWComplex.cell (Set.univ : Set (SSet.toTop.obj X)) 0,
      ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = SSet.realizedVertex v :=
  SSet.realizedVertex_is_classical_zeroCell v

example : TopCat.CWComplex
    (SSet.toTop.obj (⊥ : (Δ[0] : SSet.{u}).Subcomplex).toSSet) :=
  SSet.realizationCWComplex _

example (n : ℕ) :
    (SSet.boundary.toTopDiskBoundaryIso.{u} n).hom ≫ TopCat.diskBoundaryInclusion n =
      SSet.toTop.map (SSet.boundary.{u} n).ι ≫ (SSet.stdSimplex.toTopDiskIso n).hom :=
  SSet.boundary.toTopDiskBoundaryIso_hom_comp_inclusion n

example : Arrow.mk (SSet.toTop.map (SSet.boundary.{u} 0).ι) ≅
    Arrow.mk (TopCat.diskBoundaryInclusion.{u} 0) :=
  SSet.boundary.toTopDiskArrowIso 0

example (X : SSet.{u}) (c : (SSet.realizationCWComplex X).Cells) :
    (SSet.realizationCWComplexCellsEquiv X c).dim = c.j := by simp

example {X : SSet.{u}} (v : X _⦋0⦌) (x : TopCat.disk.{u} 0) :
    (SSet.realizationCWVertexCell v).ι x = SSet.realizedVertex v :=
  SSet.realizationCWVertexCell_ι_apply v x

example {X : SSet.{u}} (v : X _⦋0⦌) :
    (SSet.realizedVertexPair v).map =
      TopCat.const (X := TopCat.of PUnit.{u + 1}) (SSet.realizedVertex v) :=
  SSet.realizedVertexPair_map v

example {X : SSet.{u}} (v : X _⦋0⦌)
    (z : (TopPair.hurewiczCylinderPair (SSet.realizedVertexPair v)).snd) :
    (SSet.realizedVertexHurewiczCofibrationData v).cylinderRetraction
        ((TopPair.hurewiczCylinderPair (SSet.realizedVertexPair v)).map z) = z :=
  TopPair.HurewiczCofibrationData.cylinderRetraction_boundary _ z

example {X : SSet.{u}} (v : X _⦋0⦌) (x : SSet.toTop.obj X) :
    (SSet.realizedVertexStandardNDRData v).control x = 0 ↔ x = SSet.realizedVertex v := by
  refine ((SSet.realizedVertexStandardNDRData v).control_eq_zero_iff x).trans ?_
  change (∃ _ : PUnit.{u + 1}, SSet.realizedVertex v = x) ↔ x = SSet.realizedVertex v
  constructor
  · rintro ⟨_, rfl⟩
    rfl
  · intro hx
    exact ⟨PUnit.unit, hx.symm⟩

example : TopCat.CWComplex
    (SSet.toTop.obj (nerve (SingleObj (Multiplicative ℤ)))) :=
  SSet.realizationCWComplex _

example : TopPair.HurewiczCofibrationData
    (SSet.realizedVertexPair
      (X := nerve (SingleObj (Multiplicative ℤ)))
      (ComposableArrows.mk₀ (SingleObj.star (Multiplicative ℤ)))) :=
  SSet.realizedVertexHurewiczCofibrationData _

#print axioms SSet.boundary.toTopDiskArrowIso
#print axioms SSet.realizationRelativeCWComplexOfMono
#print axioms SSet.realizationCWComplex
#print axioms SSet.instCWComplexToTop
#print axioms SSet.realizedVertex_is_classical_zeroCell
#print axioms SSet.realizationCWComplex_cell_ι
#print axioms SSet.realizationCWVertexCell_ι_apply
#print axioms SSet.toTop_map_isHurewiczCofibration
#print axioms SSet.realizedVertex_isClosedEmbedding
#print axioms SSet.realizedVertex_isHurewiczCofibration
#print axioms SSet.realizedVertexHurewiczCofibrationData
#print axioms SSet.realizedVertexStandardNDRData
#print axioms TopPair.HurewiczCofibrationData.toStandardNDRData
#print axioms TopCat.pathEvalZero_mem_weakHomotopyEquivalences
