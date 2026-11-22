/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPointFibreNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationFibration
import MathlibExt.AlgebraicTopology.ModelCategory.Replacement

/-!
# The actual realized point fibres of a sharp simplicial map

At every original simplicial point, sharpness makes the constant-path map
from the strict fibre to the compact-open homotopy fibre weak. The proof
chooses the ordinary scalar fibrant base replacement and the actual
trivial-cofibration/fibration factorization internally, then descends along
the whole original total and base square. No fibrancy of the original
total or base and no fibre-comparison certificate is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen TopCat.modelCategory

namespace SSet.SharpComparisonDraft

/-- Sharpness derives the original constant-path comparison at every realized simplicial point. -/
theorem Sharp.strictFiberToHomotopyFiber_realization_weak {X B : SSet.{u}}
    (p : X ⟶ B) (hp : Sharp p) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    TopCat.weakHomotopyEquivalences
      (TopCat.strictFiberToHomotopyFiber (SSet.toTop.map p) (SSet.realizedPoint b)) := by
  let j := (fibrantReplacementUnit (C := SSet.{u})).app B
  let d := factorizationData (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) (p ≫ j)
  have hdi := (mem_trivialCofibrations_iff d.i).mp d.hi
  let _ : WeakEquivalence d.i := hdi.2
  let _ : Fibration d.p := (fibration_iff d.p).mpr d.hp
  have hj : WeakEquivalence j := by dsimp [j]; infer_instance
  have hsq : p ≫ j = d.i ≫ d.p := d.fac.symm
  have hsTop : TopCat.weakHomotopyEquivalences (SSet.toTop.map d.i) :=
    (weakEquivalence_iff _).mp hdi.2
  have hjTop : TopCat.weakHomotopyEquivalences (SSet.toTop.map j) :=
    (weakEquivalence_iff _).mp hj
  apply TopCat.strictFiberToHomotopyFiber_mem_of_square
    (SSet.toTop.map d.i) (SSet.toTop.map j)
    (SSet.toTop_pointFibre_square p d.p d.i j hsq) (SSet.realizedPoint b) hsTop hjTop
  · exact SSet.strictFiberMap_realization_weak p d.p d.i j hsq b hdi.2 hj hp
      (sharp_of_fibration d.p)
  · exact TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences
      (SSet.toTop.map d.p) (SSet.toTop.map j (SSet.realizedPoint b))

/-- The original whole point fibre maps to the actual compact-open homotopy fibre by constant paths. -/
def pointFibreHomotopyComparison {X B : SSet.{u}}
    (p : X ⟶ B) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    SSet.toTop.obj (pullback p b) ⟶
      TopCat.homotopyFiber (SSet.toTop.map p) (SSet.realizedPoint b) :=
  (SSet.realizationPointFibreIso p b).hom ≫
    TopCat.strictFiberToHomotopyFiber (SSet.toTop.map p) (SSet.realizedPoint b)

/-- The actual comparison retains the full original total-space leg. -/
@[reassoc]
theorem pointFibreHomotopyComparison_toTotal {X B : SSet.{u}}
    (p : X ⟶ B) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    pointFibreHomotopyComparison p b ≫
        TopCat.homotopyFiberToTotal (SSet.toTop.map p) (SSet.realizedPoint b) =
      SSet.toTop.map (pullback.fst p b) := by
  rw [pointFibreHomotopyComparison, Category.assoc,
    TopCat.strictFiberToHomotopyFiber_toTotal, SSet.realizationPointFibreIso_fst]

/-- The actual carried path is the constant path at the same original point. -/
@[reassoc]
theorem pointFibreHomotopyComparison_path {X B : SSet.{u}}
    (p : X ⟶ B) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    pointFibreHomotopyComparison p b ≫
        TopCat.homotopyFiberPath (SSet.toTop.map p) (SSet.realizedPoint b) =
      SSet.toTop.map (pullback.snd p b) ≫ SSet.realizedZeroIso.hom ≫
        TopCat.const (SSet.realizedPoint b) ≫ TopCat.pathConstant (SSet.toTop.obj B) := by
  rw [pointFibreHomotopyComparison, Category.assoc,
    TopCat.strictFiberToHomotopyFiber_path, ← Category.assoc,
    SSet.realizationPointFibreIso_snd]
  simp only [Category.assoc]

/-- Sharpness makes the same whole original point-fibre comparison a weak homotopy equivalence. -/
theorem pointFibreHomotopyComparison_weak {X B : SSet.{u}}
    (p : X ⟶ B) (hp : Sharp p) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    TopCat.weakHomotopyEquivalences (pointFibreHomotopyComparison p b) :=
  TopCat.weakHomotopyEquivalences.comp_mem _ _
    (TopCat.weakHomotopyEquivalences.of_isIso (SSet.realizationPointFibreIso p b).hom)
    (Sharp.strictFiberToHomotopyFiber_realization_weak p hp b)

end SSet.SharpComparisonDraft
