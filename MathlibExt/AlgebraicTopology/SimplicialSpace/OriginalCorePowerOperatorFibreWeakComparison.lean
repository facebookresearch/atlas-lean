/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Actual original coefficient operators on complete ordered equivalence fibres.
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCompletionRaw
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkPowerOperatorDK
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalEquivalenceFibreWeakComparison

/-!
# Equivalence fibres of groupoid-simplex power operators

For a Reedy-fibrant Segal space, every groupoid-simplex coefficient operator induces weak
equivalences on its original mapping fibres and ordered equivalence fibres. The comparison
preserves the precise component-selector preimage and retains both pullback projections and the
map to the full mapping-fibre comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCorePowerFibres
open RezkCompletionRaw

/-- Full original mapping-fibre weakness for each coefficient operator follows
from the actual internally constructed categorical inverse homotopies. -/
theorem originalPowerOperator_mappingFibre_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) {m n : SimplexCategoryᵒᵖ} (δ : m ⟶ n)
    (x y : (((powerDiagram W).obj m).diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences
      (mappingFibre.map ((powerDiagram W).map δ) (x := x) (y := y) rfl rfl) := by
  exact RezkPowerOperatorDK.powerMap_mappingFibre_weak δ.unop 0 W hW x y

/-- The actual original equivalence-fibre comparison keeps the complete chosen pair. -/
def originalPowerOperatorEquivalenceFibreMap (W : SimplicialSpace.{u})
    (hW : segalSpaces W) {m n : SimplexCategoryᵒᵖ} (δ : m ⟶ n)
    (x y : (((powerDiagram W).obj m).diagram _⦋0⦌) _⦋0⦌) :
    SegalHomotopy.equivalenceFibre ((powerDiagram W).obj m)
        (RezkPowerOperatorDK.power_segal m.unop W hW) x y ⟶
      SegalHomotopy.equivalenceFibre ((powerDiagram W).obj n)
          (RezkPowerOperatorDK.power_segal n.unop W hW)
        (mappingVertexMap ((powerDiagram W).map δ) x)
        (mappingVertexMap ((powerDiagram W).map δ) y) :=
  SegalHomotopy.equivalenceFibreMap ((powerDiagram W).map δ)
    (RezkPowerOperatorDK.power_segal m.unop W hW) (RezkPowerOperatorDK.power_segal n.unop W hW)
    (x := x) (y := y) rfl rfl

/-- Reflection by the genuine intrinsic full mapping functor identifies the
exact original selector preimage. No core weakness or completeness is supplied. -/
theorem originalPowerOperator_equivalenceSelector_preimage
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {m n : SimplexCategoryᵒᵖ} (δ : m ⟶ n)
    (x y : (((powerDiagram W).obj m).diagram _⦋0⦌) _⦋0⦌) :
    (SSet.mapπ₀ (mappingFibre.map ((powerDiagram W).map δ)
      (x := x) (y := y) rfl rfl)) ⁻¹'
      ((SSet.mapπ₀ (mappingFibre.fst ((powerDiagram W).obj n)
        (mappingVertexMap ((powerDiagram W).map δ) x)
        (mappingVertexMap ((powerDiagram W).map δ) y))) ⁻¹'
        SegalHomotopy.equivalenceComponents ((powerDiagram W).obj n)
          (RezkPowerOperatorDK.power_segal n.unop W hW)) =
      (SSet.mapπ₀ (mappingFibre.fst ((powerDiagram W).obj m) x y)) ⁻¹'
        SegalHomotopy.equivalenceComponents ((powerDiagram W).obj m)
          (RezkPowerOperatorDK.power_segal m.unop W hW) :=
  SegalHomotopy.equivalenceFibreSelector_preimage_of_mappingFibreWeak
    ((powerDiagram W).map δ) (RezkPowerOperatorDK.power_segal m.unop W hW)
        (RezkPowerOperatorDK.power_segal n.unop W hW)
    (originalPowerOperator_mappingFibre_weak W hW δ) x y

/-- The SAME actual equivalence-fibre map is weak by its exact component-preimage
restriction of the internally proved full mapping-fibre weak comparison. -/
theorem originalPowerOperator_equivalenceFibre_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) {m n : SimplexCategoryᵒᵖ} (δ : m ⟶ n)
    (x y : (((powerDiagram W).obj m).diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (originalPowerOperatorEquivalenceFibreMap W hW δ x y) :=
  SegalHomotopy.equivalenceFibreMap_weak_of_mappingFibreWeak
    ((powerDiagram W).map δ) (RezkPowerOperatorDK.power_segal m.unop W hW)
        (RezkPowerOperatorDK.power_segal n.unop W hW)
    (originalPowerOperator_mappingFibre_weak W hW δ) x y

/-- Both original pullback projections and the actual whole mapping-fibre comparison commute. -/
theorem originalPowerOperator_equivalenceFibreMap_legs
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {m n : SimplexCategoryᵒᵖ} (δ : m ⟶ n)
    (x y : (((powerDiagram W).obj m).diagram _⦋0⦌) _⦋0⦌) :
    let P := (powerDiagram W).obj m
    let Q := (powerDiagram W).obj n
    let hP := RezkPowerOperatorDK.power_segal m.unop W hW
    let hQ := RezkPowerOperatorDK.power_segal n.unop W hW
    let f := (powerDiagram W).map δ
    let x' := mappingVertexMap f x
    let y' := mappingVertexMap f y
    let c := originalPowerOperatorEquivalenceFibreMap W hW δ x y
    c ≫ pullback.fst (SegalHomotopy.coreEndpoint Q hQ) (mappingPointPair Q x' y') =
        pullback.fst (SegalHomotopy.coreEndpoint P hP) (mappingPointPair P x y) ≫
          SegalHomotopy.equivalenceMap f hP hQ ∧
      c ≫ pullback.snd (SegalHomotopy.coreEndpoint Q hQ) (mappingPointPair Q x' y') =
        pullback.snd (SegalHomotopy.coreEndpoint P hP) (mappingPointPair P x y) ∧
      c ≫ SegalHomotopy.equivalenceFibreToMappingFibre Q hQ x' y' =
        SegalHomotopy.equivalenceFibreToMappingFibre P hP x y ≫
          mappingFibre.map f (x := x) (y := y) rfl rfl := by
  have h := SegalHomotopy.equivalenceFibreMap_laws ((powerDiagram W).map δ)
    (RezkPowerOperatorDK.power_segal m.unop W hW) (RezkPowerOperatorDK.power_segal n.unop W hW)
        (x := x) (y := y) rfl rfl
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end SimplicialSpace.RezkCorePowerFibres
