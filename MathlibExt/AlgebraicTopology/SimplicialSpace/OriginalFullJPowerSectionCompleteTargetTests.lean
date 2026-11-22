/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalWalkingECompleteTargetTests
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalSplitCompositeWeakRetracts
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCoefficientContractions
import MathlibExt.AlgebraicTopology.SimplicialSpace.CategoricalPowerHomotopy
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCompletionRaw

/-!
# Every complete target tests the original full-J constant section as weak

The original zero-simplex inclusion and collapse supply the actual power
evaluation and constant map. One composite is strictly identity at the
original zero power; the other is the full constant-J coefficient map.
The native E contraction transposes to a literal categorical homotopy of
that second composite to identity. The complete-target inner tests and
strict Arrow retract then give the original section's Rezk membership.

All original coefficient operators, the original power-zero unit Iso, and
the actual constantPowerSection are retained. No Segalness, fibrancy,
Dwyer--Kan equivalence or weak-unit outcome is a caller input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open scoped Simplicial MonoidalCategory SimplicialSpace.Inner SimplicialSpace.Cartesian

namespace SimplicialSpace.OriginalFullJSectionTests
open OriginalWalkingETests

/-- The original collapse uses the unique scalar ordinal map to the actual zero ordinal. -/
def originalSimplexCollapse (n : SimplexCategory) : n ⟶ ⦋0⦌ :=
  SimplexCategory.const n ⦋0⦌ 0

/-- The evaluation vertex is the actual scalar zero-ordinal map at v. -/
def originalSimplexVertex (n : SimplexCategory) (v : Fin (n.len + 1)) : ⦋0⦌ ⟶ n :=
  SimplexCategory.const ⦋0⦌ n v

/-- The original vertex followed by the original collapse is strictly the zero-ordinal identity. -/
theorem originalSimplexVertex_collapse (n : SimplexCategory) (v : Fin (n.len + 1)) :
    originalSimplexVertex n v ≫ originalSimplexCollapse n = 𝟙 ⦋0⦌ := by
  apply SimplexCategory.Hom.ext
  exact DFunLike.ext _ _ (fun _ => (Subsingleton.elim _ _ : (_ : Fin 1) = _))

/-- The other original ordinal composite is the actual constant ordinal operator. -/
theorem originalSimplexCollapse_vertex (n : SimplexCategory) (v : Fin (n.len + 1)) :
    originalSimplexCollapse n ≫ originalSimplexVertex n v = SimplexCategory.const n n v := by
  ext i
  rfl

/-- The full original free-groupoid coefficient functor sends that operator to its literal constant
map. -/
theorem originalCoefficient_constant (n : SimplexCategory) (v : Fin (n.len + 1)) :
    RezkCompletionRaw.coefficient.{u}.map (SimplexCategory.const n n v) =
      discreteInnerFunctor.map (SSet.FreeGroupoidSimplex.constantMap.{u} n n v) := by
  change discreteInnerFunctor.map
      (SSet.FreeGroupoidSimplex.J.{u}.map (SimplexCategory.const n n v)) = _
  congr 1
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro x
  apply (SSet.FreeGroupoidSimplex.simplexVertexEquiv n a.unop.len).injective
  funext i
  rw [SSet.FreeGroupoidSimplex.simplexVertexEquiv_site,
    SSet.FreeGroupoidSimplex.constantMap_coordinates]
  rfl

/-- The actual contravariant whole power of the original collapse inserts the zero power into degree
n. -/
def originalPowerCollapse (W : SimplicialSpace.{u}) (n : SimplexCategory) :
    (RezkCompletionRaw.powerDiagram W).obj (op ⦋0⦌) ⟶
      (RezkCompletionRaw.powerDiagram W).obj (op n) :=
  (RezkCompletionRaw.powerDiagram W).map (originalSimplexCollapse n).op

/-- The same actual coefficient vertex gives the entire original zero-power evaluation. -/
def originalPowerEvaluation (W : SimplicialSpace.{u}) (n : SimplexCategory)
    (v : Fin (n.len + 1)) :
    (RezkCompletionRaw.powerDiagram W).obj (op n) ⟶
      (RezkCompletionRaw.powerDiagram W).obj (op ⦋0⦌) :=
  (RezkCompletionRaw.powerDiagram W).map (originalSimplexVertex n v).op

/-- The strict original power section-evaluation composite is the zero-power identity. -/
theorem originalPowerCollapse_evaluation (W : SimplicialSpace.{u}) (n : SimplexCategory)
    (v : Fin (n.len + 1)) :
    originalPowerCollapse W n ≫ originalPowerEvaluation W n v =
      𝟙 ((RezkCompletionRaw.powerDiagram W).obj (op ⦋0⦌)) := by
  dsimp only [originalPowerCollapse, originalPowerEvaluation]
  rw [← CategoryTheory.Functor.map_comp, ← op_comp, originalSimplexVertex_collapse,
    op_id, CategoryTheory.Functor.map_id]

/-- The other power composite is exactly precomposition by the original full-J constant map. -/
theorem originalPowerEvaluation_collapse (W : SimplicialSpace.{u}) (n : SimplexCategory)
    (v : Fin (n.len + 1)) :
    originalPowerEvaluation W n v ≫ originalPowerCollapse W n =
      (MonoidalClosed.pre
        (discreteInnerFunctor.map (SSet.FreeGroupoidSimplex.constantMap.{u} n n v))).app W := by
  have hcomp : originalPowerEvaluation W n v ≫ originalPowerCollapse W n =
      (RezkCompletionRaw.powerDiagram W).map (SimplexCategory.const n n v).op := by
    dsimp only [originalPowerCollapse, originalPowerEvaluation]
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, originalSimplexCollapse_vertex]
  have hmap : (RezkCompletionRaw.powerDiagram W).map (SimplexCategory.const n n v).op =
      (MonoidalClosed.pre (RezkCompletionRaw.coefficient.map
          (SimplexCategory.const n n v))).app W :=
    RezkCompletionRaw.powerDiagram_map W (SimplexCategory.const n n v).op
  have hcoef := congrArg
    (fun j : RezkCompletionRaw.coefficient.{u}.obj n ⟶ RezkCompletionRaw.coefficient.{u}.obj n =>
      (MonoidalClosed.pre j).app W) (originalCoefficient_constant n v)
  exact hcomp.trans (hmap.trans hcoef)

/-- The original coefficient contraction is transposed by the actual full Cartesian power. -/
def originalPowerContraction (W : SimplicialSpace.{u}) (n : SimplexCategory)
    (v : Fin (n.len + 1)) :
    WalkingEUnit.coherentSpace ⊗ (RezkCompletionRaw.powerDiagram W).obj (op n) ⟶
      (RezkCompletionRaw.powerDiagram W).obj (op n) :=
  CategoricalPowerHomotopy.homotopyPrecomp
    (RezkCoefficientContractions.coefficientContraction n v) W

/-- Both original E endpoints are the complete evaluation-section composite and identity. -/
theorem originalPowerContraction_endpoints (W : SimplicialSpace.{u}) (n : SimplexCategory)
    (v : Fin (n.len + 1)) :
    WalkingEUnit.spaceEndpoint ((RezkCompletionRaw.powerDiagram W).obj (op n))
        SSet.coherentIso.x₀ ≫ originalPowerContraction W n v =
      originalPowerEvaluation W n v ≫ originalPowerCollapse W n ∧
    WalkingEUnit.spaceEndpoint ((RezkCompletionRaw.powerDiagram W).obj (op n))
        SSet.coherentIso.x₁ ≫ originalPowerContraction W n v =
      𝟙 ((RezkCompletionRaw.powerDiagram W).obj (op n)) := by
  have he := RezkCoefficientContractions.coefficientContraction_endpoints n v
  have h := CategoricalPowerHomotopy.homotopyPrecomp_endpoints
    (discreteInnerFunctor.map (SSet.FreeGroupoidSimplex.constantMap.{u} n n v))
    (𝟙 (RezkCoefficientContractions.coefficient.{u} n))
    (RezkCoefficientContractions.coefficientContraction n v) he.1 he.2 W
  constructor
  · exact h.1.trans (originalPowerEvaluation_collapse W n v).symm
  · have hid : (MonoidalClosed.pre (𝟙 (RezkCoefficientContractions.coefficient.{u} n))).app W =
        𝟙 ((ihom (RezkCoefficientContractions.coefficient.{u} n)).obj W) := by
      rw [MonoidalClosed.pre_id, NatTrans.id_app]
    exact h.2.trans hid

/-- Every complete target tests the literal power-collapse map weak by the strict split Arrow
retract. -/
theorem originalPowerCollapse_test_weak (W : SimplicialSpace.{u}) (n : SimplexCategory)
    (v : Fin (n.len + 1)) (Z : SimplicialSpace.{u}) (hZ : completeSegalSpaces Z) :
    SSet.realizationWeakEquivalences (innerTestMap (originalPowerCollapse W n) Z) := by
  have he := originalPowerContraction_endpoints W n v
  have hw := categoricalSelfHomotopy_test_weak
    (originalPowerEvaluation W n v ≫ originalPowerCollapse W n)
    (originalPowerContraction W n v) he.1 he.2 Z hZ
  have hs : innerTestMap (originalPowerEvaluation W n v) Z ≫
      innerTestMap (originalPowerCollapse W n) Z =
      𝟙 ((innerHomFunctor.obj (op ((RezkCompletionRaw.powerDiagram W).obj (op ⦋0⦌)))).obj Z) := by
    rw [innerTestMap_comp, originalPowerCollapse_evaluation, innerTestMap_id]
  apply SSet.realizationWeak_of_splitComposite_left
    (innerTestMap (originalPowerCollapse W n) Z)
    (innerTestMap (originalPowerEvaluation W n v) Z) hs
  rw [innerTestMap_comp]
  exact hw

/-- The original power-collapse map belongs to the genuine all-complete-target Rezk weak class. -/
theorem originalPowerCollapse_rezkWeak (W : SimplicialSpace.{u}) (n : SimplexCategory) :
    rezkWeakEquivalences (originalPowerCollapse W n) :=
  fun Z hZ => originalPowerCollapse_test_weak W n 0 Z hZ

/-- Original whole section naturality factors the actual constant section through the same zero
power. -/
theorem constantPowerSection_collapse (W : SimplicialSpace.{u}) (n : SimplexCategory) :
    (RezkCompletionRaw.constantPowerSection W).app (op n) =
      (RezkCompletionRaw.constantPowerSection W).app (op ⦋0⦌) ≫ originalPowerCollapse W n := by
  have h := (RezkCompletionRaw.constantPowerSection W).naturality (originalSimplexCollapse n).op
  change (𝟙 W) ≫ (RezkCompletionRaw.constantPowerSection W).app (op n) =
    (RezkCompletionRaw.constantPowerSection W).app (op ⦋0⦌) ≫ originalPowerCollapse W n at h
  simpa only [Category.id_comp] using h

/-- Every original constant section is weak for every W, using its actual zero-power Iso and
tests. -/
theorem constantPowerSection_rezkWeak (W : SimplicialSpace.{u}) (m : SimplexCategoryᵒᵖ) :
    rezkWeakEquivalences ((RezkCompletionRaw.constantPowerSection W).app m) := by
  change rezkWeakEquivalences ((RezkCompletionRaw.constantPowerSection W).app (op m.unop))
  rw [constantPowerSection_collapse]
  apply rezkWeakEquivalences.comp_mem _ _ _ (originalPowerCollapse_rezkWeak W m.unop)
  rw [RezkCompletionRaw.constantPowerSection_zero_eq_inverse]
  exact rezkWeakEquivalences.of_isIso _

/-- Evaluation at the original vertex is transported by the genuine original zero-power unit Iso. -/
def originalSectionEvaluation (W : SimplicialSpace.{u}) (n : SimplexCategory)
    (v : Fin (n.len + 1)) : (RezkCompletionRaw.powerDiagram W).obj (op n) ⟶ W :=
  originalPowerEvaluation W n v ≫ (RezkCompletionRaw.powerZeroUnitIso W).hom

/-- The unchanged actual constantPowerSection followed by that evaluation is strictly identity. -/
theorem constantPowerSection_evaluation (W : SimplicialSpace.{u}) (n : SimplexCategory)
    (v : Fin (n.len + 1)) :
    (RezkCompletionRaw.constantPowerSection W).app (op n) ≫ originalSectionEvaluation W n v =
      𝟙 W := by
  rw [constantPowerSection_collapse]
  dsimp only [originalSectionEvaluation]
  calc
    ((RezkCompletionRaw.constantPowerSection W).app (op ⦋0⦌) ≫ originalPowerCollapse W n) ≫
        (originalPowerEvaluation W n v ≫ (RezkCompletionRaw.powerZeroUnitIso W).hom) =
      (RezkCompletionRaw.constantPowerSection W).app (op ⦋0⦌) ≫
        ((originalPowerCollapse W n ≫ originalPowerEvaluation W n v) ≫
          (RezkCompletionRaw.powerZeroUnitIso W).hom) := by simp only [Category.assoc]
    _ = (RezkCompletionRaw.constantPowerSection W).app (op ⦋0⦌) ≫
        (RezkCompletionRaw.powerZeroUnitIso W).hom := by
      rw [originalPowerCollapse_evaluation, Category.id_comp]
    _ = 𝟙 W := RezkCompletionRaw.constantPowerSection_zero_comparison W

/-- Both original section-evaluation orders retain the literal constant-power composite. -/
theorem originalSectionEvaluation_section (W : SimplicialSpace.{u}) (n : SimplexCategory)
    (v : Fin (n.len + 1)) :
    originalSectionEvaluation W n v ≫ (RezkCompletionRaw.constantPowerSection W).app (op n) =
      originalPowerEvaluation W n v ≫ originalPowerCollapse W n := by
  rw [constantPowerSection_collapse, RezkCompletionRaw.constantPowerSection_zero_eq_inverse]
  dsimp only [originalSectionEvaluation]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Every original coefficient power operator is derived Rezk weak from the original whole section
square. -/
theorem powerDiagram_map_rezkWeak (W : SimplicialSpace.{u})
    {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    rezkWeakEquivalences ((RezkCompletionRaw.powerDiagram W).map f) := by
  apply (rezkWeakEquivalences.precomp_iff _ _ (constantPowerSection_rezkWeak W m)).mp
  have h := (RezkCompletionRaw.constantPowerSection W).naturality f
  change (𝟙 W) ≫ (RezkCompletionRaw.constantPowerSection W).app n =
    (RezkCompletionRaw.constantPowerSection W).app m ≫ (RezkCompletionRaw.powerDiagram W).map f at h
  rw [← h, Category.id_comp]
  exact constantPowerSection_rezkWeak W n

end SimplicialSpace.OriginalFullJSectionTests
