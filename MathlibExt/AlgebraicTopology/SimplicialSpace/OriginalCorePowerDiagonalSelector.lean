/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Original whole-core diagonal and its actual selector.
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCompletionRaw
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHomotopyCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ComponentUnionKanFibration

/-!
# Diagonal equivalence cores of groupoid-simplex powers

For a Reedy-fibrant Segal space, the equivalence cores of its groupoid-simplex powers form a
simplicial diagram whose diagonal maps into the raw completion. A map from that completion to
another Reedy-fibrant Segal space induces a comparison to its equivalence subcomplex, with
vertex and endpoint equations. The target core inclusion and endpoint map are Kan fibrations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open HomotopicalAlgebra
open scoped Simplicial MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal
open RezkCompletionRaw SegalHomotopy

private theorem component_comp_apply {A B C : SimplicialSpace.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k j : SimplexCategoryᵒᵖ) (x : (A.diagram.obj k).obj j) :
    (((f ≫ g).hom.app k).app j) x = ((g.hom.app k).app j) (((f.hom.app k).app j) x) := by
  rfl

private theorem component_id_apply (A : SimplicialSpace.{u})
    (k j : SimplexCategoryᵒᵖ) (x : (A.diagram.obj k).obj j) :
    (((𝟙 A : A ⟶ A).hom.app k).app j) x = x := by
  rfl

private theorem component_iso_hom_inv_apply {A B : SimplicialSpace.{u}}
    (e : A ≅ B) (k j : SimplexCategoryᵒᵖ) (x : (A.diagram.obj k).obj j) :
    ((e.inv.hom.app k).app j) (((e.hom.hom.app k).app j) x) = x := by
  have h := congrArg (fun f : A ⟶ A => ((f.hom.app k).app j) x) e.hom_inv_id
  simpa only [component_comp_apply, component_id_apply] using h

/-- Every original full-J power is Segal by the actual Cartesian power theorem. -/
theorem powerDiagram_segal (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (n : SimplexCategoryᵒᵖ) : segalSpaces ((powerDiagram W).obj n) := by
  change segalSpaces ((ihom (discreteInnerFunctor.obj
    (SSet.FreeGroupoidSimplex.J.{u}.obj n.unop))).obj W)
  exact SegalExponentRawAssembly.outerPower_segal
    (SSet.FreeGroupoidSimplex.J.{u}.obj n.unop) W hW

/-- The cores of the same powers, with every original coefficient operator. -/
def corePowerDiagram (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SimplicialObject SSet.{u} where
  obj n := (equivalenceSubcomplex ((powerDiagram W).obj n)
    (powerDiagram_segal W hW n) : SSet.{u})
  map δ := equivalenceMap ((powerDiagram W).map δ)
    (powerDiagram_segal W hW _) (powerDiagram_segal W hW _)
  map_id n := by
    rw [(powerDiagram W).map_id]
    exact equivalenceMap_id _ _
  map_comp δ ε := by
    rw [(powerDiagram W).map_comp]
    exact equivalenceMap_comp _ _ _ _ _

set_option linter.unusedVariables false in
/-- The core inclusions are natural for the complete original power diagram. -/
def corePowerInclusion (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    corePowerDiagram W hW ⟶ rowPowerDiagram W (op ⦋1⦌) where
  app n := (equivalenceSubcomplex ((powerDiagram W).obj n)
    (powerDiagram_segal W hW n)).ι
  naturality n m δ := equivalenceMap_ι _ _ _

/-- The actual diagonal of equivalence arrows in every original power. -/
def coreDiagonal (W : SimplicialSpace.{u}) (hW : segalSpaces W) : SSet.{u} :=
  SSet.simplicialDiagonalFunctor.obj (corePowerDiagram W hW)

/-- Its whole diagonal inclusion has codomain the original raw-completion row one. -/
def coreDiagonalInclusion (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    coreDiagonal W hW ⟶ (rawCompletion W).diagram _⦋1⦌ :=
  SSet.simplicialDiagonalFunctor.map (corePowerInclusion W hW)

/-- Evaluation at an original coefficient vertex uses the coefficient operator
to zero followed by Raw20's actual zero-power Iso, including its J[0] leg. -/
def coefficientVertexEvaluation (W : SimplicialSpace.{u})
    {n : SimplexCategoryᵒᵖ} (α : ⦋0⦌ ⟶ n.unop) :
    (powerDiagram W).obj n ⟶ W :=
  (powerDiagram W).map α.op ≫ (powerZeroUnitIso W).hom

/-- The selected original W edge retains both the coefficient-to-zero operator
and the actual inner vertex; no simplicial global vertex choice is made. -/
def originalCoreVertex (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {n : SimplexCategoryᵒᵖ} (α : ⦋0⦌ ⟶ n.unop)
    (q : (coreDiagonal W hW).obj n) : (W.diagram _⦋1⦌) _⦋0⦌ :=
  ((coefficientVertexEvaluation W α).hom.app (op ⦋1⦌)).app (op ⦋0⦌)
    ((((powerDiagram W).obj n).diagram _⦋1⦌).map α.op q.val)

/-- Intrinsic equivalence is preserved by that actual simplicial-space functor.
This uses only the original source Segalness, with no DK or core-WE input. -/
theorem originalCoreVertex_isEquivalence (W : SimplicialSpace.{u})
    (hW : segalSpaces W) {n : SimplexCategoryᵒᵖ} (α : ⦋0⦌ ⟶ n.unop)
    (q : (coreDiagonal W hW).obj n) :
    IsEquivalenceEdge W hW (originalCoreVertex W hW α q) :=
  isEquivalenceEdge_map (coefficientVertexEvaluation W α)
    (powerDiagram_segal W hW n) hW _
    ((mem_equivalenceSubcomplex_iff_vertex ((powerDiagram W).obj n)
      (powerDiagram_segal W hW n) n q.val α).mp q.property)

/-- Every original diagonal vertex is literally the raw unit applied to its
coefficient-zero selector. The equation uses the inverse of the actual Iso. -/
theorem coreDiagonalInclusion_vertex (W : SimplicialSpace.{u})
    (hW : segalSpaces W) {n : SimplexCategoryᵒᵖ} (α : ⦋0⦌ ⟶ n.unop)
    (q : (coreDiagonal W hW).obj n) :
    ((rawCompletion W).diagram _⦋1⦌).map α.op
        ((coreDiagonalInclusion W hW).app n q) =
      ((rawCompletionUnit W).hom.app (op ⦋1⦌)).app (op ⦋0⦌)
        (originalCoreVertex W hW α q) := by
  rw [rawCompletionUnit_innerZero, constantPowerSection_zero_eq_inverse]
  let a : (((powerDiagram W).obj (op ⦋0⦌)).diagram _⦋1⦌) _⦋0⦌ :=
    (((powerDiagram W).map α.op).hom.app (op ⦋1⦌)).app (op ⦋0⦌)
      ((((powerDiagram W).obj n).diagram _⦋1⦌).map α.op q.val)
  have inverse_apply := component_iso_hom_inv_apply (powerZeroUnitIso W)
    (op ⦋1⦌) (op ⦋0⦌) a
  have hleft : ((rawCompletion W).diagram _⦋1⦌).map α.op
      ((coreDiagonalInclusion W hW).app n q) = a := by
    change (SSet.simplicialDiagonalFunctor.obj (rowPowerDiagram W (op ⦋1⦌))).map α.op q.val = a
    rw [SSet.simplicialDiagonalFunctor_obj_map]
    rfl
  have hright : originalCoreVertex W hW α q =
      ((((powerZeroUnitIso W).hom.hom.app (op ⦋1⦌)).app (op ⦋0⦌)) a) := by
    dsimp only [originalCoreVertex, coefficientVertexEvaluation]
    rw [component_comp_apply]
  rw [hleft, hright]
  exact inverse_apply.symm

/-- The actual whole diagonal composite lands in the target equivalence core.
Target Segalness is an independently derived input; completeness is absent. -/
theorem coreDiagonalComposite_mem {W V : SimplicialSpace.{u}}
    (β : rawCompletion W ⟶ V) (hW : segalSpaces W) (hV : segalSpaces V)
    (n : SimplexCategoryᵒᵖ) (q : (coreDiagonal W hW).obj n) :
    (β.hom.app (op ⦋1⦌)).app n ((coreDiagonalInclusion W hW).app n q) ∈
      (equivalenceSubcomplex V hV).obj n := by
  rw [mem_equivalenceSubcomplex]
  let α : ⦋0⦌ ⟶ n.unop := SimplexCategory.const ⦋0⦌ n.unop 0
  rw [← (β.hom.app (op ⦋1⦌)).naturality_apply,
    coreDiagonalInclusion_vertex W hW α q]
  exact isEquivalenceEdge_map (rawCompletionUnit W ≫ β) hW hV _
    (originalCoreVertex_isEquivalence W hW α q)

/-- The SAME whole core comparison is the lift of the actual diagonal composite. -/
def coreDiagonalComparison {W V : SimplicialSpace.{u}}
    (β : rawCompletion W ⟶ V) (hW : segalSpaces W) (hV : segalSpaces V) :
    coreDiagonal W hW ⟶ (equivalenceSubcomplex V hV : SSet.{u}) :=
  SSet.Subcomplex.lift (coreDiagonalInclusion W hW ≫ β.hom.app (op ⦋1⦌)) (by
    intro n q hq
    rcases hq with ⟨a, rfl⟩
    exact coreDiagonalComposite_mem β hW hV n a)

/-- The lift retains the entire original row-one map. -/
@[reassoc]
theorem coreDiagonalComparison_ι {W V : SimplicialSpace.{u}}
    (β : rawCompletion W ⟶ V) (hW : segalSpaces W) (hV : segalSpaces V) :
    coreDiagonalComparison β hW hV ≫ (equivalenceSubcomplex V hV).ι =
      coreDiagonalInclusion W hW ≫ β.hom.app (op ⦋1⦌) :=
  SSet.Subcomplex.lift_ι _ _

/-- The target core uses source d₁ first and target d₀ second. -/
def coreEndpoint (V : SimplicialSpace.{u}) (hV : segalSpaces V) :
    (equivalenceSubcomplex V hV : SSet.{u}) ⟶
      (V.diagram _⦋0⦌) ⨯ (V.diagram _⦋0⦌) :=
  (equivalenceSubcomplex V hV).ι ≫ mappingEndpoint V

/-- The base map is the original raw endpoint followed by β₀ on both factors. -/
def coreDiagonalBase {W V : SimplicialSpace.{u}}
    (β : rawCompletion W ⟶ V) (hW : segalSpaces W) :
    coreDiagonal W hW ⟶ (V.diagram _⦋0⦌) ⨯ (V.diagram _⦋0⦌) :=
  coreDiagonalInclusion W hW ≫ mappingEndpoint (rawCompletion W) ≫
    prod.map (β.hom.app (op ⦋0⦌)) (β.hom.app (op ⦋0⦌))

/-- The actual core comparison is over that SAME ordered target object pair. -/
theorem coreDiagonalComparison_over_base {W V : SimplicialSpace.{u}}
    (β : rawCompletion W ⟶ V) (hW : segalSpaces W) (hV : segalSpaces V) :
    coreDiagonalComparison β hW hV ≫ coreEndpoint V hV = coreDiagonalBase β hW := by
  rw [coreEndpoint, ← Category.assoc, coreDiagonalComparison_ι, Category.assoc]
  exact congrArg (fun f => coreDiagonalInclusion W hW ≫ f)
    (mappingEndpoint_naturality β).symm

/-- The base's first projection is the original raw d₁ followed by β₀. -/
theorem coreDiagonalBase_fst {W V : SimplicialSpace.{u}}
    (β : rawCompletion W ⟶ V) (hW : segalSpaces W) :
    coreDiagonalBase β hW ≫ prod.fst = coreDiagonalInclusion W hW ≫
      (rawCompletion W).diagram.δ (1 : Fin 2) ≫ β.hom.app (op ⦋0⦌) := by
  simp only [coreDiagonalBase, Category.assoc, prod.map_fst, mappingEndpoint_fst_assoc]

/-- The base's second projection is the original raw d₀ followed by β₀. -/
theorem coreDiagonalBase_snd {W V : SimplicialSpace.{u}}
    (β : rawCompletion W ⟶ V) (hW : segalSpaces W) :
    coreDiagonalBase β hW ≫ prod.snd = coreDiagonalInclusion W hW ≫
      (rawCompletion W).diagram.δ (0 : Fin 2) ≫ β.hom.app (op ⦋0⦌) := by
  simp only [coreDiagonalBase, Category.assoc, prod.map_snd, mappingEndpoint_snd_assoc]

/-- The target equivalence-core inclusion is the actual native component-union
inclusion. Its fibration proof needs no ambient Kan assumption or weakness input. -/
theorem coreInclusion_fibration (V : SimplicialSpace.{u}) (hV : segalSpaces V) :
    Fibration (equivalenceSubcomplex V hV).ι := by
  change Fibration (SSet.componentUnion (V.diagram _⦋1⦌)
    (equivalenceComponents V hV)).ι
  exact SSet.componentUnionInclusionKanFibration _ _

/-- The actual ordered target core endpoint is a fibration, derived from
its native component-union inclusion and the original Reedy mapping endpoint. -/
theorem coreEndpoint_fibration (V : SimplicialSpace.{u}) (hV : segalSpaces V) :
    Fibration (coreEndpoint V hV) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let : Fibration (equivalenceSubcomplex V hV).ι := coreInclusion_fibration V hV
  let : Fibration (mappingEndpoint V) := ReedyModel.mappingEndpoint_fibration V hV.1
  change Fibration ((equivalenceSubcomplex V hV).ι ≫ mappingEndpoint V)
  infer_instance

end SimplicialSpace.RezkCompletionCoreDiagonal
