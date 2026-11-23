/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.ClassicalExistence
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ClassifyingSpacePlusSubgroup
import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroConnectedRealization

/-!
# Independent plus constructions on ordinary algebraic BGL

The source is the actual classifying-nerve realization, its canonical
vertex and the existing stable-elementary perfect normal subgroup. Its
connectedness and classical CW structure are derived. The construction
uses the generic classical cell proof, with no Quillen comparison input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomotopicalAlgebra
open scoped ContinuousMap Simplicial TopCat.modelCategory

universe u

namespace AlgebraicKTheory.StableGL

/-- The actual stable-GL classifying nerve is connected because its vertex
is the unique object; no connectedness/model hypothesis is supplied. -/
private theorem classifyingNerve_connected (R : Type u) [Ring R] :
    (classifyingNerve R).IsConnected := by
  let K : SSet.{u} := classifyingNerve R
  let e : K _⦋0⦌ ≃ ClassifyingCategory R := CategoryTheory.nerveEquiv
  let : Subsingleton (K _⦋0⦌) := e.injective.subsingleton
  have hπ : Subsingleton (SSet.π₀ K) :=
    Function.Surjective.subsingleton (SSet.π₀.mk_surjective (X := K))
  have hne : K.Nonempty := ⟨classifyingVertex R⟩
  exact (SSet.isConnected_iff K).mpr ⟨hπ, hne⟩

/-- Full independently constructed plus output for the ACTUAL ordinary
BGL over any ring. The map uses its canonical vertex and stable-elementary
perfect normal subgroup; every local system and fiber, connected target,
exact kernel, surjective fundamental-group map and the genuine CW-model map/inverse families are
constructed.
There is no Q-comparison or caller-provided plus/model/inverse input. -/
public theorem ordinaryBGL_independentPlus_exists_full (R : Type u) [Ring R] :
    ∃ Z : TopCat.{u}, ∃ i : ordinaryBGL R ⟶ Z, ∃ y : Z,
      ∃ hxy : i (ordinaryBGLBasepoint R) = y,
        TopCat.IsPlusConstructionAt i (ordinaryBGLBasepoint R) y hxy
          (BGLPlusSubgroup R) ∧
        TopCat.IsLocalCoefficientHomologyEquivalence i ∧
        (∀ z : Z, TopCat.IsAcyclicMapAt i z) ∧
        MonoidHom.ker (FundamentalGroup.mapOfEq i.hom
          (rfl : i.hom (ordinaryBGLBasepoint R) = i (ordinaryBGLBasepoint R))) =
            BGLPlusSubgroup R ∧
        Function.Surjective (FundamentalGroup.mapOfEq i.hom hxy) ∧
        PathConnectedSpace Z ∧
        (∃ C : TopCat.{u}, ∃ _ : T2Space C,
          ∃ _ : Topology.CWComplex (Set.univ : Set C),
            ∃ c : C ⟶ Z, ∃ e : C ≃ₕ Z, e.toFun = c.hom ∧
              ∃ g : Z ⟶ C, Nonempty (TopCat.Homotopy (c ≫ g) (𝟙 C)) ∧
                Nonempty (TopCat.Homotopy (g ≫ c) (𝟙 Z))) := by
  let K : SSet.{u} := classifyingNerve R
  let X : TopCat.{u} := ordinaryBGL R
  let x : X := ordinaryBGLBasepoint R
  let P : Subgroup (FundamentalGroup X x) := BGLPlusSubgroup R
  let : K.IsConnected := classifyingNerve_connected R
  let : PathConnectedSpace X := SSet.pathConnectedSpace_realization_of_isConnected K
  let : ConnectedSpace X := inferInstance
  let : T2Space X := SSet.realization_t2Space K
  let : Topology.CWComplex (Set.univ : Set X) := by
    change Topology.CWComplex (Set.univ : Set (SSet.toTop.obj K))
    infer_instance
  let : P.Normal := BGLPlusSubgroup.instNormal R
  let : Group.IsPerfect P := BGLPlusSubgroup.instIsPerfect R
  let Z := AlgebraicTopology.LoopCellRegularThreeComparison.originalThree X x P
  let i : X ⟶ Z := AlgebraicTopology.LoopCellAttachment.inclusion X x P ≫
    AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let y := AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeBasePoint X x P
  let M := AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeModel X x P
  let c := AlgebraicTopology.CellFamilySimplicialModel.realizationMap
    (AlgebraicTopology.LoopCellAttachment.space X x P) 2 P
      (AlgebraicTopology.LoopCellSphericalGenerators.sphericalGenerator X x P)
  have h :=
      AlgebraicTopology.LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P
  rcases h with ⟨hp, hL, ha, hk, hsurj, hpc, _, _, hT, hCW, e, he, g, hleft, hright⟩
  exact ⟨Z, i, y, rfl, hp, hL, ha, hk, hsurj, hpc,
    SSet.toTop.obj M, hT, hCW, c, e, he, g, hleft, hright⟩

/-- Every ring has an independently constructed plus map on the actual
ordinary algebraic BGL, at its canonical realized vertex and with the
existing perfect normal subgroup. The target, map, point and genuine CW
model are constructed; both model inverse homotopies belong to its actual
homotopy equivalence. No Q-construction comparison is used. -/
public theorem ordinaryBGL_independentPlus_exists (R : Type u) [Ring R] :
    ∃ Z : TopCat.{u}, ∃ i : ordinaryBGL R ⟶ Z, ∃ y : Z,
      ∃ hxy : i (ordinaryBGLBasepoint R) = y,
        TopCat.IsPlusConstructionAt i (ordinaryBGLBasepoint R) y hxy
          (BGLPlusSubgroup R) ∧
        (∀ z : Z, TopCat.IsAcyclicMapAt i z) ∧
        (∃ C : TopCat.{u}, ∃ _ : T2Space C,
          ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Z)) := by
  obtain ⟨Z, i, y, hxy, hp, _, ha, _, _, _, C, hT, hCW, c, e, _, g, _, _⟩ :=
    ordinaryBGL_independentPlus_exists_full R
  exact ⟨Z, i, y, hxy, hp, ha, C, hT, hCW, ⟨e⟩⟩


end AlgebraicKTheory.StableGL

end
