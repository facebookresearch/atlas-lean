/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidCounit

public import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoid

public import MathlibExt.Topology.CWComplex.UnbasedWhitehead
public import MathlibExt.Topology.CWComplex.BasedWhitehead
public import MathlibExt.Topology.Category.TopCat.RealizedPointCofibration
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationHausdorff
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.FundamentalGroupIso

/-!
# The actual singular realization of a CW-type space

A genuine independently sized unbased CW model makes the original singular
counit a homotopy equivalence. The model used by subsequent cell proofs is
the actual realization of Sing X in X's own universe. Its canonical realized
singular vertex maps exactly to the original point, so no additional based
model or selected point-comparison witness is required.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap Simplicial TopCat.modelCategory

universe u v

namespace TopCat

/-- The original singular counit is an actual homotopy equivalence when the
target has a genuine unbased CW model in an independent universe. -/
public theorem singularRealizationHomotopyEquiv_of_CWType
    (X : TopCat.{u})
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X)) :
    ∃ e : SSet.toTop.obj (TopCat.toSSet.obj X) ≃ₕ X,
      e.toFun = (sSetTopAdj.counit.app X).hom := by
  obtain ⟨C, hT, hC, ⟨eC⟩⟩ := hCW
  let : T2Space C := hT
  let : Topology.CWComplex (Set.univ : Set C) := hC
  let R := SSet.toTop.obj (TopCat.toSSet.obj X)
  let : T2Space R := SSet.realization_t2Space (TopCat.toSSet.obj X)
  let : Topology.CWComplex (Set.univ : Set R) := inferInstance
  exact Topology.CWComplex.unbasedCWTypeWhiteheadIndependentModels
    R C (ContinuousMap.HomotopyEquiv.refl R) eC (sSetTopAdj.counit.app X)
      (SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences X)

set_option linter.unusedVariables false in
/-- Compatibility with the original CW-type counit API. Use the unconditional theorem. -/
@[deprecated singularRealizationCounit_pi1_bijective (since := "2026-10-30")]
public theorem singularRealizationCounit_pi1_bijective_of_CWType
    (X : TopCat.{u})
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X)) (x : X) :
    Function.Bijective (FundamentalGroup.mapOfEq (sSetTopAdj.counit.app X).hom
      ((TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x)).trans
        (TopCat.toSSetObj₀Equiv.apply_symm_apply x))) :=
  singularRealizationCounit_pi1_bijective X x

/-- Connected CW type gives path connectedness of the actual singular realization. -/
public theorem singularRealization_pathConnected_of_connected_CWType
    (X : TopCat.{u}) [ConnectedSpace X]
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X)) :
    PathConnectedSpace (SSet.toTop.obj (TopCat.toSSet.obj X)) := by
  obtain ⟨C, hT, hC, ⟨eC⟩⟩ := hCW
  let : T2Space C := hT
  let : Topology.CWComplex (Set.univ : Set C) := hC
  let : PathConnectedSpace X :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType eC
  obtain ⟨e, _⟩ := singularRealizationHomotopyEquiv_of_CWType X ⟨C, hT, hC, ⟨eC⟩⟩
  let H := e.left_inv.some
  refine { nonempty := ⟨e.invFun (Classical.arbitrary X)⟩, joined := ?_ }
  intro a b
  exact ⟨((H.evalAt a).symm.trans
    ((PathConnectedSpace.somePath (e a) (e b)).map e.invFun.continuous)).trans (H.evalAt b)⟩

end TopCat

namespace TopCat

/-- The ACTUAL singular counit has a based inverse and BOTH original
point-relative inverse families at its canonical realized singular vertex.
Point cofibrancy of the actual target is structural; the source point
cofibration, counit weakness and all model families are derived internally.
No based-model/inverse/homotopy witness is supplied. -/
public theorem singularRealization_based_inverse_of_cofibrant_point
    (X : TopCat.{u}) (x : X)
    [HomotopicalAlgebra.Cofibration
      (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)] :
    let c := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)
    let s := sSetTopAdj.counit.app X
    ∃ r : X ⟶ SSet.toTop.obj (TopCat.toSSet.obj X), r x = c ∧
      Nonempty (ContinuousMap.HomotopyRel (s ≫ r).hom (𝟙 (SSet.toTop.obj (TopCat.toSSet.obj X)) :
        SSet.toTop.obj (TopCat.toSSet.obj X) ⟶ SSet.toTop.obj (TopCat.toSSet.obj X)).hom {c}) ∧
      Nonempty (ContinuousMap.HomotopyRel (r ≫ s).hom (𝟙 X : X ⟶ X).hom {x}) := by
  let c := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)
  let s := sSetTopAdj.counit.app X
  let := SSet.realizedVertex_pointMap_cofibration
    (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x)
  have hs : s c = x :=
    (TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x)).trans
      (TopCat.toSSetObj₀Equiv.apply_symm_apply x)
  exact TopCat.exists_based_inverse_of_weak_of_cofibrant_points
    _ X c x s hs (SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences X)

end TopCat

end
