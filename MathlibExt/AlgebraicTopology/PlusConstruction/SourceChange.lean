/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidCounit
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence
public import MathlibExt.AlgebraicTopology.PlusConstruction.HomologyEquivalence
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatWeakLocalCoefficients
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyEquivalence
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PiOneMapComposition
public import Mathlib.Algebra.Group.Equiv.Defs

/-!
# Transport an original plus map to its actual classical source model

The model is |Sing X| with its original counit. Its canonical vertex maps
exactly to x. The subgroup is the comap through the ACTUAL counit π₁ map;
normality and perfectness are derived using the proved π₁ bijection. The
original all-local-coefficient maps give canonical acyclicity of the literal
composite. The counit comparison works for every source space; no lifted
ring, desired subgroup, plus witness or model comparison is a caller input.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap Simplicial

universe u

namespace TopCat.IsPlusConstructionAt

/-- The original plus map pulls back to the actual same-universe classical
singular realization, with the literal induced subgroup and source map. -/
public theorem on_singularRealization
    {X Y : TopCat.{u}} [PathConnectedSpace Y]
    {j : X ⟶ Y} {x : X} {y : Y} {hxy : j x = y}
    {P : Subgroup (FundamentalGroup X x)} [P.Normal] [Group.IsPerfect P]
    (hj : TopCat.IsPlusConstructionAt j x y hxy P) :
    let C := SSet.toTop.obj (TopCat.toSSet.obj X)
    let c : C := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)
    let s := sSetTopAdj.counit.app X
    let hs : s c = x :=
      (TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x)).trans
        (TopCat.toSSetObj₀Equiv.apply_symm_apply x)
    let m := FundamentalGroup.mapOfEq s.hom hs
    let Q := P.comap m
    ∃ hN : Q.Normal, ∃ hP : Group.IsPerfect Q,
      @TopCat.IsPlusConstructionAt C Y (s ≫ j) c y
        ((congrArg j hs).trans hxy) Q hN hP ∧
          TopCat.IsLocalCoefficientHomologyEquivalence (s ≫ j) := by
  let C := SSet.toTop.obj (TopCat.toSSet.obj X)
  let c : C := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)
  let s := sSetTopAdj.counit.app X
  have hs : s c = x :=
    (TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x)).trans
      (TopCat.toSSetObj₀Equiv.apply_symm_apply x)
  let m := FundamentalGroup.mapOfEq s.hom hs
  let Q := P.comap m
  have hm : Function.Bijective m :=
    TopCat.singularRealizationCounit_pi1_bijective X x
  let ep := MulEquiv.ofBijective m hm
  have hep : ep.toMonoidHom = m := rfl
  have hN : Q.Normal := inferInstance
  have hP : Group.IsPerfect Q := by
    change Group.IsPerfect (P.comap m)
    rw [← hep, Subgroup.comap_equiv_eq_map_symm']
    exact Group.IsPerfect.map ep.symm.toMonoidHom
  letI : Q.Normal := hN
  letI : Group.IsPerfect Q := hP
  have hsL : TopCat.IsLocalCoefficientHomologyEquivalence s :=
    TopCat.weakHomotopyEquivalences.isLocalCoefficientHomologyEquivalence_allComponents s
      (SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences X)
  have hL : TopCat.IsLocalCoefficientHomologyEquivalence (s ≫ j) :=
    hsL.comp hj.localCoefficientHomologyEquivalence
  have hcy : (s ≫ j) c = y := (congrArg j hs).trans hxy
  have hc : FundamentalGroup.mapOfEq (s ≫ j).hom hcy =
      (FundamentalGroup.mapOfEq j.hom hxy).comp m := by
    have hcomp : (j.hom.comp s.hom) c = y :=
      (congrArg (fun z : X => j.hom z) hs).trans hxy
    have hMap := FundamentalGroup.mapOfEq_comp (x := c) (y := x) (z := y)
      s.hom j.hom hs hxy hcomp
    simpa only [TopCat.hom_comp, m] using hMap
  refine ⟨hN, hP, ⟨?_, ?_⟩, hL⟩
  · exact TopCat.isAcyclicMapAt_of_localCoefficientHomologyEquivalence (s ≫ j) hL y
  · rw [hc]
    ext q
    change FundamentalGroup.mapOfEq j.hom hxy (m q) = 1 ↔ m q ∈ P
    change m q ∈ MonoidHom.ker (FundamentalGroup.mapOfEq j.hom hxy) ↔ m q ∈ P
    rw [hj.kernel_eq]

end TopCat.IsPlusConstructionAt

end
