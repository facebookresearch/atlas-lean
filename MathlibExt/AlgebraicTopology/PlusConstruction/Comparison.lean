/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.HomologyEquivalence
public import MathlibExt.AlgebraicTopology.PlusConstruction.FundamentalGroup
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyEquivalence
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberFundamentalSurjectivity
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PiOneMapComposition

/-!
# Actual comparisons between independently chosen plus targets

A calibrated triangle between plus maps killing the same subgroup gives
the actual quotient comparison on π₁. With the usual connected CW-type
target hypotheses, the SAME forward comparison is a homotopy equivalence.
The comparison map itself is derived by the classical extension theorem in
`ClassicalComparison`; it is not a desired inverse supplied to that theorem.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe u v w

namespace TopCat.IsPlusConstructionAt

/-- The actual comparison in a commuting source triangle induces the
quotient-group equivalence. Both quotient maps come from the original plus
maps; no target fundamental-group equivalence is an input. -/
public theorem pi1Comparison_bijective
    {X B Y : TopCat.{u}} (i : X ⟶ B) (j : X ⟶ Y) (F : B ⟶ Y)
    (x : X) (b : B) (y : Y) (hix : i x = b) (hjx : j x = y)
    (hFy : F b = y) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P]
    (hi : TopCat.IsPlusConstructionAt i x b hix P)
    (hj : TopCat.IsPlusConstructionAt j x y hjx P) (hF : i ≫ F = j) :
    Function.Bijective (FundamentalGroup.mapOfEq F.hom hFy) := by
  let mi := FundamentalGroup.mapOfEq i.hom hix
  let mj := FundamentalGroup.mapOfEq j.hom hjx
  let mF := FundamentalGroup.mapOfEq F.hom hFy
  have hcompPoint : (F.hom.comp i.hom) x = y := (congrArg F.hom hix).trans hFy
  have ht : F.hom.comp i.hom = j.hom :=
    (TopCat.hom_comp i F).symm.trans (congrArg TopCat.Hom.hom hF)
  have hMapEq :
      FundamentalGroup.mapOfEq (F.hom.comp i.hom) hcompPoint = mj :=
    FundamentalGroup.mapOfEq_congr ht hcompPoint hjx
  have hComposition :
      FundamentalGroup.mapOfEq (F.hom.comp i.hom) hcompPoint = mF.comp mi :=
    FundamentalGroup.mapOfEq_comp i.hom F.hom hix hFy hcompPoint
  have hc : mF.comp mi = mj := hComposition.symm.trans hMapEq
  let ei := hi.fundamentalGroupQuotientMulEquiv hi.pi1Map_surjective
  let ej := hj.fundamentalGroupQuotientMulEquiv hj.pi1Map_surjective
  let e := ei.symm.trans ej
  have he (q : FundamentalGroup X x) : e (mi q) = mj q := by
    change ej (ei.symm (mi q)) = mj q
    rw [hi.fundamentalGroupQuotientMulEquiv_symm_map hi.pi1Map_surjective]
    exact hj.fundamentalGroupQuotientMulEquiv_mk hj.pi1Map_surjective q
  have hm (a : FundamentalGroup B b) : mF a = e a := by
    obtain ⟨q, rfl⟩ := hi.pi1Map_surjective a
    exact (congrArg (fun m => m q) hc).trans (he q).symm
  rw [show (mF : FundamentalGroup B b → FundamentalGroup Y y) = e from funext hm]
  exact e.bijective

/-- Connected independently sized unbased CW models upgrade the actual
commuting comparison to a homotopy equivalence with literal forward map F. -/
public theorem homotopyEquiv_of_commuting_triangle
    {X B Y : TopCat.{u}} [ConnectedSpace B] [ConnectedSpace Y]
    (hCWB : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ B))
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
    (i : X ⟶ B) (j : X ⟶ Y) (F : B ⟶ Y)
    (x : X) (b : B) (y : Y) (hix : i x = b) (hjx : j x = y)
    (hFy : F b = y) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P]
    (hi : TopCat.IsPlusConstructionAt i x b hix P)
    (hj : TopCat.IsPlusConstructionAt j x y hjx P) (hF : i ≫ F = j) :
    ∃ e : B ≃ₕ Y, e.toFun = F.hom := by
  obtain ⟨CB, hTB, hCB, ⟨eB⟩⟩ := hCWB
  obtain ⟨CY, hTY, hCY, ⟨eY⟩⟩ := hCWY
  letI : T2Space CB := hTB
  letI : Topology.CWComplex (Set.univ : Set CB) := hCB
  letI : T2Space CY := hTY
  letI : Topology.CWComplex (Set.univ : Set CY) := hCY
  letI : PathConnectedSpace B :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType eB
  letI : PathConnectedSpace Y :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType eY
  have hiL := hi.localCoefficientHomologyEquivalence
  have hjL : TopCat.IsLocalCoefficientHomologyEquivalence (i ≫ F) := by
    rw [hF]
    exact hj.localCoefficientHomologyEquivalence
  have hFL : TopCat.IsLocalCoefficientHomologyEquivalence F := hiL.of_comp hjL
  have hπb : Function.Bijective (FundamentalGroup.mapOfEq F.hom rfl (x := b)) := by
    have h := pi1Comparison_bijective i j F x b y hix hjx hFy P hi hj hF
    cases hFy
    exact h
  have hπ := FundamentalGroup.mapOfEq_bijective_of_pathConnected F.hom b hπb
  exact TopCat.allLocalCoefficient_CWType_piOneIso_homotopyEquiv
    ⟨CB, hTB, hCB, ⟨eB⟩⟩ ⟨CY, hTY, hCY, ⟨eY⟩⟩ F hFL hπ

end TopCat.IsPlusConstructionAt

end
