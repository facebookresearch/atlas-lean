/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowBasedComparison
public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusConstruction
public import MathlibExt.AlgebraicTopology.PlusConstruction.ClassicalMapping
public import MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentOrdinaryUnitTransport
public import MathlibExt.CategoryTheory.CategoryHomology.ClassifyingSpaceSingular
public import MathlibExt.AlgebraicTopology.LocalCoefficient.IntegralConsequence
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The derived comparison from the independent cell plus to the zero space

The based stable map kills the actual stable-elementary subgroup because
the original zero-unit fundamental group is commutative. The constructed
plus extension supplies a strict source triangle and both whole-source
relative uniqueness families. Its integral homology isomorphism is then
derived from that same triangle and the original all-local-system property
of the independent cell inclusion.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology AlgebraicTopology
open scoped TopCat.modelCategory ContinuousMap

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private theorem rowBGLPathConnected : PathConnectedSpace (ordinaryBGL R) := by
  letI : (classifyingNerve R).IsConnected :=
    CategoryTheory.nerve_isConnected_of_category_isConnected
  exact SSet.pathConnectedSpace_realization_of_isConnected (classifyingNerve R)

/-- The actual based stable map kills every element of the original
stable-elementary plus subgroup, with no killing or target H-space input. -/
public theorem finiteFreeRowBasedZeroComparison_kills_stableElementary :
    ∀ p ∈ BGLPlusSubgroup R,
      FundamentalGroup.mapOfEq (finiteFreeRowBasedZeroComparison R).hom rfl p = 1 := by
  let Y := SSet.toTop.obj
    (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))
  let x := ordinaryBGLBasepoint R
  let f : ordinaryBGL R ⟶ Y := finiteFreeRowBasedZeroComparison R
  letI : IsMulCommutative (FundamentalGroup Y (f x)) := by
    have hUnit : f x = SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.IdempotentModel R) :=
      finiteFreeRowBasedZeroComparison_basepoint R
    have hComm : IsMulCommutative (FundamentalGroup Y
        (SInverseS.ComponentTranslation.zeroSpacePoint
          (C := FGProjectiveCat.IdempotentModel R))) := IsMulCommutative.of_comm
      (SInverseS.ComponentTranslation.zeroSpace_fundamentalGroup_mul_comm
        (C := FGProjectiveCat.IdempotentModel R))
    exact hUnit.symm ▸ hComm
  let P := BGLPlusSubgroup R
  let phi : P →* FundamentalGroup Y (f x) :=
    (FundamentalGroup.mapOfEq f.hom rfl).comp P.subtype
  intro p hp
  have hPerfect : (⟨p, hp⟩ : P) ∈ commutator P := Group.IsPerfect.mem_commutator
  exact MonoidHom.mem_ker.mp ((Abelianization.commutator_subset_ker phi) hPerfect)

/-- The independently constructed actual cell plus admits a derived based
map into the original projective zero space. The source triangle is strict,
every integral homology map is an Iso, and both uniqueness homotopies fix
the entire original source image at every time. -/
public theorem finiteFreeRowIndependentPlusComparison_exists :
    let X := ordinaryBGL R
    let x := ordinaryBGLBasepoint R
    let P := BGLPlusSubgroup R
    letI : PathConnectedSpace X := by
      letI : (classifyingNerve R).IsConnected :=
        CategoryTheory.nerve_isConnected_of_category_isConnected
      exact SSet.pathConnectedSpace_realization_of_isConnected (classifyingNerve R)
    let B := LoopCellRegularThreeComparison.originalThree X x P
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    let Y := SSet.toTop.obj
      (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))
    ∃ F : B ⟶ Y,
      i ≫ F = finiteFreeRowBasedZeroComparison R ∧
      F (i x) = SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.IdempotentModel R) ∧
      (∀ q : ℕ, IsIso ((singularIntegralHomologyFunctor q).map F)) ∧
      ∀ G : B ⟶ Y, i ≫ G = finiteFreeRowBasedZeroComparison R →
        Nonempty (ContinuousMap.HomotopyRel F.hom G.hom (Set.range i)) ∧
          Nonempty (ContinuousMap.HomotopyRel G.hom F.hom (Set.range i)) := by
  let X := ordinaryBGL R
  let x := ordinaryBGLBasepoint R
  let P := BGLPlusSubgroup R
  letI : PathConnectedSpace X := rowBGLPathConnected R
  letI : ConnectedSpace X := inferInstance
  letI : T2Space X := SSet.realization_t2Space (classifyingNerve R)
  letI : Topology.CWComplex (Set.univ : Set X) := by
    change Topology.CWComplex (Set.univ : Set (SSet.toTop.obj (classifyingNerve R)))
    infer_instance
  let B := LoopCellRegularThreeComparison.originalThree X x P
  let i := LoopCellAttachment.inclusion X x P ≫
    LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let Y := SSet.toTop.obj
    (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))
  let f : X ⟶ Y := finiteFreeRowBasedZeroComparison R
  obtain ⟨r, F, hFr, hF, hr, hTriangle, hLeft, hRight, hUnique⟩ :=
    LoopCellIndependentPlus.original_connected_CW_plus_map_extension X x P Y f
      (finiteFreeRowBasedZeroComparison_kills_stableElementary R)
  have hi : TopCat.IsLocalCoefficientHomologyEquivalence i :=
    (LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P).2.1
  have hPoint : F (i x) =
      SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.IdempotentModel R) :=
    (ConcreteCategory.congr_hom hF x).trans
      (finiteFreeRowBasedZeroComparison_basepoint R)
  have hUniqueFamilies :
      ∀ G : B ⟶ Y, i ≫ G = f →
        Nonempty (ContinuousMap.HomotopyRel F.hom G.hom (Set.range i)) ∧
          Nonempty (ContinuousMap.HomotopyRel G.hom F.hom (Set.range i)) := hUnique
  refine ⟨F, hF, hPoint, ?_, hUniqueFamilies⟩
  intro q
  let Hq := singularIntegralHomologyFunctor q
  let a : Hq.obj X ⟶ Hq.obj B := Hq.map i
  let b : Hq.obj B ⟶ Hq.obj Y := Hq.map F
  letI : IsIso a := hi.isIntegral q
  have hMap : a ≫ b = Hq.map f :=
    (Hq.map_comp i F).symm.trans (congrArg Hq.map hF)
  have hIso : IsIso (a ≫ b) := by
    rw [hMap]
    exact finiteFreeRowBasedZeroComparison_integral_isIso R q
  change IsIso b
  exact (isIso_comp_left_iff a b).mp hIso

end AlgebraicKTheory.StableGL

end
