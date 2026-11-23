/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.PlusConstruction.ClassicalExistence
import Mathlib.Data.ZMod.Basic
import MathlibExt.AlgebraicTopology.PlusConstruction.FundamentalGroup
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Logic.Small.Defs

/-! External clients use the public constructed output and original maps. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
open scoped ContinuousMap Simplicial TopCat.modelCategory

universe u

private local instance publicPlusClientColimits (I : Type u) :
    HasColimitsOfShape (Discrete I) AddCommGrpCat.{u} :=
  letI : Small.{u} (Discrete I) := small_self (Discrete I)
  AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

private local instance publicPlusClientCoproducts : HasCoproducts.{u} AddCommGrpCat.{u} :=
  fun I =>
    letI : Small.{u} (Discrete I) := small_self (Discrete I)
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)

#check @AlgebraicTopology.LoopCellIndependentPlus.original_connected_CW_plus_construction
#print axioms AlgebraicTopology.LoopCellIndependentPlus.original_connected_CW_plus_construction
#check @AlgebraicTopology.LoopCellIndependentPlus.original_connected_CW_plus_construction_full
#print axioms AlgebraicTopology.LoopCellIndependentPlus.original_connected_CW_plus_construction_full
#check @AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreeToTwoBoundary_recipe
#print axioms AlgebraicTopology.LoopCellRegularThreeComparison.nativeThreeToTwoBoundary_recipe
#check @AlgebraicTopology.LoopCellRegularThreeComparison.originalRR3ToRR2Matrix_eq_id
#print axioms AlgebraicTopology.LoopCellRegularThreeComparison.originalRR3ToRR2Matrix_eq_id

namespace ClassicalExistenceClients

variable (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
  [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
  [P.Normal] [Group.IsPerfect P]

private local instance sourcePaths : PathConnectedSpace X :=
  Topology.CWComplex.pathConnectedSpace_of_connected_CWType
    (ContinuousMap.HomotopyEquiv.refl X)

private abbrev Z := LoopCellRegularThreeComparison.originalThree X x P
private abbrev i := LoopCellAttachment.inclusion X x P ≫
  LoopCellRegularThreeComparison.originalThreeInclusion X x P
private abbrev y := LoopCellRegularThreeComparison.originalThreeBasePoint X x P
private abbrev K := LoopCellRegularThreeComparison.originalThreeModel X x P
private abbrev c := CellFamilySimplicialModel.realizationMap (LoopCellAttachment.space X x P) 2 P
  (LoopCellSphericalGenerators.sphericalGenerator X x P)
private abbrev R : AddCommGrpCat.{u} := singularIntegralCoefficients.{u}
private abbrev F := (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj (R : AddCommGrpCat.{u})
private abbrev A := LoopCellPulledSimplicialModel.nativePair X x P
private abbrev B := LoopCellRegularThreeComparison.nativeThreePair X x P
private abbrev f := SSet.chainComplexMap (A X x P).hom R ≫
  F.map (LoopCellRegularThreeComparison.nativeTwoToThreePullbackIso X x P).hom
private abbrev g := SSet.chainComplexMap (B X x P).hom R

-- 1. The entire original relative quotient vanishes in every degree.
example (n : ℕ) : IsZero ((cokernel (f X x P ≫ g X x P)).homology n) := by
  rcases LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P with
    ⟨_, _, _, _, _, _, h, _, _⟩
  exact h n

-- 2. The literal original regular projection has all homology maps invertible.
example (n : ℕ) : IsIso (SSet.homologyMap
    (pullback.snd (TopCat.toSSet.map (i X x P))
      (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj (Z X x P))
        (TopCat.toSSetObj₀Equiv.symm (y X x P)))) R n) := by
  rcases LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P with
    ⟨_, _, _, _, _, _, _, h, _⟩
  exact h n

-- 3. Every original target system, without a flatness premise.
example (L : TopCat.LocalSystem ℤ (Z X x P)) (n : ℕ) :
    IsIso (TopCat.localCoefficientPullbackHomologyMap (i X x P) L n) := by
  rcases LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P with
    ⟨_, h, _, _, _, _, _, _, _⟩
  exact h L n

-- 4. Canonical reduced acyclicity at every actual target point.
example (z : Z X x P) : TopCat.IsAcyclicMapAt (i X x P) z := by
  rcases LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P with
    ⟨_, _, h, _, _, _, _, _, _⟩
  exact h z

-- 5. The actual plus map has its exact kernel and a connected target.
example : TopCat.IsPlusConstructionAt (i X x P) x (y X x P) rfl P ∧
    MonoidHom.ker (FundamentalGroup.mapOfEq (i X x P).hom
      (rfl : (i X x P).hom x = y X x P)) = P ∧ PathConnectedSpace (Z X x P) := by
  rcases LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P with
    ⟨hp, _, _, hk, _, hc, _, _, _⟩
  exact ⟨hp, hk, hc⟩

-- 6. A genuine classical CW model is constructed, not assumed.
example : ∃ C : TopCat.{u}, ∃ _ : T2Space C,
    ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Z X x P) := by
  rcases LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P with
    ⟨_, _, _, _, _, _, _, _, ht, hcw, e, _, _, _, _⟩
  exact ⟨SSet.toTop.obj (K X x P), ht, hcw, ⟨e⟩⟩

-- 7. The returned model uses the literal original comparison.
example : ∃ e : SSet.toTop.obj (K X x P) ≃ₕ Z X x P, e.toFun = (c X x P).hom := by
  rcases LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P with
    ⟨_, _, _, _, _, _, _, _, _, _, e, he, _, _, _⟩
  exact ⟨e, he⟩

-- 8. Both ordinary inverse families concern that same original map.
example : ∃ r : Z X x P ⟶ SSet.toTop.obj (K X x P),
    Nonempty (TopCat.Homotopy (c X x P ≫ r) (𝟙 _)) ∧
      Nonempty (TopCat.Homotopy (r ≫ c X x P) (𝟙 _)) := by
  rcases LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, r, hl, hr⟩
  exact ⟨r, hl, hr⟩

-- 9–10. The original connected-CW public constructor remains usable directly.
example : ∀ z : Z X x P, TopCat.IsAcyclicMapAt (i X x P) z :=
  (LoopCellIndependentPlus.original_connected_CW_plus_construction X x P).2.1

example : ∃ C : TopCat.{u}, ∃ _ : T2Space C,
    ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Z X x P) :=
  (LoopCellIndependentPlus.original_connected_CW_plus_construction X x P).2.2

-- An additional concrete nonflat integer-system regression.
example (n : ℕ) :
    let L : TopCat.LocalSystem ℤ (Z X x P) :=
      (Functor.const (_root_.FundamentalGroupoid (Z X x P))).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2)))
    IsIso (TopCat.localCoefficientPullbackHomologyMap (i X x P) L n) := by
  rcases LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P with
    ⟨_, h, _, _, _, _, _, _, _⟩
  exact h _ n

-- The literal constructed map is onto its actual canonical-point pi1.
example : Function.Surjective (FundamentalGroup.mapOfEq (i X x P).hom
    (rfl : (i X x P).hom x = y X x P)) := by
  rcases LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P with
    ⟨_, _, _, _, hsurj, _, _, _, _⟩
  exact hsurj

-- Existing canonical quotient API, with BOTH actual-map characteristic laws.
example : ∃ e : FundamentalGroup X x ⧸ P ≃* FundamentalGroup (Z X x P) (y X x P),
    (∀ q : FundamentalGroup X x, e (QuotientGroup.mk q) =
      FundamentalGroup.mapOfEq (i X x P).hom rfl q) ∧
    (∀ q : FundamentalGroup X x, e.symm
      (FundamentalGroup.mapOfEq (i X x P).hom rfl q) = QuotientGroup.mk q) := by
  rcases LoopCellIndependentPlus.original_connected_CW_plus_construction_full X x P with
    ⟨hp, _, _, _, hsurj, _, _, _, _⟩
  exact ⟨hp.fundamentalGroupQuotientMulEquiv hsurj,
    fun q => hp.fundamentalGroupQuotientMulEquiv_mk hsurj q,
    fun q => hp.fundamentalGroupQuotientMulEquiv_symm_map hsurj q⟩

end ClassicalExistenceClients

end
