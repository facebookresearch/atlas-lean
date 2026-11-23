/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusConstruction
import Mathlib.Data.ZMod.Basic
import MathlibExt.AlgebraicTopology.PlusConstruction.FundamentalGroup

/-! Ring-only external clients for the independently constructed actual BGL map. -/

noncomputable section

open CategoryTheory
open scoped ContinuousMap Simplicial TopCat.modelCategory

universe u

namespace AlgebraicKTheory.StableGL

#check @ordinaryBGL_independentPlus_exists
#print axioms ordinaryBGL_independentPlus_exists
#check @ordinaryBGL_independentPlus_exists_full
#print axioms ordinaryBGL_independentPlus_exists_full

-- The two complete previous Ring-only client conclusions are retained.
example (R : Type u) [Ring R] :
    ∃ Z : TopCat.{u}, ∃ i : ordinaryBGL R ⟶ Z, ∃ y : Z,
      ∃ hxy : i (ordinaryBGLBasepoint R) = y,
        TopCat.IsPlusConstructionAt i (ordinaryBGLBasepoint R) y hxy
          (BGLPlusSubgroup R) ∧
        (∀ z : Z, TopCat.IsAcyclicMapAt i z) ∧
        (∃ C : TopCat.{u}, ∃ _ : T2Space C,
          ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Z)) :=
  ordinaryBGL_independentPlus_exists R

example (R : Type u) [Ring R] :
    ∃ Z : TopCat.{u}, ∃ i : ordinaryBGL R ⟶ Z,
      (∀ z : Z, TopCat.IsAcyclicMapAt i z) ∧
      (∃ C : TopCat.{u}, ∃ _ : T2Space C,
        ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Z)) := by
  obtain ⟨Z, i, y, hxy, hp, ha, hc⟩ := ordinaryBGL_independentPlus_exists R
  exact ⟨Z, i, ha, hc⟩

-- Whole all-local-system and connected-target output, not a chosen-fiber-only record.
example (R : Type u) [Ring R] :
    ∃ Z : TopCat.{u}, ∃ i : ordinaryBGL R ⟶ Z,
      PathConnectedSpace Z ∧ TopCat.IsLocalCoefficientHomologyEquivalence i ∧
        (∀ z : Z, TopCat.IsAcyclicMapAt i z) := by
  obtain ⟨Z, i, y, hxy, hp, hL, ha, hk, _, hpc, hm⟩ :=
    ordinaryBGL_independentPlus_exists_full R
  exact ⟨Z, i, hpc, hL, ha⟩

-- Literal model forward comparison and both ordinary inverse families.
example (R : Type u) [Ring R] :
    ∃ Z : TopCat.{u}, ∃ _i : ordinaryBGL R ⟶ Z,
      ∃ C : TopCat.{u}, ∃ _ : T2Space C,
        ∃ _ : Topology.CWComplex (Set.univ : Set C),
          ∃ c : C ⟶ Z, ∃ e : C ≃ₕ Z, e.toFun = c.hom ∧
            ∃ g : Z ⟶ C, Nonempty (TopCat.Homotopy (c ≫ g) (𝟙 C)) ∧
              Nonempty (TopCat.Homotopy (g ≫ c) (𝟙 Z)) := by
  obtain ⟨Z, i, y, hxy, hp, hL, ha, hk, _, hpc, hm⟩ :=
    ordinaryBGL_independentPlus_exists_full R
  exact ⟨Z, i, hm⟩

-- Surjectivity uses exactly the returned y and returned point equality.
example (R : Type u) [Ring R] :
    ∃ Z : TopCat.{u}, ∃ i : ordinaryBGL R ⟶ Z, ∃ y : Z,
      ∃ hxy : i (ordinaryBGLBasepoint R) = y,
        Function.Surjective (FundamentalGroup.mapOfEq i.hom hxy) := by
  obtain ⟨Z, i, y, hxy, _, _, _, _, hsurj, _, _⟩ :=
    ordinaryBGL_independentPlus_exists_full R
  exact ⟨Z, i, y, hxy, hsurj⟩

-- Ring-only inputs derive the actual quotient and its original class laws.
example (R : Type u) [Ring R] :
    letI : (BGLPlusSubgroup R).Normal := BGLPlusSubgroup.instNormal R
    letI : Group.IsPerfect (BGLPlusSubgroup R) := BGLPlusSubgroup.instIsPerfect R
    ∃ Z : TopCat.{u}, ∃ i : ordinaryBGL R ⟶ Z, ∃ y : Z,
      ∃ hxy : i (ordinaryBGLBasepoint R) = y,
        ∃ e : FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R) ⧸
            BGLPlusSubgroup R ≃* FundamentalGroup Z y,
          (∀ q : FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R),
            e (QuotientGroup.mk q) = FundamentalGroup.mapOfEq i.hom hxy q) ∧
          (∀ q : FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R),
            e.symm (FundamentalGroup.mapOfEq i.hom hxy q) = QuotientGroup.mk q) := by
  let : (BGLPlusSubgroup R).Normal := BGLPlusSubgroup.instNormal R
  let : Group.IsPerfect (BGLPlusSubgroup R) := BGLPlusSubgroup.instIsPerfect R
  obtain ⟨Z, i, y, hxy, hp, _, _, _, hsurj, _, _⟩ :=
    ordinaryBGL_independentPlus_exists_full R
  exact ⟨Z, i, y, hxy, hp.fundamentalGroupQuotientMulEquiv hsurj,
    fun q => hp.fundamentalGroupQuotientMulEquiv_mk hsurj q,
    fun q => hp.fundamentalGroupQuotientMulEquiv_symm_map hsurj q⟩

end AlgebraicKTheory.StableGL

end
