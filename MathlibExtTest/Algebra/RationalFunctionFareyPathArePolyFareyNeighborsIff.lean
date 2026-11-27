/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.RationalFunctionFareyPathArePolyFareyNeighborsIff
import MathlibExt.Algebra.ContinuedFractions.RationalFunctionFareyPath
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Field.ZMod

/-!
# Tests for the polynomial Farey neighbour criterion

We apply the criterion to fractions over `ℚ` and derive that a Farey fraction
cannot neighbour itself.
-/

namespace MathlibExtTest.Algebra.RationalFunctionFareyPathArePolyFareyNeighborsIff

open Polynomial MetaMathlibExt

open scoped Classical in
example : ArePolyFareyNeighbors 1 ((0 : ℚ[X]), 1) (1, X) := by
  classical
  have hw : ((0 : ℚ[X]), 1) ∈ polyFareySeries 1 := by
    refine ⟨?_, ?_, isCoprime_zero_left.mpr isUnit_one, monic_one⟩ <;> simp
  have hz : ((1 : ℚ[X]), X) ∈ polyFareySeries 1 := by
    refine ⟨?_, ?_, isCoprime_one_left, monic_X⟩ <;> simp
  apply (arePolyFareyNeighbors_iff 1 hw hz).mpr
  simp

open scoped Classical in
example : ArePolyFareyNeighbors 1 ((1 : ℚ[X]), X) (1, X + 1) := by
  classical
  have hw : ((1 : ℚ[X]), X) ∈ polyFareySeries 1 := by
    refine ⟨?_, ?_, isCoprime_one_left, monic_X⟩ <;> simp
  have hdeg : (X + 1 : ℚ[X]).degree = 1 := by
    simpa only [C_1] using degree_X_add_C (1 : ℚ)
  have hz : ((1 : ℚ[X]), X + 1) ∈ polyFareySeries 1 := by
    refine ⟨?_, ?_, isCoprime_one_left, ?_⟩
    · change (1 : ℚ[X]).degree < (X + 1 : ℚ[X]).degree
      rw [degree_one, hdeg]
      exact WithBot.coe_lt_coe.mpr Nat.zero_lt_one
    · exact (natDegree_eq_of_degree_eq_some hdeg).le
    · simpa using (monic_X_add_C (1 : ℚ))
  apply (arePolyFareyNeighbors_iff 1 hw hz).mpr
  simp

example {F : Type*} [Field F] [DecidableEq (RatFunc F)] (n : ℕ)
    {w : F[X] × F[X]} (hw : w ∈ polyFareySeries n) : ¬ ArePolyFareyNeighbors n w w := by
  intro h
  have hd := (arePolyFareyNeighbors_iff n hw hw).mp h
  have hbot : (⊥ : WithBot ℕ) = 0 := by simpa only [sub_self, degree_zero] using hd
  exact WithBot.bot_ne_coe hbot

section NeighborCount

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem one_div_X_mem : ((1 : (ZMod 3)[X]), X) ∈ polyFareySeries 2 := by
  refine ⟨?_, ?_, isCoprime_one_left, monic_X⟩ <;> simp

-- In order two, 1/X has two degree-one and six degree-two neighbours.
open scoped Classical in
example :
    Set.ncard {z : (ZMod 3)[X] × (ZMod 3)[X] | z ∈ polyFareySeries 2 ∧ z.2.natDegree = 1 ∧
      ArePolyFareyNeighbors 2 (1, X) z} = 2 ∧
    Set.ncard {z : (ZMod 3)[X] × (ZMod 3)[X] | z ∈ polyFareySeries 2 ∧ z.2.natDegree = 2 ∧
      ArePolyFareyNeighbors 2 (1, X) z} = 6 := by
  have h := (polyFarey_neighbor_count 3 2 one_div_X_mem (by simp)).1
  exact ⟨by simpa using h 0 (by simp), by simpa using h 1 (by simp)⟩

-- The unique smaller neighbour is the constant-denominator fraction 0/1.
open scoped Classical in
example (z : (ZMod 3)[X] × (ZMod 3)[X]) (hz : z ∈ polyFareySeries 2)
    (hdeg : z.2.natDegree < 1) (h : ArePolyFareyNeighbors 2 (1, X) z) : z = (0, 1) := by
  have h0 : ((0 : (ZMod 3)[X]), 1) ∈ polyFareySeries 2 := by
    refine ⟨?_, ?_, isCoprime_zero_left.mpr isUnit_one, monic_one⟩ <;> simp
  have hn : ArePolyFareyNeighbors 2 ((1 : (ZMod 3)[X]), X) (0, 1) :=
    (arePolyFareyNeighbors_iff 2 one_div_X_mem h0).mpr (by simp)
  exact (polyFarey_neighbor_count 3 2 one_div_X_mem (by simp)).2.unique
    ⟨hz, by simpa using hdeg, h⟩ ⟨h0, by simp, hn⟩

end NeighborCount

end MathlibExtTest.Algebra.RationalFunctionFareyPathArePolyFareyNeighborsIff
