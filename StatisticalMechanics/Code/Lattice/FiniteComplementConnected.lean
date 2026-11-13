/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































import Mathlib
import Code.Lattice.StraightWalk

open Set
open SimpleGraph

namespace StatMech

namespace Lattice





theorem fcc_xLowerBound (F : Set (Site 2)) (hF : F.Finite) :
    ∃ b : ℤ, ∀ q ∈ F, b ≤ q 0 := by
  have him : ((fun q : Site 2 => q 0) '' F).Finite := hF.image _
  obtain ⟨b, hb⟩ := him.bddBelow
  exact ⟨b, fun q hq => hb ⟨q, hq, rfl⟩⟩









theorem fcc_horizWalk_off_finite (F : Set (Site 2)) (b : ℤ)
    (hb : ∀ q ∈ F, b ≤ q 0) (z : Site 2) (hz : z 0 < b) (M : ℤ) (hM : M ≤ z 0) :
    ∀ w ∈ (sw_horizSeg (z 1) (z 0) M).support, w ∉ F := by
  intro w hw hwF
  rw [sw_horizSeg_mem_support] at hw
  obtain ⟨t, ht, rfl⟩ := hw
  rw [Set.uIcc_of_ge hM] at ht
  obtain ⟨_, htr⟩ := ht
  have hble : b ≤ (![t, z 1] : Site 2) 0 := hb _ hwF
  simp only [Matrix.cons_val_zero] at hble
  linarith















theorem fcc_far_reach_off_finite (F : Set (Site 2)) (hF : F.Finite) :
    ∃ b : ℤ, (∀ q ∈ F, b ≤ q 0) ∧
      ∀ z : Site 2, z 0 ≤ b - 1 → ∀ M : ℤ, M ≤ z 0 →
        ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
          (∀ w ∈ p.support, w ∉ F) ∧
          (∀ q ∈ F, z0 0 ≤ q 0) ∧
          z0 = ![M, z 1] := by
  obtain ⟨b, hb⟩ := fcc_xLowerBound F hF
  refine ⟨b, hb, fun z hz M hM => ?_⟩
  
  have hzb : z 0 < b := by linarith
  
  have hstart : (![z 0, z 1] : Site 2) = z := by
    funext i; fin_cases i <;> rfl
  refine ⟨![M, z 1],
    (sw_horizSeg (z 1) (z 0) M).copy hstart rfl, ?_, ?_, rfl⟩
  · 
    intro w hw
    rw [Walk.support_copy] at hw
    exact fcc_horizWalk_off_finite F b hb z hzb M hM w hw
  · 
    intro q hq
    have : b ≤ q 0 := hb q hq
    simp only [Matrix.cons_val_zero]
    linarith

end Lattice

end StatMech
