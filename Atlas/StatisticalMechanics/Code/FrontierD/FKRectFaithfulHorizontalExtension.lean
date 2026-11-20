/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectFaithfulJordanCrossing
import Code.Lattice.StraightWalk



open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice
open StatMech.RSW.Box

noncomputable section



def fkRectFaithfulHorizontalExtension
    (alpha beta : Int) {x y : Site 2}
    (W : (hypercubicLattice 2).Walk x y) :
    (hypercubicLattice 2).Walk ![alpha, x 1] ![beta, y 1] :=
  let W' : (hypercubicLattice 2).Walk
      ![x 0, x 1] ![y 0, y 1] := W.copy (by
        ext i
        fin_cases i <;> simp) (by
        ext i
        fin_cases i <;> simp)
  ((sw_horizSeg (x 1) alpha (x 0)).append W').append
    (sw_horizSeg (y 1) (y 0) beta)



theorem fkRectFaithfulHorizontalExtension_mem_support_iff
    (alpha beta : Int) {x y z : Site 2}
    (W : (hypercubicLattice 2).Walk x y) :
    z ∈ (fkRectFaithfulHorizontalExtension alpha beta W).support ↔
      z ∈ (sw_horizSeg (x 1) alpha (x 0)).support ∨
        z ∈ W.support ∨
          z ∈ (sw_horizSeg (y 1) (y 0) beta).support := by
  simp only [fkRectFaithfulHorizontalExtension,
    Walk.mem_support_append_iff, Walk.support_copy]
  tauto



theorem fkRectFaithfulHorizontalExtension_fst_bounds
    (alpha beta : Int) {x y : Site 2}
    (W : (hypercubicLattice 2).Walk x y)
    (hx : alpha <= x 0) (hy : y 0 <= beta)
    (hW : ∀ z ∈ W.support, alpha <= z 0 ∧ z 0 <= beta) :
    ∀ z ∈ (fkRectFaithfulHorizontalExtension alpha beta W).support,
      alpha <= z 0 ∧ z 0 <= beta := by
  have hWx := hW x W.start_mem_support
  have hWy := hW y W.end_mem_support
  intro z hz
  rw [fkRectFaithfulHorizontalExtension_mem_support_iff] at hz
  rcases hz with hz | hz | hz
  · rw [sw_horizSeg_mem_support] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Set.uIcc_of_le hx] at ht
    rcases ht with ⟨ht0, ht1⟩
    constructor <;> simp only [Matrix.cons_val_zero] <;> omega
  · exact hW z hz
  · rw [sw_horizSeg_mem_support] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Set.uIcc_of_le hy] at ht
    rcases ht with ⟨ht0, ht1⟩
    constructor <;> simp only [Matrix.cons_val_zero] <;> omega



theorem fkRectFaithfulHorizontalExtension_snd_bounds
    (alpha beta lower upper : Int) {x y : Site 2}
    (W : (hypercubicLattice 2).Walk x y)
    (hW : ∀ z ∈ W.support, lower <= z 1 ∧ z 1 <= upper) :
    ∀ z ∈ (fkRectFaithfulHorizontalExtension alpha beta W).support,
      lower <= z 1 ∧ z 1 <= upper := by
  intro z hz
  have hx := hW x W.start_mem_support
  have hy := hW y W.end_mem_support
  rw [fkRectFaithfulHorizontalExtension_mem_support_iff] at hz
  rcases hz with hz | hz | hz
  · rw [sw_horizSeg_mem_support] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    simpa using hx
  · exact hW z hz
  · rw [sw_horizSeg_mem_support] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    simpa using hy


theorem fkRectFaithfulHorizontalExtension_support_rect
    (alpha beta lower upper : Int) {x y : Site 2}
    (W : (hypercubicLattice 2).Walk x y)
    (hx : alpha <= x 0) (hy : y 0 <= beta)
    (hW : ∀ z ∈ W.support, z ∈ rect alpha beta lower upper) :
    ∀ z ∈ (fkRectFaithfulHorizontalExtension alpha beta W).support,
      z ∈ rect alpha beta lower upper := by
  intro z hz
  rw [mem_rect]
  have hfst := fkRectFaithfulHorizontalExtension_fst_bounds
    alpha beta W hx hy (by
      intro a ha
      exact ⟨(hW a ha).1, (hW a ha).2.1⟩) z hz
  have hsnd := fkRectFaithfulHorizontalExtension_snd_bounds
    alpha beta lower upper W (by
      intro a ha
      exact (hW a ha).2.2) z hz
  exact ⟨hfst.1, hfst.2, hsnd.1, hsnd.2⟩



theorem fkRectFaithfulHorizontalExtension_support_disjoint_of_core_bounds
    (alpha beta coreLeft coreRight : Int) {x y a b : Site 2}
    (W : (hypercubicLattice 2).Walk x y)
    (V : (hypercubicLattice 2).Walk a b)
    (hleft : alpha <= x 0) (hxcore : x 0 <= coreLeft)
    (hcorey : coreRight <= y 0) (hyright : y 0 <= beta)
    (hV : ∀ z ∈ V.support,
      coreLeft <= z 0 ∧ z 0 <= coreRight)
    (hdisjoint : ∀ z, z ∈ W.support -> z ∈ V.support -> False) :
    ∀ z, z ∈ (fkRectFaithfulHorizontalExtension alpha beta W).support ->
      z ∈ V.support -> False := by
  intro z hz hVz
  rw [fkRectFaithfulHorizontalExtension_mem_support_iff] at hz
  rcases hz with hz | hz | hz
  · rw [sw_horizSeg_mem_support] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Set.uIcc_of_le hleft] at ht
    rcases ht with ⟨ht0, ht1⟩
    have hVx := hV ![t, x 1] hVz
    simp only [Matrix.cons_val_zero] at hVx
    rcases hVx with ⟨hVleft, hVright⟩
    have htEq : t = x 0 := by omega
    have hsite : (![t, x 1] : Site 2) = x := by
      funext i
      fin_cases i <;> simp [htEq]
    apply hdisjoint x W.start_mem_support
    simpa [hsite] using hVz
  · exact hdisjoint z hz hVz
  · rw [sw_horizSeg_mem_support] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Set.uIcc_of_le hyright] at ht
    rcases ht with ⟨ht0, ht1⟩
    have hVx := hV ![t, y 1] hVz
    simp only [Matrix.cons_val_zero] at hVx
    rcases hVx with ⟨hVleft, hVright⟩
    have htEq : t = y 0 := by omega
    have hsite : (![t, y 1] : Site 2) = y := by
      funext i
      fin_cases i <;> simp [htEq]
    apply hdisjoint y W.end_mem_support
    simpa [hsite] using hVz

end

end StatMech.FrontierD
