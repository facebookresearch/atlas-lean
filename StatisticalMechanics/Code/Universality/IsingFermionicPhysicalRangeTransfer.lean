/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalUnitRangeVariation










namespace StatMech.Universality

noncomputable section



theorem fkIsingSquareRadialPatchPrimal_physicalDeepVariation_sq_le_of_ghostComparison
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) (base : Real)
    (hprimalLower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
    (hdualUpper : ∀ q,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
    ((1 / (m : Real)) *
      ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
        |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
          fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) ^ 2 ≤
      64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  obtain ⟨hprimal, -⟩ :=
    fkIsingSquareRadialPatch_unitRange_of_primalLower_dualUpper
      n m hn hm hm2 base hprimalLower hdualUpper
  exact fkIsingSquareRadialPatchPrimal_physicalDeepVariation_sq_le_of_unitRange
    n m hn hm (by omega) r hr base (fun p ↦ (hprimal p).1)
      (fun p ↦ (hprimal p).2)


theorem fkIsingSquareRadialPatchDual_physicalDeepVariation_sq_le_of_ghostComparison
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) (base : Real)
    (hprimalLower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
    (hdualUpper : ∀ q,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
    ((1 / (m : Real)) *
      ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
        |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
          fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤
      64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  obtain ⟨-, hdual⟩ :=
    fkIsingSquareRadialPatch_unitRange_of_primalLower_dualUpper
      n m hn hm hm2 base hprimalLower hdualUpper
  exact fkIsingSquareRadialPatchDual_physicalDeepVariation_sq_le_of_unitRange
    n m hn hm hm2 r hr base (fun q ↦ (hdual q).1)
      (fun q ↦ (hdual q).2)

end

end StatMech.Universality
