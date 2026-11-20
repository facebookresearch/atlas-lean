/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalRadialPatch









namespace StatMech.Universality

open Finset
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareInteriorRadialIncrement_le_one
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareInteriorRadialIncrement n hn e ≤ 1 := by
  induction e using Quot.ind with
  | _ d =>
      exact fkIsingSquareWiredPrimitiveIncrement_le_one n hn (.dart d.1)

theorem abs_fkIsingSquareRadialPatchHorizontalSignedIncrement_le_one
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) :
    |fkIsingSquareRadialPatchHorizontalSignedIncrement
        n m hn hm hmpos i j| ≤ 1 := by
  have h0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
  have h1 := fkIsingSquareInteriorRadialIncrement_le_one n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
  by_cases h : Even (i + j)
  · simp [fkIsingSquareRadialPatchHorizontalSignedIncrement, h,
      abs_of_nonneg h0, h1]
  · simp [fkIsingSquareRadialPatchHorizontalSignedIncrement, h,
      abs_of_nonneg h0, h1]

theorem abs_fkIsingSquareRadialPatchVerticalSignedIncrement_le_one
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) :
    |fkIsingSquareRadialPatchVerticalSignedIncrement
        n m hn hm hmpos i j| ≤ 1 := by
  have h0 := fkIsingSquareInteriorRadialIncrement_nonneg n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
  have h1 := fkIsingSquareInteriorRadialIncrement_le_one n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
  by_cases h : Even (i + j)
  · simp [fkIsingSquareRadialPatchVerticalSignedIncrement, h,
      abs_of_nonneg h0, h1]
  · simp [fkIsingSquareRadialPatchVerticalSignedIncrement, h,
      abs_of_nonneg h0, h1]



theorem abs_fkIsingSquareRadialPatchPrimitive_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) :
    |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| ≤ i + j := by
  unfold fkIsingSquareRadialPatchPrimitive isingRectanglePrimitive
  calc
    |(∑ k ∈ range i,
        fkIsingSquareRadialPatchHorizontalSignedIncrement
          n m hn hm hmpos k 0) +
      ∑ l ∈ range j,
        fkIsingSquareRadialPatchVerticalSignedIncrement
          n m hn hm hmpos i l| ≤
        |∑ k ∈ range i,
          fkIsingSquareRadialPatchHorizontalSignedIncrement
            n m hn hm hmpos k 0| +
        |∑ l ∈ range j,
          fkIsingSquareRadialPatchVerticalSignedIncrement
            n m hn hm hmpos i l| := abs_add_le _ _
    _ ≤ (∑ _k ∈ range i, (1 : Real)) +
        ∑ _l ∈ range j, (1 : Real) := by
      gcongr
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun k _ ↦
            abs_fkIsingSquareRadialPatchHorizontalSignedIncrement_le_one
              n m hn hm hmpos k 0)
      · exact (Finset.abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun l _ ↦
            abs_fkIsingSquareRadialPatchVerticalSignedIncrement_le_one
              n m hn hm hmpos i l)
    _ = i + j := by simp

end

end StatMech.Universality
