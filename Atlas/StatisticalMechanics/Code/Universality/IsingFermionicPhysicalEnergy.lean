/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalLocalClosed












namespace StatMech.Universality

open Finset
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section


def fkIsingSquareWiredObservableGrid
    (n : Nat) (hn : 0 < n)
    (carrier : Nat → Nat → FKIsingSquareWiredCarrier n) :
    Nat → Nat → Complex :=
  fun i j ↦ (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
    (carrier i j)


def fkIsingSquareWiredIntegratedPrimitive
    (n : Nat) (hn : 0 < n)
    (horizontalCarrier verticalCarrier :
      Nat → Nat → FKIsingSquareWiredCarrier n) :
    Nat → Nat → Real :=
  isingRectanglePrimitive
    (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
      (horizontalCarrier i j))
    (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
      (verticalCarrier i j))

theorem fkIsingSquareWiredIntegratedPrimitive_nonneg
    (n : Nat) (hn : 0 < n)
    (horizontalCarrier verticalCarrier :
      Nat → Nat → FKIsingSquareWiredCarrier n)
    (i j : Nat) :
    0 ≤ fkIsingSquareWiredIntegratedPrimitive n hn
      horizontalCarrier verticalCarrier i j := by
  unfold fkIsingSquareWiredIntegratedPrimitive isingRectanglePrimitive
  apply add_nonneg <;> apply Finset.sum_nonneg <;> intro k hk
  · exact fkIsingSquareWiredPrimitiveIncrement_nonneg n hn _
  · exact fkIsingSquareWiredPrimitiveIncrement_nonneg n hn _


theorem fkIsingSquareWiredIntegratedPrimitive_horizontal_increment
    (n : Nat) (hn : 0 < n)
    (horizontalCarrier verticalCarrier :
      Nat → Nat → FKIsingSquareWiredCarrier n)
    (hclosed : IsingRectangleClosedOneForm
      (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
        (horizontalCarrier i j))
      (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
        (verticalCarrier i j)))
    (i j : Nat) :
    fkIsingSquareWiredIntegratedPrimitive n hn
          horizontalCarrier verticalCarrier (i + 1) j -
        fkIsingSquareWiredIntegratedPrimitive n hn
          horizontalCarrier verticalCarrier i j =
      fkIsingSquareWiredPrimitiveIncrement n hn
        (horizontalCarrier i j) := by
  exact isingRectanglePrimitive_horizontal_increment _ _ hclosed i j



theorem fkIsingSquareWiredIntegratedPrimitive_vertical_increment
    (n : Nat) (hn : 0 < n)
    (horizontalCarrier verticalCarrier :
      Nat → Nat → FKIsingSquareWiredCarrier n)
    (i j : Nat) :
    fkIsingSquareWiredIntegratedPrimitive n hn
          horizontalCarrier verticalCarrier i (j + 1) -
        fkIsingSquareWiredIntegratedPrimitive n hn
          horizontalCarrier verticalCarrier i j =
      fkIsingSquareWiredPrimitiveIncrement n hn
        (verticalCarrier i j) := by
  exact isingRectanglePrimitive_vertical_increment _ _ i j





theorem fkIsingSquareWired_physicalNormalized_normSq_sum_le
    (n : Nat) (hn : 0 < n)
    (horizontalCarrier verticalCarrier :
      Nat → Nat → FKIsingSquareWiredCarrier n)
    (hclosed : IsingRectangleClosedOneForm
      (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
        (horizontalCarrier i j))
      (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
        (verticalCarrier i j)))
    (C mesh L : Real) (width height : Nat)
    (hupper : ∀ i j, fkIsingSquareWiredIntegratedPrimitive n hn
      horizontalCarrier verticalCarrier i j ≤ C)
    (hmesh : 0 < mesh) (hC : 0 ≤ C)
    (hscale : mesh * (height + width) ≤ L) :
    mesh ^ 2 *
        ((∑ j ∈ range height, ∑ i ∈ range width,
            Complex.normSq
              (fkIsingSquareWiredObservableGrid n hn horizontalCarrier i j /
                (Real.sqrt (2 * mesh) : Complex))) +
          (∑ i ∈ range width, ∑ j ∈ range height,
            Complex.normSq
              (fkIsingSquareWiredObservableGrid n hn verticalCarrier i j /
                (Real.sqrt (2 * mesh) : Complex)))) ≤
      L * C / 2 := by
  apply isingRectangle_physicalNormalized_normSq_sum_le
    (fkIsingSquareWiredObservableGrid n hn horizontalCarrier)
    (fkIsingSquareWiredObservableGrid n hn verticalCarrier)
    hclosed C mesh L width height
  · exact fkIsingSquareWiredIntegratedPrimitive_nonneg n hn
      horizontalCarrier verticalCarrier
  · exact hupper
  · exact hmesh
  · exact hC
  · exact hscale

end

end StatMech.Universality
