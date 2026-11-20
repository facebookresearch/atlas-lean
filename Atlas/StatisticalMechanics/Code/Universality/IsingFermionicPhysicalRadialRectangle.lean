/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalRadialIncidence
import Code.Universality.IsingFermionicPhysicalEnergy
import Code.Universality.IsingFermionicPrimitiveFiniteIntegration











namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section




structure FKIsingSquareInteriorRadialRectanglePlacement
    (n : Nat) (hn : 0 < n) where
  horizontal : Nat → Nat → FKIsingSquareInteriorRadialIncidence n hn
  vertical : Nat → Nat → FKIsingSquareInteriorRadialIncidence n hn
  cell : Nat → Nat → FKIsingSquareInteriorRadialCell n
  west : ∀ i j, vertical i j =
    fkIsingSquareInteriorRadialCellIncidence n hn (cell i j) .west
  east : ∀ i j, horizontal i (j + 1) =
    fkIsingSquareInteriorRadialCellIncidence n hn (cell i j) .east
  south : ∀ i j, horizontal i j =
    fkIsingSquareInteriorRadialCellIncidence n hn (cell i j) .south
  north : ∀ i j, vertical (i + 1) j =
    fkIsingSquareInteriorRadialCellIncidence n hn (cell i j) .north

namespace FKIsingSquareInteriorRadialRectanglePlacement

variable {n : Nat} {hn : 0 < n}

def horizontalIncrement
    (P : FKIsingSquareInteriorRadialRectanglePlacement n hn) :
    Nat → Nat → Real :=
  fun i j ↦ fkIsingSquareInteriorRadialIncrement n hn (P.horizontal i j)

def verticalIncrement
    (P : FKIsingSquareInteriorRadialRectanglePlacement n hn) :
    Nat → Nat → Real :=
  fun i j ↦ fkIsingSquareInteriorRadialIncrement n hn (P.vertical i j)


theorem increment_closed
    (P : FKIsingSquareInteriorRadialRectanglePlacement n hn) :
    IsingRectangleClosedOneForm P.horizontalIncrement P.verticalIncrement := by
  intro i j
  rw [show P.verticalIncrement i j =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell i j) .west) by
        exact congrArg _ (P.west i j),
    show P.horizontalIncrement i (j + 1) =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell i j) .east) by
        exact congrArg _ (P.east i j),
    show P.horizontalIncrement i j =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell i j) .south) by
        exact congrArg _ (P.south i j),
    show P.verticalIncrement (i + 1) j =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell i j) .north) by
        exact congrArg _ (P.north i j)]
  exact fkIsingSquareInteriorRadialCell_increment_closed n hn (P.cell i j)


noncomputable def representative
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    FKIsingSquareInteriorRadialDart n :=
  Quotient.out e

theorem mk_representative
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    Quot.mk _ (representative e) = e :=
  Quotient.out_eq e


noncomputable def carrier
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    FKIsingSquareWiredCarrier n :=
  .dart (representative e).1

theorem primitiveIncrement_carrier
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareWiredPrimitiveIncrement n hn (carrier e) =
      fkIsingSquareInteriorRadialIncrement n hn e := by
  have h := congrArg (fkIsingSquareInteriorRadialIncrement n hn)
    (mk_representative e)
  simpa [carrier, representative] using h

noncomputable def horizontalCarrier
    (P : FKIsingSquareInteriorRadialRectanglePlacement n hn) :
    Nat → Nat → FKIsingSquareWiredCarrier n :=
  fun i j ↦ carrier (P.horizontal i j)

noncomputable def verticalCarrier
    (P : FKIsingSquareInteriorRadialRectanglePlacement n hn) :
    Nat → Nat → FKIsingSquareWiredCarrier n :=
  fun i j ↦ carrier (P.vertical i j)



theorem carrier_increment_closed
    (P : FKIsingSquareInteriorRadialRectanglePlacement n hn) :
    IsingRectangleClosedOneForm
      (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
        (P.horizontalCarrier i j))
      (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
        (P.verticalCarrier i j)) := by
  simpa [horizontalCarrier, verticalCarrier, horizontalIncrement,
    verticalIncrement, primitiveIncrement_carrier] using P.increment_closed



theorem physicalNormalized_normSq_sum_le
    (P : FKIsingSquareInteriorRadialRectanglePlacement n hn)
    (C mesh L : Real) (width height : Nat)
    (hupper : ∀ i j, fkIsingSquareWiredIntegratedPrimitive n hn
      P.horizontalCarrier P.verticalCarrier i j ≤ C)
    (hmesh : 0 < mesh) (hC : 0 ≤ C)
    (hscale : mesh * (height + width) ≤ L) :
    mesh ^ 2 *
        ((∑ j ∈ Finset.range height, ∑ i ∈ Finset.range width,
            Complex.normSq
              (fkIsingSquareWiredObservableGrid n hn P.horizontalCarrier i j /
                (Real.sqrt (2 * mesh) : Complex))) +
          (∑ i ∈ Finset.range width, ∑ j ∈ Finset.range height,
            Complex.normSq
              (fkIsingSquareWiredObservableGrid n hn P.verticalCarrier i j /
                (Real.sqrt (2 * mesh) : Complex)))) ≤
      L * C / 2 := by
  exact fkIsingSquareWired_physicalNormalized_normSq_sum_le n hn
    P.horizontalCarrier P.verticalCarrier P.carrier_increment_closed
    C mesh L width height hupper hmesh hC hscale

end FKIsingSquareInteriorRadialRectanglePlacement




structure FKIsingSquareInteriorRadialFiniteRectanglePlacement
    (n : Nat) (hn : 0 < n) (width height : Nat) where
  horizontal : Nat → Nat → FKIsingSquareInteriorRadialIncidence n hn
  vertical : Nat → Nat → FKIsingSquareInteriorRadialIncidence n hn
  cell : Fin width → Fin height → FKIsingSquareInteriorRadialCell n
  west : ∀ i j, vertical i.1 j.1 =
    fkIsingSquareInteriorRadialCellIncidence n hn (cell i j) .west
  east : ∀ i j, horizontal i.1 (j.1 + 1) =
    fkIsingSquareInteriorRadialCellIncidence n hn (cell i j) .east
  south : ∀ i j, horizontal i.1 j.1 =
    fkIsingSquareInteriorRadialCellIncidence n hn (cell i j) .south
  north : ∀ i j, vertical (i.1 + 1) j.1 =
    fkIsingSquareInteriorRadialCellIncidence n hn (cell i j) .north

namespace FKIsingSquareInteriorRadialFiniteRectanglePlacement

variable {n width height : Nat} {hn : 0 < n}




noncomputable def singleton
    (e : FKIsingSquareInteriorRadialCell n) :
    FKIsingSquareInteriorRadialFiniteRectanglePlacement n hn 1 1 where
  horizontal i j :=
    if j = 0 then fkIsingSquareInteriorRadialCellIncidence n hn e .south
    else fkIsingSquareInteriorRadialCellIncidence n hn e .east
  vertical i j :=
    if i = 0 then fkIsingSquareInteriorRadialCellIncidence n hn e .west
    else fkIsingSquareInteriorRadialCellIncidence n hn e .north
  cell _ _ := e
  west i _ := by simp [i.eq_zero]
  east _ j := by simp [j.eq_zero]
  south _ j := by simp [j.eq_zero]
  north i _ := by simp [i.eq_zero]

def horizontalIncrement
    (P : FKIsingSquareInteriorRadialFiniteRectanglePlacement
      n hn width height) : Nat → Nat → Real :=
  fun i j ↦ fkIsingSquareInteriorRadialIncrement n hn (P.horizontal i j)

def verticalIncrement
    (P : FKIsingSquareInteriorRadialFiniteRectanglePlacement
      n hn width height) : Nat → Nat → Real :=
  fun i j ↦ fkIsingSquareInteriorRadialIncrement n hn (P.vertical i j)

theorem increment_closed_on
    (P : FKIsingSquareInteriorRadialFiniteRectanglePlacement
      n hn width height) :
    IsingRectangleClosedOneFormOn P.horizontalIncrement P.verticalIncrement
      width height := by
  intro i hi j hj
  let ii : Fin width := ⟨i, hi⟩
  let jj : Fin height := ⟨j, hj⟩
  rw [show P.verticalIncrement i j =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell ii jj) .west) by
        exact congrArg _ (P.west ii jj),
    show P.horizontalIncrement i (j + 1) =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell ii jj) .east) by
        exact congrArg _ (P.east ii jj),
    show P.horizontalIncrement i j =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell ii jj) .south) by
        exact congrArg _ (P.south ii jj),
    show P.verticalIncrement (i + 1) j =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell ii jj) .north) by
        exact congrArg _ (P.north ii jj)]
  exact fkIsingSquareInteriorRadialCell_increment_closed n hn (P.cell ii jj)

noncomputable def horizontalCarrier
    (P : FKIsingSquareInteriorRadialFiniteRectanglePlacement
      n hn width height) : Nat → Nat → FKIsingSquareWiredCarrier n :=
  fun i j ↦ FKIsingSquareInteriorRadialRectanglePlacement.carrier
    (P.horizontal i j)

noncomputable def verticalCarrier
    (P : FKIsingSquareInteriorRadialFiniteRectanglePlacement
      n hn width height) : Nat → Nat → FKIsingSquareWiredCarrier n :=
  fun i j ↦ FKIsingSquareInteriorRadialRectanglePlacement.carrier
    (P.vertical i j)

theorem carrier_increment_closed_on
    (P : FKIsingSquareInteriorRadialFiniteRectanglePlacement
      n hn width height) :
    IsingRectangleClosedOneFormOn
      (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
        (P.horizontalCarrier i j))
      (fun i j ↦ fkIsingSquareWiredPrimitiveIncrement n hn
        (P.verticalCarrier i j)) width height := by
  simpa [horizontalCarrier, verticalCarrier, horizontalIncrement,
    verticalIncrement,
    FKIsingSquareInteriorRadialRectanglePlacement.primitiveIncrement_carrier]
    using P.increment_closed_on



theorem physicalNormalized_normSq_sum_le
    (P : FKIsingSquareInteriorRadialFiniteRectanglePlacement
      n hn width height)
    (C mesh L : Real)
    (hupper : ∀ i ≤ width, ∀ j ≤ height,
      fkIsingSquareWiredIntegratedPrimitive n hn
        P.horizontalCarrier P.verticalCarrier i j ≤ C)
    (hmesh : 0 < mesh) (hC : 0 ≤ C)
    (hscale : mesh * (height + width) ≤ L) :
    mesh ^ 2 *
        ((∑ j ∈ Finset.range height, ∑ i ∈ Finset.range width,
            Complex.normSq
              (fkIsingSquareWiredObservableGrid n hn P.horizontalCarrier i j /
                (Real.sqrt (2 * mesh) : Complex))) +
          (∑ i ∈ Finset.range width, ∑ j ∈ Finset.range height,
            Complex.normSq
              (fkIsingSquareWiredObservableGrid n hn P.verticalCarrier i j /
                (Real.sqrt (2 * mesh) : Complex)))) ≤
      L * C / 2 := by
  apply isingRectangle_physicalNormalized_normSq_sum_le_on
    (fkIsingSquareWiredObservableGrid n hn P.horizontalCarrier)
    (fkIsingSquareWiredObservableGrid n hn P.verticalCarrier)
    C mesh L width height
  · simpa [fkIsingSquareWiredObservableGrid,
      fkIsingSquareWiredPrimitiveIncrement, isingPrimitiveIncrement] using
      P.carrier_increment_closed_on
  · intro i hi j hj
    exact fkIsingSquareWiredIntegratedPrimitive_nonneg n hn
      P.horizontalCarrier P.verticalCarrier i j
  · exact hupper
  · exact hmesh
  · exact hC
  · exact hscale

end FKIsingSquareInteriorRadialFiniteRectanglePlacement

end

end StatMech.Universality
