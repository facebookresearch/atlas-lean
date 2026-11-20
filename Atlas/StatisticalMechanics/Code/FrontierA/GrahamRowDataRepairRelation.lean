/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamComponentExchangeWeightedCounterexample
import Code.FrontierA.GrahamFourColorUniformMaskSelector












open Finset

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



def RowDataRepairRelated
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (d : leftRowData ends m j k l zero)
    (e : rightRowData ends m j k l zero) : Prop :=
  let c := (rowDataToLeftFiber ends m j k l zero d).1
  let q := (rowDataToRightFiber ends m j k l zero e).1
  ∃ X Y : Finset I,
    X ⊆ middleMask m c ∧
      Y ⊆ outerMask m c ∧
      sources ends X = {k, l} ∧
      sources ends Y = ∅ ∧
      BalancedRepairAdmissible ends m X k zero c Y ∧
      balancedSwap m X Y c = q


noncomputable def admissibleRightRowRepairs
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (d : leftRowData ends m j k l zero) :
    Finset (rightRowData ends m j k l zero) := by
  classical
  exact Finset.univ.filter (RowDataRepairRelated ends m j k l zero d)

@[simp] theorem mem_admissibleRightRowRepairs_iff
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (d : leftRowData ends m j k l zero)
    (e : rightRowData ends m j k l zero) :
    e ∈ admissibleRightRowRepairs ends m j k l zero d ↔
      RowDataRepairRelated ends m j k l zero d e := by
  classical
  simp [admissibleRightRowRepairs]



theorem rowDataRepairRelated_iff_sameMask
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (d : leftRowData ends m j k l zero)
    (e : rightRowData ends m j k l zero) :
    RowDataRepairRelated ends m j k l zero d e ↔
      fourColorMaskProfile m
          (rowDataToLeftFiber ends m j k l zero d).1 =
        fourColorMaskProfile m
          (rowDataToRightFiber ends m j k l zero e).1 := by
  let c := (rowDataToLeftFiber ends m j k l zero d).1
  let q := (rowDataToRightFiber ends m j k l zero e).1
  have hc := (rowDataToLeftFiber ends m j k l zero d).2
  have hq := (rowDataToRightFiber ends m j k l zero e).2
  change (∃ X Y : Finset I,
      X ⊆ middleMask m c ∧
        Y ⊆ outerMask m c ∧
        sources ends X = {k, l} ∧
        sources ends Y = ∅ ∧
        BalancedRepairAdmissible ends m X k zero c Y ∧
        balancedSwap m X Y c = q) ↔
    fourColorMaskProfile m c = fourColorMaskProfile m q
  constructor
  · rintro ⟨X, Y, -, -, -, -, -, hswap⟩
    calc
      fourColorMaskProfile m c =
          fourColorMaskProfile m (balancedSwap m X Y c) :=
        (fourColorMaskProfile_balancedSwap m X Y c).symm
      _ = fourColorMaskProfile m q := congrArg _ hswap
  · intro hprofile
    have hrepair := left_right_sameMasks_admissible hc hq
      (congrArg Prod.fst hprofile) (congrArg Prod.snd hprofile)
    exact ⟨balancedMiddleDifference m c q,
      balancedOuterDifference m c q,
      hrepair.1, hrepair.2.1, hrepair.2.2.1, hrepair.2.2.2.1,
      hrepair.2.2.2.2.1, hrepair.2.2.2.2.2⟩



noncomputable def canonicalRightRowData
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (d : leftRowData ends m j k l zero) :
    rightRowData ends m j k l zero := by
  let c := rowDataToLeftFiber ends m j k l zero d
  let X := canonicalMiddleTransfer ends m c.1 k zero
  let Y := canonicalOuterTransfer ends m c.1 k zero
  let q := balancedSwap m X Y c.1
  have hv := canonicalTransfers_valid hloop hjk hkl c.2
  have hdisc := canonicalBalancedSwap_disconnects
    hloop hjk hkl hk0 c.2
  have hq : RightPattern ends m {j, k} {k, l} k zero q :=
    rightPattern_of_balancedTransfer c.2 hv.1 hv.2.1
      hv.2.2.1 hv.2.2.2 hdisc
  exact rightFiberToRowData ends m j k l zero ⟨q, hq⟩



theorem canonicalRightRowData_mem_admissibleRightRowRepairs
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (d : leftRowData ends m j k l zero) :
    canonicalRightRowData ends m j k l zero hloop hjk hkl hk0 d ∈
      admissibleRightRowRepairs ends m j k l zero d := by
  rw [mem_admissibleRightRowRepairs_iff,
    rowDataRepairRelated_iff_sameMask]
  let c := rowDataToLeftFiber ends m j k l zero d
  let X := canonicalMiddleTransfer ends m c.1 k zero
  let Y := canonicalOuterTransfer ends m c.1 k zero
  let q := balancedSwap m X Y c.1
  have hv := canonicalTransfers_valid hloop hjk hkl c.2
  have hdisc := canonicalBalancedSwap_disconnects
    hloop hjk hkl hk0 c.2
  have hq : RightPattern ends m {j, k} {k, l} k zero q :=
    rightPattern_of_balancedTransfer c.2 hv.1 hv.2.1
      hv.2.2.1 hv.2.2.2 hdisc
  change fourColorMaskProfile m c.1 =
    fourColorMaskProfile m
      (rowDataToRightFiber ends m j k l zero
        (rightFiberToRowData ends m j k l zero ⟨q, hq⟩)).1
  rw [rowDataToRightFiber_leftInverse]
  exact (fourColorMaskProfile_balancedSwap m X Y c.1).symm



noncomputable def admissibleRightRowNeighborhood
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (S : Finset (leftRowData ends m j k l zero)) :
    Finset (rightRowData ends m j k l zero) := by
  classical
  exact Finset.univ.filter fun e =>
    ∃ d ∈ S, RowDataRepairRelated ends m j k l zero d e

@[simp] theorem mem_admissibleRightRowNeighborhood_iff
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (S : Finset (leftRowData ends m j k l zero))
    (e : rightRowData ends m j k l zero) :
    e ∈ admissibleRightRowNeighborhood ends m j k l zero S ↔
      ∃ d ∈ S, RowDataRepairRelated ends m j k l zero d e := by
  classical
  simp [admissibleRightRowNeighborhood]


def RowDataRepairHall
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W) : Prop :=
  ∀ S : Finset (leftRowData ends m j k l zero),
    S.card ≤ (admissibleRightRowNeighborhood ends m j k l zero S).card



theorem rowDataRepairHall_of_related_embedding
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (f : leftRowData ends m j k l zero ↪
      rightRowData ends m j k l zero)
    (hrelated : ∀ d, RowDataRepairRelated ends m j k l zero d (f d)) :
    RowDataRepairHall ends m j k l zero := by
  intro S
  calc
    S.card = (S.map f).card := (Finset.card_map f).symm
    _ ≤ (admissibleRightRowNeighborhood ends m j k l zero S).card := by
      apply Finset.card_le_card
      intro e he
      rcases Finset.mem_map.mp he with ⟨d, hd, hde⟩
      rw [mem_admissibleRightRowNeighborhood_iff]
      refine ⟨d, hd, ?_⟩
      rw [← hde]
      exact hrelated d



theorem GrahamWeightedRowMinor_of_rowDataRepairHall
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hhall : RowDataRepairHall ends m j k l zero) :
    GrahamWeightedRowMinor ends m j k l zero := by
  unfold GrahamWeightedRowMinor
  rw [← leftRowData_card_eq_weightedSum,
    ← rightRowData_card_eq_weightedSum]
  rw [← Finset.card_univ, ← Finset.card_univ]
  calc
    (Finset.univ : Finset (leftRowData ends m j k l zero)).card ≤
        (admissibleRightRowNeighborhood ends m j k l zero Finset.univ).card :=
      hhall Finset.univ
    _ ≤ (Finset.univ : Finset (rightRowData ends m j k l zero)).card :=
      Finset.card_le_card (Finset.subset_univ _)

end StatMech.GrahamGHS.FourColor
