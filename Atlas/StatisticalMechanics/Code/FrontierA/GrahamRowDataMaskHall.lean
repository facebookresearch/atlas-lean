/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamRowDataRepairRelation
import Code.FrontierA.GrahamFourColorMaskMatching





open Finset
open Classical

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def leftRowDataMaskSigmaEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W) :
    leftRowData ends m j k l zero ≃
      Sigma (leftMaskFiber ends m j k l zero) :=
  (leftFiberEquivRowData ends m j k l zero).symm.trans
    (Equiv.sigmaFiberEquiv
      (fun c : leftFiber ends m {j, k} {k, l} k zero =>
        fourColorMaskProfile m c.1)).symm


noncomputable def rightRowDataMaskSigmaEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W) :
    Sigma (rightMaskFiber ends m j k l zero) ≃
      rightRowData ends m j k l zero :=
  (Equiv.sigmaFiberEquiv
      (fun c : rightFiber ends m {j, k} {k, l} k zero =>
        fourColorMaskProfile m c.1)).trans
    (rightFiberEquivRowData ends m j k l zero)


noncomputable def rowDataRepairEmbedding_of_maskFiberEmbeddings
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (f : MaskFiberEmbeddings ends m j k l zero) :
    leftRowData ends m j k l zero ↪ rightRowData ends m j k l zero where
  toFun d :=
    let c := rowDataToLeftFiber ends m j k l zero d
    let p := fourColorMaskProfile m c.1
    rightFiberToRowData ends m j k l zero (f p ⟨c, rfl⟩).1
  inj' := by
    intro d e hde
    let c := rowDataToLeftFiber ends m j k l zero d
    let q := rowDataToLeftFiber ends m j k l zero e
    let pc := fourColorMaskProfile m c.1
    let pq := fourColorMaskProfile m q.1
    let fc := f pc ⟨c, rfl⟩
    let fq := f pq ⟨q, rfl⟩
    have hright : fc.1 = fq.1 := by
      have h := congrArg (rowDataToRightFiber ends m j k l zero) hde
      simpa [c, q, pc, pq, fc, fq,
        rowDataToRightFiber_leftInverse] using h
    have hp : pc = pq := by
      calc
        pc = fourColorMaskProfile m fc.1.1 := fc.2.symm
        _ = fourColorMaskProfile m fq.1.1 :=
          congrArg (fun x : rightFiber ends m {j, k} {k, l} k zero =>
            fourColorMaskProfile m x.1) hright
        _ = pq := fq.2
    let sc : Sigma (leftMaskFiber ends m j k l zero) := ⟨pc, ⟨c, rfl⟩⟩
    let sq : Sigma (leftMaskFiber ends m j k l zero) := ⟨pq, ⟨q, rfl⟩⟩
    let sf := (Function.Embedding.refl (Finset I × Finset I)).sigmaMap f
    have hsout : sf sc = sf sq := by
      apply Sigma.subtype_ext hp
      simpa [sf, sc, sq, fc, fq] using hright
    have hsin : sc = sq := sf.injective hsout
    have hcq : c = q := congrArg
      (fun x : Sigma (leftMaskFiber ends m j k l zero) => x.2.1) hsin
    exact rowDataToLeftFiber_injective ends m j k l zero hcq



theorem rowDataRepairEmbedding_of_maskFiberEmbeddings_related
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (f : MaskFiberEmbeddings ends m j k l zero)
    (d : leftRowData ends m j k l zero) :
    RowDataRepairRelated ends m j k l zero d
      (rowDataRepairEmbedding_of_maskFiberEmbeddings
        ends m j k l zero f d) := by
  rw [rowDataRepairRelated_iff_sameMask]
  let c := rowDataToLeftFiber ends m j k l zero d
  let p := fourColorMaskProfile m c.1
  let q := f p (⟨c, rfl⟩ : leftMaskFiber ends m j k l zero p)
  change fourColorMaskProfile m c.1 =
    fourColorMaskProfile m
      (rowDataToRightFiber ends m j k l zero
        (rightFiberToRowData ends m j k l zero q.1)).1
  rw [rowDataToRightFiber_leftInverse]
  exact q.2.symm


theorem rowDataRepairHall_of_maskFiberEmbeddings
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (f : MaskFiberEmbeddings ends m j k l zero) :
    RowDataRepairHall ends m j k l zero :=
  rowDataRepairHall_of_related_embedding ends m j k l zero
    (rowDataRepairEmbedding_of_maskFiberEmbeddings ends m j k l zero f)
    (rowDataRepairEmbedding_of_maskFiberEmbeddings_related
      ends m j k l zero f)



theorem rowDataRepairHall_of_maskwise
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hmask : forall p : Finset I × Finset I,
      Fintype.card (leftMaskFiber ends m j k l zero p) <=
        Fintype.card (rightMaskFiber ends m j k l zero p)) :
    RowDataRepairHall ends m j k l zero := by
  obtain ⟨f⟩ := (nonempty_maskFiberEmbeddings_iff ends m j k l zero).2 hmask
  exact rowDataRepairHall_of_maskFiberEmbeddings ends m j k l zero f



noncomputable def maskFiberEmbeddings_of_related_injection
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (g : leftRowData ends m j k l zero ->
      rightRowData ends m j k l zero)
    (hg : Function.Injective g)
    (hrelated : forall d, RowDataRepairRelated ends m j k l zero d (g d)) :
    MaskFiberEmbeddings ends m j k l zero := by
  intro p
  refine
    { toFun := fun c => ?_
      inj' := ?_ }
  · let d := leftFiberToRowData ends m j k l zero c.1
    let q := rowDataToRightFiber ends m j k l zero (g d)
    refine ⟨q, ?_⟩
    have hmask := (rowDataRepairRelated_iff_sameMask
      ends m j k l zero d (g d)).1 (hrelated d)
    change fourColorMaskProfile m q.1 = p
    calc
      fourColorMaskProfile m q.1 =
          fourColorMaskProfile m
            (rowDataToLeftFiber ends m j k l zero d).1 := hmask.symm
      _ = fourColorMaskProfile m c.1.1 := by
        rw [rowDataToLeftFiber_leftInverse]
      _ = p := c.2
  · intro c d hcd
    apply Subtype.ext
    apply (leftFiberEquivRowData ends m j k l zero).injective
    change leftFiberToRowData ends m j k l zero c.1 =
      leftFiberToRowData ends m j k l zero d.1
    apply hg
    apply rowDataToRightFiber_injective ends m j k l zero
    have hq := congrArg (fun q => q.1.1) hcd
    dsimp only at hq
    exact Subtype.ext hq




theorem rowDataRepairHall_iff_maskwise
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W) :
    RowDataRepairHall ends m j k l zero ↔
      forall p : Finset I × Finset I,
        Fintype.card (leftMaskFiber ends m j k l zero p) <=
          Fintype.card (rightMaskFiber ends m j k l zero p) := by
  constructor
  · intro hhall
    have hhall' : forall S : Finset (leftRowData ends m j k l zero),
        S.card <= (Finset.univ.filter fun e =>
          ∃ d ∈ S, RowDataRepairRelated ends m j k l zero d e).card := by
      simpa [RowDataRepairHall, admissibleRightRowNeighborhood] using hhall
    obtain ⟨g, hg, hrelated⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective
        (RowDataRepairRelated ends m j k l zero)).1 hhall'
    let f := maskFiberEmbeddings_of_related_injection
      ends m j k l zero g hg hrelated
    intro p
    exact Fintype.card_le_of_injective (f p) (f p).injective
  · exact rowDataRepairHall_of_maskwise ends m j k l zero




theorem rowDataRepairHall_of_subsingleton_leftMaskFibers
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : forall i, i ∈ m -> ¬(ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hsub : forall p : Finset I × Finset I,
      Subsingleton (leftMaskFiber ends m j k l zero p)) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_maskFiberEmbeddings
  intro p
  by_cases hleft : Nonempty (leftMaskFiber ends m j k l zero p)
  · let c := Classical.choice hleft
    let d := Classical.choice
      (rightMaskFiber_nonempty_of_left hloop hjk hkl hk0 p c)
    letI : Subsingleton (leftMaskFiber ends m j k l zero p) := hsub p
    exact
      { toFun := fun _ => d
        inj' := fun a b _ => Subsingleton.elim a b }
  · exact
      { toFun := fun c => False.elim (hleft ⟨c⟩)
        inj' := fun a _ _ => False.elim (hleft ⟨a⟩) }



theorem rowDataRepairHall_of_subsingleton_cycleSectors
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : forall i, i ∈ m -> ¬(ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hcycle : forall p : Finset I × Finset I,
      Subsingleton (boundarySector ends p.1 ∅) ∧
        Subsingleton (boundarySector ends p.2 ∅)) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_subsingleton_leftMaskFibers
    ends m j k l zero hloop hjk hkl hk0
  intro p
  exact subsingleton_leftMaskFiber_of_cycleSectors
    ends m j k l zero p (hcycle p).1 (hcycle p).2

end StatMech.GrahamGHS.FourColor
