/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitWindingGeometry



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section



def fkRectRibbonCellResidueEmbed (M : ℕ)
    (z : Fin M × Fin 8) : ZMod (8 * M) :=
  (8 * z.1.val + z.2.val : ℕ)

theorem fkRectRibbonCellResidueEmbed_injective
    (M : ℕ) (_hM : 0 < M) :
    Function.Injective (fkRectRibbonCellResidueEmbed M) := by
  rintro ⟨i, r⟩ ⟨j, s⟩ h
  have hval := congrArg (fun z : ZMod (8 * M) => z.val) h
  simp only [fkRectRibbonCellResidueEmbed, ZMod.val_natCast] at hval
  have hi : 8 * i.val + r.val < 8 * M := by omega
  have hj : 8 * j.val + s.val < 8 * M := by omega
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hval
  have hij : i.val = j.val := by omega
  have hrs : r.val = s.val := by omega
  exact Prod.ext (Fin.ext hij) (Fin.ext hrs)

def fkRectRibbonNormalizeCell {M : ℕ} (hM : 0 < M)
    (i : Fin M) (o : Int) : Fin M × Fin 8 :=
  (fkRectIntModFin hM ((i.val : Int) + o / 8),
    fkRectIntModFin (by decide) o)

theorem fkRectRibbonCellResidueEmbed_normalize
    {M : ℕ} (hM : 0 < M) (i : Fin M) (o : Int) :
    fkRectRibbonCellResidueEmbed M
        (fkRectRibbonNormalizeCell hM i o) =
      (((8 * i.val : Nat) : Int) + o : ZMod (8 * M)) := by
  let z : Int := (i.val : Int) + o / 8
  have hM0 : (M : Int) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  have h80 : (8 : Int) ≠ 0 := by norm_num
  have hrM : ((z.natMod M : Nat) : Int) = z % (M : Int) := by
    unfold Int.natMod
    rw [Int.toNat_of_nonneg (Int.emod_nonneg z hM0)]
  have hr8 : ((o.natMod 8 : Nat) : Int) = o % 8 := by
    unfold Int.natMod
    rw [Int.toNat_of_nonneg (Int.emod_nonneg o h80)]
  simp only [fkRectRibbonCellResidueEmbed, fkRectRibbonNormalizeCell]
  rw [← Int.cast_natCast]
  rw [← Int.cast_add]
  change (((8 * (fkRectIntModFin hM
      ((i.val : Int) + o / 8)).val +
      (fkRectIntModFin (show 0 < 8 by decide) o).val : Nat) : Int) :
        ZMod (8 * M)) = _
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
  refine ⟨z / (M : Int), ?_⟩
  simp only [fkRectIntModFin, Fin.val_mk]
  dsimp only [z] at hrM
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [hrM, hr8]
  have hz := Int.emod_add_ediv z (M : Int)
  have ho := Int.emod_add_ediv o 8
  dsimp only [z] at hz ⊢
  linear_combination -8 * hz - ho

@[simp] theorem fkRectRibbonNormalizeCell_slot
    {M : ℕ} (hM : 0 < M) (i : Fin M) (r : Fin 8) :
    fkRectRibbonNormalizeCell hM i (r.val : Int) = (i, r) := by
  fin_cases r <;>
    apply Prod.ext <;>
    apply Fin.ext <;>
    simp [fkRectRibbonNormalizeCell, fkRectIntModFin, Int.natMod,
      Int.emod_eq_of_lt, i.isLt]

@[simp] theorem fkRectRibbonNormalizeCell_slot_add_eight
    {M : ℕ} (hM : 0 < M) (i : Fin M) (r : Fin 8) :
    fkRectRibbonNormalizeCell hM i (8 + r.val : Int) =
      (finitePeriodicSucc hM i, r) := by
  have hdiv : (8 + (r.val : Int)) / 8 = 1 := by
    omega
  apply Prod.ext
  · apply Fin.ext
    simp only [fkRectRibbonNormalizeCell, hdiv, Int.reduceAdd, Prod.fst]
    simp only [fkRectIntModFin, Fin.val_mk, Int.natMod,
      finitePeriodicSucc]
    rw [Int.toNat_emod (by omega) (by omega)]
    norm_num
  · fin_cases r <;>
      apply Fin.ext <;>
      norm_num [fkRectRibbonNormalizeCell, fkRectIntModFin, Int.natMod,
        Int.toNat]

@[simp] theorem fkRectRibbonNormalizeCell_neg_one
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i (-1) =
      (SixVertexArrows.cyclicPred hM i, (7 : Fin 8)) := by
  apply Prod.ext
  · exact congrArg id (fkRectIntModFin_natCast_sub_one hM i)
  · apply Fin.ext
    norm_num [fkRectRibbonNormalizeCell, fkRectIntModFin, Int.natMod,
      Int.toNat]

@[simp] theorem fkRectRibbonNormalizeCell_zero
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 0 = (i, (0 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (0 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_one
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 1 = (i, (1 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (1 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_two
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 2 = (i, (2 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (2 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_three
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 3 = (i, (3 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (3 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_four
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 4 = (i, (4 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (4 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_five
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 5 = (i, (5 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (5 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_six
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 6 = (i, (6 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (6 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_seven
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 7 = (i, (7 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot hM i (7 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_eight
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 8 =
      (finitePeriodicSucc hM i, (0 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot_add_eight hM i (0 : Fin 8)

@[simp] theorem fkRectRibbonNormalizeCell_nine
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    fkRectRibbonNormalizeCell hM i 9 =
      (finitePeriodicSucc hM i, (1 : Fin 8)) := by
  simpa using fkRectRibbonNormalizeCell_slot_add_eight hM i (1 : Fin 8)


def fkRectMedialRibbonBlockDirection
    (pairing : Bool) (side : FKMedialSide) (t : Fin 8) : Fin 4 := by
  let block := fkRectMedialRibbonBlock pairing side
  have hlen : block.length = 8 :=
    fkRectMedialRibbonBlock_length pairing side
  exact block.get ⟨t.val, by simpa [hlen] using t.isLt⟩



def fkRectMedialRibbonBlockOffset
    (pairing : Bool) (side : FKMedialSide) (t : Fin 8) : Int × Int :=
  fkRectMedialRibbonPortOffset side +
    pos (fkRectMedialRibbonBlockDirection pairing side) t

def fkRectMedialRibbonBlockOffsetTable
    (pairing : Bool) (side : FKMedialSide) : Fin 8 → Int × Int :=
  match pairing, side with
  | false, .west => ![(2, 4), (2, 5), (2, 6), (3, 6),
      (4, 6), (4, 7), (4, 8), (4, 9)]
  | false, .east => ![(6, 4), (6, 3), (6, 2), (5, 2),
      (4, 2), (4, 1), (4, 0), (4, -1)]
  | false, .south => ![(4, 2), (5, 2), (6, 2), (6, 3),
      (6, 4), (7, 4), (8, 4), (9, 4)]
  | false, .north => ![(4, 6), (3, 6), (2, 6), (2, 5),
      (2, 4), (1, 4), (0, 4), (-1, 4)]
  | true, .west => ![(2, 4), (2, 3), (2, 2), (3, 2),
      (4, 2), (4, 1), (4, 0), (4, -1)]
  | true, .east => ![(6, 4), (6, 5), (6, 6), (5, 6),
      (4, 6), (4, 7), (4, 8), (4, 9)]
  | true, .south => ![(4, 2), (3, 2), (2, 2), (2, 3),
      (2, 4), (1, 4), (0, 4), (-1, 4)]
  | true, .north => ![(4, 6), (5, 6), (6, 6), (6, 5),
      (6, 4), (7, 4), (8, 4), (9, 4)]

theorem fkRectMedialRibbonBlockOffset_eq_table
    (pairing : Bool) (side : FKMedialSide) :
    fkRectMedialRibbonBlockOffset pairing side =
      fkRectMedialRibbonBlockOffsetTable pairing side := by
  funext t
  cases pairing <;> cases side <;> fin_cases t <;>
    decide



def fkRectMedialRibbonBlockSite
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) (t : Fin 8) :
    ZMod (8 * R.medialTorus.width) ×
      ZMod (8 * R.medialTorus.height) :=
  let o := fkRectMedialRibbonBlockOffset (pairing d.1.1) d.1.2 t
  (((8 * d.1.1.1.val : Nat) : Int) + o.1,
    ((8 * d.1.1.2.val : Nat) : Int) + o.2)


def fkRectMedialRibbonBlockCode
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) (t : Fin 8) :
    (Fin R.medialTorus.width × Fin 8) ×
      (Fin R.medialTorus.height × Fin 8) :=
  let o := fkRectMedialRibbonBlockOffset (pairing d.1.1) d.1.2 t
  (fkRectRibbonNormalizeCell R.medialTorus.width_pos d.1.1.1 o.1,
    fkRectRibbonNormalizeCell R.medialTorus.height_pos d.1.1.2 o.2)

theorem fkRectMedialRibbonBlockCode_embed
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) (t : Fin 8) :
    (fkRectRibbonCellResidueEmbed R.medialTorus.width
        (fkRectMedialRibbonBlockCode R pairing d t).1,
      fkRectRibbonCellResidueEmbed R.medialTorus.height
        (fkRectMedialRibbonBlockCode R pairing d t).2) =
      fkRectMedialRibbonBlockSite R pairing d t := by
  simp only [fkRectMedialRibbonBlockCode, fkRectMedialRibbonBlockSite]
  let o := fkRectMedialRibbonBlockOffset (pairing d.1.1) d.1.2 t
  change
    (fkRectRibbonCellResidueEmbed R.medialTorus.width
        (fkRectRibbonNormalizeCell R.medialTorus.width_pos d.1.1.1 o.1),
      fkRectRibbonCellResidueEmbed R.medialTorus.height
        (fkRectRibbonNormalizeCell R.medialTorus.height_pos d.1.1.2 o.2)) = _
  rw [fkRectRibbonCellResidueEmbed_normalize,
    fkRectRibbonCellResidueEmbed_normalize]

private theorem finitePeriodicSucc_injective {N : Nat} (hN : 0 < N) :
    Function.Injective (finitePeriodicSucc hN) := by
  intro i j h
  simpa only [svCyclicPred_finitePeriodicSucc] using
    congrArg (SixVertexArrows.cyclicPred hN) h

private theorem cyclicPred_injective {N : Nat} (hN : 0 < N) :
    Function.Injective (SixVertexArrows.cyclicPred hN) := by
  intro i j h
  simpa only [finitePeriodicSucc_cyclicPred] using
    congrArg (finitePeriodicSucc hN) h

@[simp] private theorem finitePeriodicSucc_inj_iff
    {N : Nat} (hN : 0 < N) (i j : Fin N) :
    finitePeriodicSucc hN i = finitePeriodicSucc hN j ↔ i = j :=
  (finitePeriodicSucc_injective hN).eq_iff

@[simp] private theorem cyclicPred_inj_iff
    {N : Nat} (hN : 0 < N) (i j : Fin N) :
    SixVertexArrows.cyclicPred hN i =
      SixVertexArrows.cyclicPred hN j ↔ i = j :=
  (cyclicPred_injective hN).eq_iff

set_option maxHeartbeats 2000000 in




theorem fkRectMedialRibbonBlockCode_injective
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus) :
    Function.Injective (fun z :
        FKMedialBlackDart R.medialTorus × Fin 8 =>
      fkRectMedialRibbonBlockCode R pairing z.1 z.2) := by
  rintro ⟨⟨⟨⟨i, j⟩, s⟩, hs⟩, t⟩
    ⟨⟨⟨⟨k, l⟩, q⟩, hq⟩, u⟩ h
  cases hp : pairing (i, j)
  · cases hr : pairing (k, l)
    · cases s <;> cases q
      all_goals fin_cases t <;> fin_cases u <;>
        simp_all [fkRectMedialRibbonBlockCode,
          fkRectMedialRibbonBlockOffset_eq_table,
          fkRectMedialRibbonBlockOffsetTable,
          fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical]
      all_goals
        rcases h with ⟨rfl, rfl⟩
        simp [fkMedialCheckerColor, fkMedialSideVertical] at hs hq <;>
          simp_all

    · cases s <;> cases q
      all_goals fin_cases t <;> fin_cases u <;>
        simp_all [fkRectMedialRibbonBlockCode,
          fkRectMedialRibbonBlockOffset_eq_table,
          fkRectMedialRibbonBlockOffsetTable,
          fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical]
      all_goals
        rcases h with ⟨rfl, rfl⟩
        simp [fkMedialCheckerColor, fkMedialSideVertical] at hs hq <;>
          simp_all

  · cases hr : pairing (k, l)
    · cases s <;> cases q
      all_goals fin_cases t <;> fin_cases u <;>
        simp_all [fkRectMedialRibbonBlockCode,
          fkRectMedialRibbonBlockOffset_eq_table,
          fkRectMedialRibbonBlockOffsetTable,
          fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical]
      all_goals
        rcases h with ⟨rfl, rfl⟩
        simp [fkMedialCheckerColor, fkMedialSideVertical] at hs hq <;>
          simp_all
    · cases s <;> cases q
      all_goals fin_cases t <;> fin_cases u <;>
        simp_all [fkRectMedialRibbonBlockCode,
          fkRectMedialRibbonBlockOffset_eq_table,
          fkRectMedialRibbonBlockOffsetTable,
          fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical]
      all_goals
        rcases h with ⟨rfl, rfl⟩
        simp [fkMedialCheckerColor, fkMedialSideVertical] at hs hq <;>
          simp_all

theorem fkRectMedialRibbonBlockSite_injective
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus) :
    Function.Injective (fun z :
        FKMedialBlackDart R.medialTorus × Fin 8 =>
      fkRectMedialRibbonBlockSite R pairing z.1 z.2) := by
  intro z w h
  apply fkRectMedialRibbonBlockCode_injective R pairing
  let E := fun c :
      (Fin R.medialTorus.width × Fin 8) ×
        (Fin R.medialTorus.height × Fin 8) =>
    (fkRectRibbonCellResidueEmbed R.medialTorus.width c.1,
      fkRectRibbonCellResidueEmbed R.medialTorus.height c.2)
  have hz : E (fkRectMedialRibbonBlockCode R pairing z.1 z.2) =
      fkRectMedialRibbonBlockSite R pairing z.1 z.2 :=
    fkRectMedialRibbonBlockCode_embed R pairing z.1 z.2
  have hw : E (fkRectMedialRibbonBlockCode R pairing w.1 w.2) =
      fkRectMedialRibbonBlockSite R pairing w.1 w.2 :=
    fkRectMedialRibbonBlockCode_embed R pairing w.1 w.2
  have he : E (fkRectMedialRibbonBlockCode R pairing z.1 z.2) =
      E (fkRectMedialRibbonBlockCode R pairing w.1 w.2) :=
    hz.trans (h.trans hw.symm)
  apply Prod.ext
  · apply fkRectRibbonCellResidueEmbed_injective _
      R.medialTorus.width_pos
    exact congrArg Prod.fst he
  · apply fkRectRibbonCellResidueEmbed_injective _
      R.medialTorus.height_pos
    exact congrArg Prod.snd he



def fkRectBlackOrbitMedialRibbonIndexedSite
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z : Fin (fkRectBlackOrbitList
        (fkRectConfigurationToMedialPairing R omega) d).length × Fin 8) :
    ZMod (8 * R.medialTorus.width) ×
      ZMod (8 * R.medialTorus.height) :=
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  fkRectMedialRibbonBlockSite R pairing (l.get z.1) z.2

theorem fkRectBlackOrbitMedialRibbonIndexedSite_injective
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Function.Injective
      (fkRectBlackOrbitMedialRibbonIndexedSite R omega d) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  intro z w h
  have hblock : (l.get z.1, z.2) = (l.get w.1, w.2) := by
    apply fkRectMedialRibbonBlockSite_injective R pairing
    exact h
  have hdart : l.get z.1 = l.get w.1 := congrArg Prod.fst hblock
  have hslot : z.2 = w.2 := congrArg
    (fun x : FKMedialBlackDart R.medialTorus × Fin 8 => x.2) hblock
  have horbit : l.Nodup := by
    exact Equiv.Perm.nodup_toList
      (fkMedialBlackBoundaryPerm pairing) d
  exact Prod.ext (horbit.injective_get hdart) hslot

@[simp] theorem fkRectMedialRibbonBlockDirection_apply
    (pairing : Bool) (side : FKMedialSide) (t : Fin 8) :
    fkRectMedialRibbonBlockDirection pairing side t =
      (fkRectMedialRibbonBlock pairing side).get
        ⟨t.val, by
          simpa only [fkRectMedialRibbonBlock_length] using t.isLt⟩ := by
  rfl

end

end StatMech.FrontierD
