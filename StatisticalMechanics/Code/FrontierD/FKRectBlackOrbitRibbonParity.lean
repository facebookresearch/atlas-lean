/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonEmbedding



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section



def fkRectBlackOrbitMedialRibbonIndexEquiv
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length ≃
      Fin (fkRectBlackOrbitList
        (fkRectConfigurationToMedialPairing R omega) d).length × Fin 8 :=
  (finCongr (by
    rw [fkRectBlackOrbitMedialRibbonWord_length]
    omega)).trans finProdFinEquiv.symm


def fkRectBlackOrbitMedialRibbonFlatSite
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length) :
    ZMod (8 * R.medialTorus.width) ×
      ZMod (8 * R.medialTorus.height) :=
  fkRectBlackOrbitMedialRibbonIndexedSite R omega d
    (fkRectBlackOrbitMedialRibbonIndexEquiv R omega d k)

theorem fkRectBlackOrbitMedialRibbonFlatSite_injective
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Function.Injective
      (fkRectBlackOrbitMedialRibbonFlatSite R omega d) :=
  (fkRectBlackOrbitMedialRibbonIndexedSite_injective R omega d).comp
    (fkRectBlackOrbitMedialRibbonIndexEquiv R omega d).injective

instance fkRectBlackOrbitMedialRibbonWord_length_neZero
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    NeZero (fkRectBlackOrbitMedialRibbonWord R omega d).length :=
  ⟨(List.length_pos_iff_ne_nil.mpr
    (fkRectBlackOrbitMedialRibbonWord_nonempty R omega d)).ne'⟩

def fkRectRibbonIndexSucc {n : ℕ} (hn : 0 < n)
    (z : Fin n × Fin 8) : Fin n × Fin 8 :=
  letI : NeZero n := ⟨hn.ne'⟩
  (if z.2 = Fin.last 7 then z.1 + 1 else z.1, z.2 + 1)

def fkRectBlackOrbitMedialRibbonIndexedDirection
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z : Fin (fkRectBlackOrbitList
        (fkRectConfigurationToMedialPairing R omega) d).length × Fin 8) :
    Fin 4 :=
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  fkRectMedialRibbonBlockDirection
    (pairing (l.get z.1).1.1) (l.get z.1).1.2 z.2

def fkRectRibbonRectStep (width height : ℕ) (mu : Fin 4)
    (p : ZMod width × ZMod height) : ZMod width × ZMod height :=
  match mu with
  | 0 => (p.1 + 1, p.2)
  | 1 => (p.1, p.2 + 1)
  | 2 => (p.1 - 1, p.2)
  | 3 => (p.1, p.2 - 1)

@[simp] theorem fkRectMedialRibbonBlockOffset_zero
    (pairing : Bool) (side : FKMedialSide) :
    fkRectMedialRibbonBlockOffset pairing side 0 =
      fkRectMedialRibbonPortOffset side := by
  cases pairing <;> cases side <;> decide

@[simp] theorem fkRectRibbon_scaled_succ
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    ((((8 * (finitePeriodicSucc hM i).val : Nat) : Int)) :
        ZMod (8 * M)) =
      (((8 * i.val : Nat) : Int) + 8 : ZMod (8 * M)) := by
  have h := fkRectRibbonCellResidueEmbed_normalize hM i 8
  rw [fkRectRibbonNormalizeCell_eight] at h
  simpa [fkRectRibbonCellResidueEmbed] using h

@[simp] theorem fkRectRibbon_scaled_pred
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    ((((8 * (SixVertexArrows.cyclicPred hM i).val : Nat) : Int)) :
        ZMod (8 * M)) =
      (((8 * i.val : Nat) : Int) - 8 : ZMod (8 * M)) := by
  have h := fkRectRibbon_scaled_succ hM
    (SixVertexArrows.cyclicPred hM i)
  rw [finitePeriodicSucc_cyclicPred] at h
  rw [h]
  ring

@[simp] theorem fkRectRibbon_scaled_succ_mul
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    ((8 : ZMod (8 * M)) * (finitePeriodicSucc hM i).val) =
      8 * (i.val : ZMod (8 * M)) + 8 := by
  simpa [Nat.cast_mul] using fkRectRibbon_scaled_succ hM i

@[simp] theorem fkRectRibbon_scaled_pred_mul
    {M : ℕ} (hM : 0 < M) (i : Fin M) :
    ((8 : ZMod (8 * M)) *
        (SixVertexArrows.cyclicPred hM i).val) =
      8 * (i.val : ZMod (8 * M)) - 8 := by
  simpa [Nat.cast_mul] using fkRectRibbon_scaled_pred hM i

theorem fkRectMedialRibbonBlockSite_slot_succ
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : FKMedialBlackDart R.medialTorus) (t : Fin 8)
    (ht : t ≠ Fin.last 7) :
    fkRectMedialRibbonBlockSite R pairing e (t + 1) =
      fkRectRibbonRectStep (8 * R.medialTorus.width)
        (8 * R.medialTorus.height)
        (fkRectMedialRibbonBlockDirection
          (pairing e.1.1) e.1.2 t)
        (fkRectMedialRibbonBlockSite R pairing e t) := by
  rcases e with ⟨⟨⟨x, y⟩, side⟩, hd⟩
  cases hp : pairing (x, y) <;> cases side <;> fin_cases t <;>
    simp_all [fkRectMedialRibbonBlockSite,
      fkRectMedialRibbonBlockOffset_eq_table,
      fkRectMedialRibbonBlockOffsetTable,
      fkRectMedialRibbonBlockDirection,
      fkRectMedialRibbonBlock, fkRectMedialRibbonLocalBlock,
      fkRectMedialRibbonPortOffset,
      fkRectMedialSideDirection, fkRectMedialLocalMateSide,
      fkRectRibbonRectStep] <;> ring

theorem fkRectMedialRibbonBlockSite_wrap
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : FKMedialBlackDart R.medialTorus) :
    fkRectMedialRibbonBlockSite R pairing
        (fkMedialBlackBoundaryPerm pairing e) 0 =
      fkRectRibbonRectStep (8 * R.medialTorus.width)
        (8 * R.medialTorus.height)
        (fkRectMedialRibbonBlockDirection
          (pairing e.1.1) e.1.2 (Fin.last 7))
        (fkRectMedialRibbonBlockSite R pairing e (Fin.last 7)) := by
  rcases e with ⟨⟨⟨x, y⟩, side⟩, hd⟩
  cases hp : pairing (x, y) <;> cases side <;>
    simp_all [fkRectMedialRibbonBlockSite,
      fkRectMedialRibbonBlockOffset_eq_table,
      fkRectMedialRibbonBlockOffsetTable,
      fkRectMedialRibbonBlockDirection,
      fkRectMedialRibbonBlock, fkRectMedialRibbonLocalBlock,
      fkRectMedialRibbonPortOffset,
      fkRectMedialSideDirection, fkRectMedialLocalMateSide,
      fkRectMedialRibbonBlockOffset_zero,
      fkRectRibbonRectStep, fkMedialBlackBoundaryPerm_val,
      fkMedialLocalMate, fkMedialBondMate] <;> ring

theorem fkRectBlackOrbitMedialRibbonIndexedSite_succ
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z : Fin (fkRectBlackOrbitList
        (fkRectConfigurationToMedialPairing R omega) d).length × Fin 8) :
    fkRectBlackOrbitMedialRibbonIndexedSite R omega d
        (fkRectRibbonIndexSucc
          (fkRectBlackOrbitList_length_pos
            (fkRectConfigurationToMedialPairing R omega) d) z) =
      fkRectRibbonRectStep (8 * R.medialTorus.width)
        (8 * R.medialTorus.height)
        (fkRectBlackOrbitMedialRibbonIndexedDirection R omega d z)
        (fkRectBlackOrbitMedialRibbonIndexedSite R omega d z) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  have hn : 0 < l.length := fkRectBlackOrbitList_length_pos pairing d
  letI : NeZero l.length := ⟨hn.ne'⟩
  rcases z with ⟨i, t⟩
  have hnext : l.get (i + 1) =
      fkMedialBlackBoundaryPerm pairing (l.get i) :=
    fkRectBlackOrbitList_get_add_one pairing d i
  by_cases ht : t = Fin.last 7
  · subst t
    simp only [fkRectRibbonIndexSucc, if_pos rfl, Fin.last_add_one]
    change fkRectMedialRibbonBlockSite R pairing (l.get (i + 1)) 0 = _
    rw [hnext]
    exact fkRectMedialRibbonBlockSite_wrap R pairing (l.get i)
  · simp only [fkRectRibbonIndexSucc, if_neg ht]
    exact fkRectMedialRibbonBlockSite_slot_succ R pairing (l.get i) t ht









































































































































































































































































































































end

end StatMech.FrontierD


























































































































































































































































































































































































































































