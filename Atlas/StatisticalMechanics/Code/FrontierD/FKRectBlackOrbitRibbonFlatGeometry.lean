/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonParity



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section

def fkRectBlackOrbitMedialRibbonFlatDirection
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length) : Fin 4 :=
  fkRectBlackOrbitMedialRibbonIndexedDirection R omega d
    (fkRectBlackOrbitMedialRibbonIndexEquiv R omega d k)

theorem fkRectList_get_flatMap_eight
    {α β : Type} (l : List α) (f : α → List β)
    (hlen : ∀ a, (f a).length = 8)
    (i : Fin l.length) (t : Fin 8) :
    (l.flatMap f).get
        ⟨t.val + 8 * i.val, by
          rw [List.length_flatMap]
          simp [hlen]
          omega⟩ =
      (f (l.get i)).get ⟨t.val, by simpa [hlen] using t.isLt⟩ := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons a l ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [List.get_eq_getElem, hlen]
      · have hidx : t.val + 8 * j.succ.val < (f a ++ l.flatMap f).length := by
          simp [List.length_flatMap, hlen]
          omega
        change (f a ++ l.flatMap f)[t.val + 8 * j.succ.val]'hidx =
          (f (l.get j)).get ⟨t.val, by simpa [hlen] using t.isLt⟩
        rw [List.getElem_append_right (by simp [hlen]; omega)]
        have hindex : t.val + 8 * j.succ.val - (f a).length =
            t.val + 8 * j.val := by
          rw [hlen]
          simp only [Fin.val_succ]
          omega
        simpa only [hindex] using ih j

set_option maxHeartbeats 500000 in

theorem fkRectBlackOrbitMedialRibbonFlatDirection_eq_get
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length) :
    fkRectBlackOrbitMedialRibbonFlatDirection R omega d k =
      (fkRectBlackOrbitMedialRibbonWord R omega d).get k := by
  let E := fkRectBlackOrbitMedialRibbonIndexEquiv R omega d
  obtain ⟨⟨i, t⟩, rfl⟩ := E.symm.surjective k
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  let f : FKMedialBlackDart R.medialTorus → List (Fin 4) := fun e =>
    fkRectMedialRibbonBlock (pairing e.1.1) e.1.2
  let u : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length :=
    ⟨t.val + 8 * i.val, by
      rw [fkRectBlackOrbitMedialRibbonWord_length]
      omega⟩
  have hu : E.symm (i, t) = u := by
    apply Fin.ext
    simp [E, u, fkRectBlackOrbitMedialRibbonIndexEquiv,
      finProdFinEquiv]
  have hget := fkRectList_get_flatMap_eight l f
    (fun e => fkRectMedialRibbonBlock_length (pairing e.1.1) e.1.2) i t
  change fkRectBlackOrbitMedialRibbonIndexedDirection R omega d
      (E (E.symm (i, t))) = _
  rw [E.apply_symm_apply, hu]
  change fkRectMedialRibbonBlockDirection
      (pairing (l.get i).1.1) (l.get i).1.2 t =
    (l.flatMap f).get u
  exact hget.symm

theorem finCongr_add_one
    {n m : ℕ} [NeZero n] [NeZero m] (h : n = m)
    (k : Fin n) :
    finCongr h (k + 1) = finCongr h k + 1 := by
  subst m
  apply Fin.ext
  simp [Fin.add_def]

theorem finProdFinEquiv_ribbonIndexSucc
    {n : ℕ} [NeZero n] (hn : 0 < n) (z : Fin n × Fin 8) :
    finProdFinEquiv (fkRectRibbonIndexSucc hn z) =
      finProdFinEquiv z + 1 := by
  rcases z with ⟨i, t⟩
  by_cases ht : t = Fin.last 7
  · subst t
    apply Fin.ext
    norm_num [fkRectRibbonIndexSucc, finProdFinEquiv, Fin.add_def]
    rw [show 7 + 8 * i.val + 1 = 8 * (i.val + 1) by omega,
      Nat.mul_comm n 8, Nat.mul_mod_mul_left]
  · have htval : t.val < 7 := by
      have hle : t.val ≤ 7 := by omega
      exact lt_of_le_of_ne hle fun h => ht (Fin.ext h)
    apply Fin.ext
    simp only [fkRectRibbonIndexSucc, if_neg ht, finProdFinEquiv,
      Equiv.coe_fn_mk, Fin.val_mk, Fin.add_def]
    have hlt : t.val + 8 * i.val + 1 < n * 8 := by omega
    norm_num
    rw [Nat.mod_eq_of_lt (by omega : t.val + 1 < 8),
      Nat.mod_eq_of_lt hlt]
    omega

set_option maxHeartbeats 1000000 in

theorem fkRectBlackOrbitMedialRibbonIndexEquiv_add_one
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length) :
    fkRectBlackOrbitMedialRibbonIndexEquiv R omega d (k + 1) =
      fkRectRibbonIndexSucc
        (fkRectBlackOrbitList_length_pos
          (fkRectConfigurationToMedialPairing R omega) d)
        (fkRectBlackOrbitMedialRibbonIndexEquiv R omega d k) := by
  let E := fkRectBlackOrbitMedialRibbonIndexEquiv R omega d
  obtain ⟨⟨i, t⟩, rfl⟩ := E.symm.surjective k
  apply E.symm.injective
  simp only [E, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  let l := fkRectBlackOrbitList
    (fkRectConfigurationToMedialPairing R omega) d
  have hn : 0 < l.length := fkRectBlackOrbitList_length_pos _ d
  letI : NeZero l.length := ⟨hn.ne'⟩
  have hw : 0 < (fkRectBlackOrbitMedialRibbonWord R omega d).length :=
    List.length_pos_iff_ne_nil.mpr
      (fkRectBlackOrbitMedialRibbonWord_nonempty R omega d)
  have hlen : (fkRectBlackOrbitMedialRibbonWord R omega d).length =
      l.length * 8 := by
    dsimp only [l]
    rw [fkRectBlackOrbitMedialRibbonWord_length]
    omega
  change (fkRectBlackOrbitMedialRibbonIndexEquiv R omega d).symm
      (i, t) + 1 =
    (fkRectBlackOrbitMedialRibbonIndexEquiv R omega d).symm
      (fkRectRibbonIndexSucc hn (i, t))
  unfold fkRectBlackOrbitMedialRibbonIndexEquiv
  change (finCongr hlen).symm (finProdFinEquiv (i, t)) + 1 =
    (finCongr hlen).symm
      (finProdFinEquiv (fkRectRibbonIndexSucc hn (i, t)))
  rw [finProdFinEquiv_ribbonIndexSucc hn]
  exact (finCongr_add_one hlen.symm _).symm

theorem fkRectBlackOrbitMedialRibbonFlatSite_succ
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length) :
    fkRectBlackOrbitMedialRibbonFlatSite R omega d (k + 1) =
      fkRectRibbonRectStep (8 * R.medialTorus.width)
        (8 * R.medialTorus.height)
        (fkRectBlackOrbitMedialRibbonFlatDirection R omega d k)
        (fkRectBlackOrbitMedialRibbonFlatSite R omega d k) := by
  rw [fkRectBlackOrbitMedialRibbonFlatSite,
    fkRectBlackOrbitMedialRibbonIndexEquiv_add_one]
  exact fkRectBlackOrbitMedialRibbonIndexedSite_succ R omega d _

theorem fkRectRibbonRectStep_opposite
    (width height : ℕ) (mu : Fin 4) (p : ZMod width × ZMod height) :
    fkRectRibbonRectStep width height (mu + 2)
        (fkRectRibbonRectStep width height mu p) = p := by
  fin_cases mu <;> simp [fkRectRibbonRectStep]

theorem fkRectBlackOrbitMedialRibbonWord_length_gt_two
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    2 < (fkRectBlackOrbitMedialRibbonWord R omega d).length := by
  rw [fkRectBlackOrbitMedialRibbonWord_length]
  have h := fkRectBlackOrbitList_length_pos
    (fkRectConfigurationToMedialPairing R omega) d
  omega

set_option maxHeartbeats 500000 in

theorem fkRectBlackOrbitMedialRibbonFlatDirection_nonUturn
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) (k :
      Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length) :
    fkRectBlackOrbitMedialRibbonFlatDirection R omega d (k + 1) ≠
      fkRectBlackOrbitMedialRibbonFlatDirection R omega d k + 2 := by
  intro hdir
  have hstep0 := fkRectBlackOrbitMedialRibbonFlatSite_succ R omega d k
  have hstep1 := fkRectBlackOrbitMedialRibbonFlatSite_succ R omega d (k + 1)
  rw [hdir, hstep0, fkRectRibbonRectStep_opposite] at hstep1
  have hsite : fkRectBlackOrbitMedialRibbonFlatSite R omega d (k + 1 + 1) =
      fkRectBlackOrbitMedialRibbonFlatSite R omega d k := hstep1
  have hindex : k + 1 + 1 = k :=
    fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d hsite
  have hlen := fkRectBlackOrbitMedialRibbonWord_length_gt_two R omega d
  have hcancel : k + (1 + 1) = k + 0 := by
    simpa [add_assoc] using hindex
  have hone : (1 + 1 : Fin
      (fkRectBlackOrbitMedialRibbonWord R omega d).length) = 0 :=
    add_left_cancel hcancel
  have hval := congrArg Fin.val hone
  change ((1 % (fkRectBlackOrbitMedialRibbonWord R omega d).length) +
      (1 % (fkRectBlackOrbitMedialRibbonWord R omega d).length)) %
      (fkRectBlackOrbitMedialRibbonWord R omega d).length = 0 at hval
  norm_num at hval
  have horbit := fkRectBlackOrbitList_length_pos
    (fkRectConfigurationToMedialPairing R omega) d
  rw [Nat.mod_eq_of_lt (by omega)] at hval
  omega

end

end StatMech.FrontierD
