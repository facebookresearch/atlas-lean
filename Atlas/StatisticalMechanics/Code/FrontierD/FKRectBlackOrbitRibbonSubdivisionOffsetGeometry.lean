/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionIndexGeometry



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectRibbon_scaled_succ_general
    {M S : ℕ} (hM : 0 < M) (hS : 0 < S) (i : Fin M) :
    (((S * (finitePeriodicSucc hM i).val : Nat) : Int) : ZMod (M * S)) =
      (((S * i.val : Nat) : Int) : ZMod (M * S)) + S := by
  rw [finitePeriodicSucc_val]
  split_ifs with hi
  · simp only [Nat.mul_zero, Nat.cast_zero, Int.cast_zero]
    have heq : S * i.val + S = M * S := by
      calc
        S * i.val + S = S * (i.val + 1) := by ring
        _ = S * M := by rw [hi]
        _ = M * S := Nat.mul_comm _ _
    push_cast
    rw [show (S : ZMod (M * S)) * i.val + S =
        ((S * i.val + S : ℕ) : ZMod (M * S)) by push_cast; ring,
      heq]
    simp
  · push_cast
    ring

theorem fkRectRibbon_scaled_pred_general
    {M S : ℕ} (hM : 0 < M) (hS : 0 < S) (i : Fin M) :
    (((S * (SixVertexArrows.cyclicPred hM i).val : Nat) : Int) :
        ZMod (M * S)) =
      (((S * i.val : Nat) : Int) : ZMod (M * S)) - S := by
  have h := fkRectRibbon_scaled_succ_general hM hS
    (SixVertexArrows.cyclicPred hM i)
  rw [finitePeriodicSucc_cyclicPred] at h
  rw [h]
  ring

set_option maxHeartbeats 500000 in

theorem fkRectRibbonSubdivisionCodeEmbed_offset_succ
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (p : ZMod width × ZMod height) (mu : Fin 4)
    (r : Fin (onsAnisotropicStepScale width height mu))
    (hr : r.val + 1 < onsAnisotropicStepScale width height mu) :
    fkRectRibbonSubdivisionCodeEmbed width height
        (fkRectRibbonSubdivisionCode width height hwidth hheight p mu
          ⟨r.val + 1, hr⟩) =
      ons_dirStep (width * height) mu
        (fkRectRibbonSubdivisionCodeEmbed width height
          (fkRectRibbonSubdivisionCode width height hwidth hheight p mu r)) := by
  letI : NeZero width := ⟨hwidth.ne'⟩
  letI : NeZero height := ⟨hheight.ne'⟩
  have hxFin : fkRectZModFin hwidth p.1 =
      (⟨p.1.val, p.1.val_lt⟩ : Fin width) :=
    Fin.ext (fkRectZModFin_val hwidth p.1)
  have hyFin : fkRectZModFin hheight p.2 =
      (⟨p.2.val, p.2.val_lt⟩ : Fin height) :=
    Fin.ext (fkRectZModFin_val hheight p.2)
  have hxPred := fkRectRibbon_scaled_pred_general hwidth hheight
    (fkRectZModFin hwidth p.1)
  have hyPred := fkRectRibbon_scaled_pred_general hheight hwidth
    (fkRectZModFin hheight p.2)
  rw [Nat.mul_comm height width] at hyPred
  simp only [fkRectZModFin_val] at hxPred hyPred
  rw [hxFin] at hxPred
  rw [hyFin] at hyPred
  push_cast at hxPred hyPred
  rcases fkRectFinFour_cases mu with hmu | hmu | hmu | hmu
  all_goals subst mu
  all_goals
    simp only [onsAnisotropicStepScale_zero, onsAnisotropicStepScale_one,
      onsAnisotropicStepScale_two, onsAnisotropicStepScale_three] at hr ⊢
  all_goals norm_num [onsAnisotropicStepScale] at hr
  all_goals by_cases hr0 : r.val = 0
  all_goals simp [fkRectRibbonSubdivisionCode, fkRectRibbonSubdivisionCodeEmbed,
    fkRectRibbonBackwardCode, hr0, finProdFinEquiv, ons_dirStep,
    hxPred, hyPred, hwidth, hheight]
  all_goals try rw [hxPred]
  all_goals try rw [hyPred]
  all_goals try rw [Nat.cast_sub (by omega)]
  all_goals push_cast
  all_goals try simp only [ZMod.cast_eq_val]
  all_goals ring_nf at hxPred hyPred ⊢
  all_goals convert hyPred using 1 <;> first | rfl | ring

theorem fkRectRibbonSubdivisionCodeEmbed_offset_zero
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (p : ZMod width × ZMod height) (mu : Fin 4)
    (r : Fin (onsAnisotropicStepScale width height mu))
    (hr : r.val = 0) :
    fkRectRibbonSubdivisionCodeEmbed width height
        (fkRectRibbonSubdivisionCode width height hwidth hheight p mu r) =
      ((((height * p.1.val : Nat) : Int) : ZMod (width * height)),
        (((width * p.2.val : Nat) : Int) : ZMod (width * height))) := by
  fin_cases mu <;>
    simp [fkRectRibbonSubdivisionCode, fkRectRibbonSubdivisionCodeEmbed,
      fkRectRibbonBackwardCode, hr, finProdFinEquiv, Nat.mul_comm,
      onsAnisotropicStepScale] at *

set_option maxHeartbeats 500000 in

theorem fkRectRibbonSubdivisionCodeEmbed_offset_wrap
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (p : ZMod width × ZMod height) (mu nu : Fin 4)
    (r : Fin (onsAnisotropicStepScale width height mu))
    (hr : ¬ r.val + 1 < onsAnisotropicStepScale width height mu)
    (s : Fin (onsAnisotropicStepScale width height nu))
    (hs : s.val = 0) :
    fkRectRibbonSubdivisionCodeEmbed width height
        (fkRectRibbonSubdivisionCode width height hwidth hheight
          (fkRectRibbonRectStep width height mu p) nu s) =
      ons_dirStep (width * height) mu
        (fkRectRibbonSubdivisionCodeEmbed width height
          (fkRectRibbonSubdivisionCode width height hwidth hheight p mu r)) := by
  letI : NeZero width := ⟨hwidth.ne'⟩
  letI : NeZero height := ⟨hheight.ne'⟩
  have hxFin : fkRectZModFin hwidth p.1 =
      (⟨p.1.val, p.1.val_lt⟩ : Fin width) :=
    Fin.ext (fkRectZModFin_val hwidth p.1)
  have hyFin : fkRectZModFin hheight p.2 =
      (⟨p.2.val, p.2.val_lt⟩ : Fin height) :=
    Fin.ext (fkRectZModFin_val hheight p.2)
  rw [fkRectRibbonSubdivisionCodeEmbed_offset_zero
    width height hwidth hheight _ nu s hs]
  have hxSucc := fkRectRibbon_scaled_succ_general hwidth hheight
    (fkRectZModFin hwidth p.1)
  have hxPred := fkRectRibbon_scaled_pred_general hwidth hheight
    (fkRectZModFin hwidth p.1)
  have hySucc := fkRectRibbon_scaled_succ_general hheight hwidth
    (fkRectZModFin hheight p.2)
  rw [Nat.mul_comm height width] at hySucc
  have hyPred := fkRectRibbon_scaled_pred_general hheight hwidth
    (fkRectZModFin hheight p.2)
  rw [Nat.mul_comm height width] at hyPred
  have hxValSucc := congrArg Fin.val (fkRectZModFin_add_one hwidth p.1)
  have hxValPred := congrArg Fin.val (fkRectZModFin_sub_one hwidth p.1)
  have hyValSucc := congrArg Fin.val (fkRectZModFin_add_one hheight p.2)
  have hyValPred := congrArg Fin.val (fkRectZModFin_sub_one hheight p.2)
  simp only [fkRectZModFin_val] at hxSucc hxPred hySucc hyPred
  simp only [fkRectZModFin_val] at hxValSucc hxValPred hyValSucc hyValPred
  rw [hxFin] at hxSucc hxPred hxValSucc hxValPred
  rw [hyFin] at hySucc hyPred hyValSucc hyValPred
  push_cast at hxSucc hxPred hySucc hyPred
  have hrLast : r.val + 1 = onsAnisotropicStepScale width height mu := by omega
  have hrLastZ := congrArg
    (fun n : ℕ => (n : ZMod (width * height))) hrLast
  push_cast at hrLastZ
  rcases fkRectFinFour_cases mu with hmu | hmu | hmu | hmu
  all_goals subst mu
  all_goals
    simp only [onsAnisotropicStepScale_zero, onsAnisotropicStepScale_one,
      onsAnisotropicStepScale_two, onsAnisotropicStepScale_three] at hr hrLastZ ⊢
  all_goals norm_num [onsAnisotropicStepScale] at hr
  all_goals by_cases hr0 : r.val = 0 <;>
    simp [fkRectRibbonSubdivisionCode, fkRectRibbonSubdivisionCodeEmbed,
      fkRectRibbonBackwardCode, hr0, finProdFinEquiv, ons_dirStep,
      fkRectRibbonRectStep, hxValSucc, hxValPred, hyValSucc, hyValPred,
      hxSucc, hxPred, hySucc, hyPred, fkRectZModFin] <;>
    try rw [hxSucc] <;> try rw [hxPred] <;>
    try rw [hySucc] <;> try rw [hyPred] <;>
    try simp_rw [Nat.cast_sub (by omega)] <;>
    push_cast
  all_goals try simp [hr0] at hrLastZ
  all_goals try simp only [ZMod.cast_eq_val]
  all_goals try rw [hxSucc]
  all_goals try rw [hySucc]
  all_goals try rw [hxPred]
  all_goals try rw [hyPred]
  all_goals try rw [← hrLastZ]
  all_goals try rw [← hrLastZ] at hxSucc
  all_goals try rw [← hrLastZ] at hxPred
  all_goals try rw [← hrLastZ] at hySucc
  all_goals try rw [← hrLastZ] at hyPred
  all_goals ring_nf at hxSucc hxPred hySucc hyPred ⊢
  all_goals try (convert hySucc using 1 <;> first | rfl | ring)
  all_goals convert hyPred using 1 <;> first | rfl | ring

end

end StatMech.FrontierD
