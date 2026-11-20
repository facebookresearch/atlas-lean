/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonFlatGeometry



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section

def fkRectRibbonBackwardCode {M S : ℕ} (hM : 0 < M) (hS : 0 < S)
    (p : Fin M) (r : Fin S) : Fin M × Fin S := by
  letI : NeZero S := ⟨hS.ne'⟩
  exact
  if hr : r.val = 0 then (p, 0)
  else
    (SixVertexArrows.cyclicPred hM p,
      ⟨S - r.val, by omega⟩)

theorem fkRectRibbonBackwardCode_injective
    {M S : ℕ} (hM : 0 < M) (hS : 0 < S) :
    Function.Injective (fun z : Fin M × Fin S =>
      fkRectRibbonBackwardCode hM hS z.1 z.2) := by
  rintro ⟨p, r⟩ ⟨q, s⟩ h
  by_cases hr : r.val = 0 <;> by_cases hs : s.val = 0
  · simp [fkRectRibbonBackwardCode, hr, hs] at h
    exact Prod.ext h (Fin.ext (hr.trans hs.symm))
  · have hres := congrArg (fun z : Fin M × Fin S => z.2.val) h
    simp [fkRectRibbonBackwardCode, hr, hs] at hres
    change 0 = S - s.val at hres
    omega
  · have hres := congrArg (fun z : Fin M × Fin S => z.2.val) h
    simp [fkRectRibbonBackwardCode, hr, hs] at hres
    change S - r.val = 0 at hres
    omega
  · have hcell := congrArg (fun z : Fin M × Fin S => z.1) h
    have hres := congrArg (fun z : Fin M × Fin S => z.2.val) h
    simp [fkRectRibbonBackwardCode, hr, hs] at hcell hres
    have hpq : p = q := by
      rw [← finitePeriodicSucc_cyclicPred hM p,
        ← finitePeriodicSucc_cyclicPred hM q, hcell]
    change S - r.val = S - s.val at hres
    have hrle : r.val ≤ S := by omega
    have hsle : s.val ≤ S := by omega
    have hcast := congrArg (fun z : Nat => (z : Int)) hres
    change ((S - r.val : Nat) : Int) = ((S - s.val : Nat) : Int) at hcast
    rw [Nat.cast_sub hrle, Nat.cast_sub hsle] at hcast
    have hrs : r = s := Fin.ext (by omega)
    exact Prod.ext hpq hrs

theorem fkRectRibbon_forward_eq_backward
    {M S : ℕ} (hM : 0 < M) (hS : 0 < S)
    (p q : Fin M) (r s : Fin S)
    (h : (p, r) = fkRectRibbonBackwardCode hM hS q s) :
    (r.val = 0 ∧ s.val = 0 ∧ p = q) ∨
      (r.val ≠ 0 ∧ s.val ≠ 0 ∧
        p = SixVertexArrows.cyclicPred hM q ∧ r.val + s.val = S) := by
  by_cases hs : s.val = 0
  · left
    simp [fkRectRibbonBackwardCode, hs] at h
    exact ⟨congrArg Fin.val h.2, hs, h.1⟩
  · right
    have hcell := congrArg (fun z : Fin M × Fin S => z.1) h
    have hres := congrArg (fun z : Fin M × Fin S => z.2.val) h
    simp [fkRectRibbonBackwardCode, hs] at hcell hres
    have hsum : r.val + s.val = S := by
      change r.val = S - s.val at hres
      omega
    exact ⟨fun hr => by omega, hs, hcell, hsum⟩

def fkRectZModFin {M : ℕ} (hM : 0 < M) (p : ZMod M) : Fin M := by
  letI : NeZero M := ⟨hM.ne'⟩
  exact ⟨p.val, p.val_lt⟩

@[simp] theorem fkRectZModFin_val {M : ℕ} (hM : 0 < M) (p : ZMod M) :
    (fkRectZModFin hM p).val = p.val := by
  rfl

theorem fkRectZModFin_injective {M : ℕ} (hM : 0 < M) :
    Function.Injective (fkRectZModFin hM) := by
  letI : NeZero M := ⟨hM.ne'⟩
  intro p q h
  exact ZMod.val_injective M (congrArg Fin.val h)

theorem fkRectZModFin_add_one {M : ℕ} (hM : 0 < M) (p : ZMod M) :
    fkRectZModFin hM (p + 1) =
      finitePeriodicSucc hM (fkRectZModFin hM p) := by
  letI : NeZero M := ⟨hM.ne'⟩
  apply Fin.ext
  simp only [fkRectZModFin, ZMod.val_add, Fin.val_mk, finitePeriodicSucc]
  rw [ZMod.val_one_eq_one_mod, Nat.add_mod_mod]

theorem fkRectZModFin_sub_one {M : ℕ} (hM : 0 < M) (p : ZMod M) :
    fkRectZModFin hM (p - 1) =
      SixVertexArrows.cyclicPred hM (fkRectZModFin hM p) := by
  letI : NeZero M := ⟨hM.ne'⟩
  have hleft := fkRectZModFin_add_one hM (p - 1)
  rw [sub_add_cancel] at hleft
  rw [hleft, svCyclicPred_finitePeriodicSucc]



def fkRectRibbonSubdivisionCode
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (p : ZMod width × ZMod height) (mu : Fin 4)
    (r : Fin (onsAnisotropicStepScale width height mu)) :
    (Fin width × Fin height) × (Fin height × Fin width) := by
  letI : NeZero width := ⟨hwidth.ne'⟩
  letI : NeZero height := ⟨hheight.ne'⟩
  let px : Fin width := ⟨p.1.val, p.1.val_lt⟩
  let py : Fin height := ⟨p.2.val, p.2.val_lt⟩
  exact match mu with
  | 0 => ((px, r), (py, 0))
  | 1 => ((px, 0), (py, r))
  | 2 => (fkRectRibbonBackwardCode hwidth hheight px r, (py, 0))
  | 3 => ((px, 0), fkRectRibbonBackwardCode hheight hwidth py r)


def fkRectRibbonSubdivisionResidueCongr
    (width height : ℕ) {mu nu : Fin 4} (h : mu = nu) :
    Fin (onsAnisotropicStepScale width height mu) ≃
      Fin (onsAnisotropicStepScale width height nu) :=
  finCongr (congrArg (onsAnisotropicStepScale width height) h)

theorem fkRectRibbonSubdivisionCode_congr_direction
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (p : ZMod width × ZMod height) {mu nu : Fin 4}
    (h : mu = nu)
    (r : Fin (onsAnisotropicStepScale width height mu)) :
    fkRectRibbonSubdivisionCode width height hwidth hheight p mu r =
      fkRectRibbonSubdivisionCode width height hwidth hheight p nu
        (fkRectRibbonSubdivisionResidueCongr width height h r) := by
  subst nu
  rfl

theorem fkRectRibbonSubdivisionCode_fixed_injective
    (width height : ℕ) (hwidth : 0 < width) (hheight : 0 < height)
    (p : ZMod width × ZMod height) (mu : Fin 4) :
    Function.Injective
      (fkRectRibbonSubdivisionCode width height hwidth hheight p mu) := by
  letI : NeZero width := ⟨hwidth.ne'⟩
  letI : NeZero height := ⟨hheight.ne'⟩
  fin_cases mu
  · intro r s h
    have hrs := congrArg
      (fun c : (Fin width × Fin height) × (Fin height × Fin width) => c.1.2) h
    simpa [fkRectRibbonSubdivisionCode] using hrs
  · intro r s h
    have hrs := congrArg
      (fun c : (Fin width × Fin height) × (Fin height × Fin width) => c.2.2) h
    simpa [fkRectRibbonSubdivisionCode] using hrs
  · intro r s h
    have hrs := congrArg
      (fun c : (Fin width × Fin height) × (Fin height × Fin width) => c.1) h
    have hpairs :
        ((⟨p.1.val, p.1.val_lt⟩ : Fin width), r) =
          ((⟨p.1.val, p.1.val_lt⟩ : Fin width), s) := by
      apply fkRectRibbonBackwardCode_injective hwidth hheight
      simpa [fkRectRibbonSubdivisionCode] using hrs
    exact congrArg Prod.snd hpairs
  · intro r s h
    have hrs := congrArg
      (fun c : (Fin width × Fin height) × (Fin height × Fin width) => c.2) h
    have hpairs :
        ((⟨p.2.val, p.2.val_lt⟩ : Fin height), r) =
          ((⟨p.2.val, p.2.val_lt⟩ : Fin height), s) := by
      apply fkRectRibbonBackwardCode_injective hheight hwidth
      simpa [fkRectRibbonSubdivisionCode] using hrs
    exact congrArg Prod.snd hpairs

def fkRectRibbonSubdivisionCodeEmbed
    (width height : ℕ)
    (c : (Fin width × Fin height) × (Fin height × Fin width)) :
    ZMod (width * height) × ZMod (width * height) :=
  ((finProdFinEquiv c.1).val, (finProdFinEquiv c.2).val)

theorem fkRectRibbonSubdivisionCodeEmbed_injective
    (width height : ℕ) [NeZero width] [NeZero height] :
    Function.Injective (fkRectRibbonSubdivisionCodeEmbed width height) := by
  intro c e h
  have hx := congrArg (fun z : ZMod (width * height) ×
      ZMod (width * height) => z.1.val) h
  have hy := congrArg (fun z : ZMod (width * height) ×
      ZMod (width * height) => z.2.val) h
  simp only [fkRectRibbonSubdivisionCodeEmbed, ZMod.val_natCast] at hx hy
  have hcx : (finProdFinEquiv c.1).val < width * height :=
    (finProdFinEquiv c.1).isLt
  have hex : (finProdFinEquiv e.1).val < width * height :=
    (finProdFinEquiv e.1).isLt
  have hcy : (finProdFinEquiv c.2).val < width * height :=
    by simpa [Nat.mul_comm] using (finProdFinEquiv c.2).isLt
  have hey : (finProdFinEquiv e.2).val < width * height :=
    by simpa [Nat.mul_comm] using (finProdFinEquiv e.2).isLt
  rw [Nat.mod_eq_of_lt hcx, Nat.mod_eq_of_lt hex] at hx
  rw [Nat.mod_eq_of_lt hcy, Nat.mod_eq_of_lt hey] at hy
  exact Prod.ext (finProdFinEquiv.injective (Fin.ext hx))
    (finProdFinEquiv.injective (Fin.ext hy))

abbrev FKRectBlackOrbitRibbonSubdivisionIndex
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :=
  Σ k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length,
    Fin (onsAnisotropicStepScale (8 * R.medialTorus.width)
      (8 * R.medialTorus.height)
      (fkRectBlackOrbitMedialRibbonFlatDirection R omega d k))

def fkRectBlackOrbitRibbonSubdivisionCode
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z : FKRectBlackOrbitRibbonSubdivisionIndex R omega d) :=
  fkRectRibbonSubdivisionCode
    (8 * R.medialTorus.width) (8 * R.medialTorus.height)
    (mul_pos (by decide) R.medialTorus.width_pos)
    (mul_pos (by decide) R.medialTorus.height_pos)
    (fkRectBlackOrbitMedialRibbonFlatSite R omega d z.1)
    (fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1) z.2

theorem fkRectFinFour_cases (mu : Fin 4) :
    mu = 0 ∨ mu = 1 ∨ mu = 2 ∨ mu = 3 := by
  fin_cases mu <;> simp

end

end StatMech.FrontierD
