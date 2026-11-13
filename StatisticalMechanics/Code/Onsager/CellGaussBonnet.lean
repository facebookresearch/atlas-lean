/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.CellEuler
































namespace StatMech.Onsager.CellGaussBonnet

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler




theorem cornerDiff_cex :
    cornerDiff ({((0:ℤ), (0:ℤ)), ((1:ℤ), (1:ℤ))} : Finset (ℤ × ℤ)) = 6 := by decide


theorem eulerChar_cex :
    eulerChar ({((0:ℤ), (0:ℤ)), ((1:ℤ), (1:ℤ))} : Finset (ℤ × ℤ)) = 1 := by decide



theorem gaussBonnet_stated_false :
    ¬ ∀ S : Finset (ℤ × ℤ), cornerDiff S = 4 * eulerChar S := by
  intro h
  have := h ({((0:ℤ), (0:ℤ)), ((1:ℤ), (1:ℤ))} : Finset (ℤ × ℤ))
  rw [cornerDiff_cex, eulerChar_cex] at this
  norm_num at this















def bI (b : Bool) : ℤ := if b then 1 else 0



def icw (k : ℤ) : ℤ := (if k = 1 then 1 else 0) - (if k = 3 then 1 else 0)


def ijump (m : ℤ) : ℤ := icw (m + 1) - icw m


def isZero (m : ℤ) : ℤ := if m = 0 then 1 else 0




def lhsLocal (e w n s ne nw se sw : Bool) : ℤ :=
  ijump (bI w + bI s + bI sw) + ijump (bI e + bI se + bI s)
    + ijump (bI n + bI nw + bI w) + ijump (bI ne + bI n + bI e)


def deltaV (e w n s ne nw se sw : Bool) : ℤ :=
  isZero (bI w + bI s + bI sw) + isZero (bI e + bI se + bI s)
    + isZero (bI n + bI nw + bI w) + isZero (bI ne + bI n + bI e)




def deltaE (e w n s : Bool) : ℤ :=
  (1 - bI s) + (1 - bI n) + (1 - bI w) + (1 - bI e)


def rhsStated (e w n s ne nw se sw : Bool) : ℤ :=
  4 * (deltaV e w n s ne nw se sw - deltaE e w n s + 1)





theorem localIdentity_stated_false :
    ¬ ∀ e w n s ne nw se sw : Bool,
      lhsLocal e w n s ne nw se sw = rhsStated e w n s ne nw se sw := by
  intro h
  have := h false false false false false false false true
  simp only [lhsLocal, rhsStated, deltaV, deltaE, bI, ijump, icw, isZero] at this
  norm_num at this












def pinchDelta (e w n s ne nw se sw : Bool) : ℤ :=
  
  (bI (sw && !w && !s) - bI (w && s && !sw))
  
  + (bI (se && !e && !s) - bI (e && s && !se))
  
  + (bI (nw && !n && !w) - bI (n && w && !nw))
  
  + (bI (ne && !n && !e) - bI (n && e && !ne))


def rhsCorrected (e w n s ne nw se sw : Bool) : ℤ :=
  rhsStated e w n s ne nw se sw + 2 * pinchDelta e w n s ne nw se sw





theorem localIdentity_corrected :
    ∀ e w n s ne nw se sw : Bool,
      lhsLocal e w n s ne nw se sw = rhsCorrected e w n s ne nw se sw := by
  decide

end StatMech.Onsager.CellGaussBonnet
