/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.HexInjections
import Code.Universality.HexBoundaryAssign

namespace StatMech.Universality

open Complex HexWalk Set
open scoped BigOperators



def hexContourFamily (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (side : Set ℂ) :
    Set (List ℤ) :=
  {ts | (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion ∧
    ∃ z ∈ side, (ofTurns a h0 ts).EndsAt z}


noncomputable def hexContourSum (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (side : Set ℂ) (x : ℝ) : ℝ :=
  ∑' ts : {ts // ts ∈ hexContourFamily inRegion a h0 side},
    x ^ (ofTurns a h0 ts.1).numVertices


structure HexContourSides where
  
  bottom : Set ℂ
  
  slantPlus : Set ℂ
  
  slantMinus : Set ℂ
  
  top : Set ℂ


noncomputable def hexContourLambda (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (sides : HexContourSides) (x : ℝ) : ℝ :=
  hexContourSum inRegion a h0 sides.bottom x


noncomputable def hexContourTauPlus (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (sides : HexContourSides) (x : ℝ) : ℝ :=
  hexContourSum inRegion a h0 sides.slantPlus x


noncomputable def hexContourTauMinus (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (sides : HexContourSides) (x : ℝ) : ℝ :=
  hexContourSum inRegion a h0 sides.slantMinus x


noncomputable def hexContourUpsilon (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (sides : HexContourSides) (x : ℝ) : ℝ :=
  hexContourSum inRegion a h0 sides.top x

end StatMech.Universality
