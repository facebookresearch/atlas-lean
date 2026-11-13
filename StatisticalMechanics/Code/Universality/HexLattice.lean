/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib

namespace StatMech.Universality

open Complex
open scoped ENNReal BigOperators










noncomputable def hexUnit (h : ℤ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)))


@[simp]
theorem norm_hexUnit (h : ℤ) : ‖hexUnit h‖ = 1 := by
  unfold hexUnit
  rw [Complex.norm_exp]
  simp [Complex.mul_re]


theorem hexUnit_ne_zero (h : ℤ) : hexUnit h ≠ 0 := by
  intro hz
  have := norm_hexUnit h
  rw [hz] at this
  simp at this




theorem hexUnit_zero : hexUnit 0 = Complex.exp (Complex.I * (Real.pi / 6)) := by
  unfold hexUnit; norm_num

theorem hexUnit_one : hexUnit 1 = Complex.exp (Complex.I * (Real.pi / 2)) := by
  unfold hexUnit
  congr 1
  push_cast
  ring

theorem hexUnit_two : hexUnit 2 = Complex.exp (Complex.I * (5 * Real.pi / 6)) := by
  unfold hexUnit
  congr 1
  push_cast
  ring




theorem hexUnit_add_three (h : ℤ) : hexUnit (h + 3) = - hexUnit h := by
  unfold hexUnit
  have hsplit : Complex.I * (Real.pi / 6 + ((h + 3 : ℤ) : ℝ) * (Real.pi / 3))
      = Complex.I * (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) + (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I]
  ring











structure HexWalk where
  
  startMid : ℂ
  
  h0 : ℤ
  

  turns : List ℤ

namespace HexWalk



def headingsAux (h : ℤ) : List ℤ → List ℤ
  | [] => [h]
  | t :: ts => h :: headingsAux (h + t) ts


def headings (w : HexWalk) : List ℤ := headingsAux w.h0 w.turns

@[simp]
theorem headingsAux_nil (h : ℤ) : headingsAux h [] = [h] := rfl

@[simp]
theorem headingsAux_cons (h t : ℤ) (ts : List ℤ) :
    headingsAux h (t :: ts) = h :: headingsAux (h + t) ts := rfl


theorem length_headingsAux (h : ℤ) (ts : List ℤ) :
    (headingsAux h ts).length = ts.length + 1 := by
  induction ts generalizing h with
  | nil => simp
  | cons t ts ih => simp [ih]

@[simp]
theorem length_headings (w : HexWalk) : w.headings.length = w.turns.length + 1 := by
  unfold headings; exact length_headingsAux _ _


@[simp]
theorem headings_head (w : HexWalk) : (w.headings).headI = w.h0 := by
  unfold headings; cases w.turns with
  | nil => rfl
  | cons t ts => rfl









noncomputable def halfStep (h : ℤ) : ℂ := (1 / 2 : ℂ) * hexUnit h






noncomputable def midsAux (m : ℂ) (h : ℤ) : List ℤ → List ℂ
  | [] => [m]
  | t :: ts => m :: midsAux (m + halfStep h + halfStep (h + t)) (h + t) ts


noncomputable def mids (w : HexWalk) : List ℂ := midsAux w.startMid w.h0 w.turns

@[simp]
theorem midsAux_nil (m : ℂ) (h : ℤ) : midsAux m h [] = [m] := rfl

@[simp]
theorem midsAux_cons (m : ℂ) (h t : ℤ) (ts : List ℤ) :
    midsAux m h (t :: ts)
      = m :: midsAux (m + halfStep h + halfStep (h + t)) (h + t) ts := rfl

theorem length_midsAux (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (midsAux m h ts).length = ts.length + 1 := by
  induction ts generalizing m h with
  | nil => simp
  | cons t ts ih => simp [ih]

@[simp]
theorem length_mids (w : HexWalk) : w.mids.length = w.turns.length + 1 := by
  unfold mids; exact length_midsAux _ _ _


@[simp]
theorem mids_head (w : HexWalk) : (w.mids).headI = w.startMid := by
  unfold mids; cases w.turns with
  | nil => rfl
  | cons t ts => rfl




noncomputable def verticesAux (m : ℂ) (h : ℤ) : List ℤ → List ℂ
  | [] => [m + halfStep h]
  | t :: ts => (m + halfStep h) :: verticesAux (m + halfStep h + halfStep (h + t)) (h + t) ts


noncomputable def vertices (w : HexWalk) : List ℂ := verticesAux w.startMid w.h0 w.turns

@[simp]
theorem verticesAux_nil (m : ℂ) (h : ℤ) : verticesAux m h [] = [m + halfStep h] := rfl

@[simp]
theorem verticesAux_cons (m : ℂ) (h t : ℤ) (ts : List ℤ) :
    verticesAux m h (t :: ts)
      = (m + halfStep h) :: verticesAux (m + halfStep h + halfStep (h + t)) (h + t) ts := rfl

theorem length_verticesAux (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (verticesAux m h ts).length = ts.length + 1 := by
  induction ts generalizing m h with
  | nil => simp
  | cons t ts ih => simp [ih]


@[simp]
theorem length_vertices (w : HexWalk) : w.vertices.length = w.turns.length + 1 := by
  unfold vertices; exact length_verticesAux _ _ _





def numVertices (w : HexWalk) : ℕ := w.turns.length + 1

@[simp]
theorem numVertices_eq (w : HexWalk) : w.numVertices = w.turns.length + 1 := rfl

@[simp]
theorem length_vertices_eq_numVertices (w : HexWalk) :
    w.vertices.length = w.numVertices := by simp [numVertices]



noncomputable def endMid (w : HexWalk) : ℂ := (w.mids).getLast (by simp [length_mids, List.ne_nil_of_length_pos])







def turnCount (w : HexWalk) : ℤ := w.turns.sum

@[simp]
theorem turnCount_eq (w : HexWalk) : w.turnCount = w.turns.sum := rfl




noncomputable def turning (w : HexWalk) : ℝ := (Real.pi / 3) * (w.turnCount : ℝ)

@[simp]
theorem turning_eq (w : HexWalk) : w.turning = (Real.pi / 3) * (w.turns.sum : ℝ) := rfl









def LegalTurns (w : HexWalk) : Prop := ∀ t ∈ w.turns, t = 1 ∨ t = -1



def IsSAW (w : HexWalk) : Prop := w.vertices.Nodup



def IsLegalSAW (w : HexWalk) : Prop := w.LegalTurns ∧ w.IsSAW









def trivialWalk (a : ℂ) (h : ℤ) : HexWalk := ⟨a, h, []⟩

@[simp] theorem trivialWalk_startMid (a : ℂ) (h : ℤ) : (trivialWalk a h).startMid = a := rfl
@[simp] theorem trivialWalk_h0 (a : ℂ) (h : ℤ) : (trivialWalk a h).h0 = h := rfl
@[simp] theorem trivialWalk_turns (a : ℂ) (h : ℤ) : (trivialWalk a h).turns = [] := rfl


@[simp]
theorem trivialWalk_numVertices (a : ℂ) (h : ℤ) : (trivialWalk a h).numVertices = 1 := rfl


@[simp]
theorem trivialWalk_turning (a : ℂ) (h : ℤ) : (trivialWalk a h).turning = 0 := by
  simp [turning, turnCount, trivialWalk]


theorem trivialWalk_legalTurns (a : ℂ) (h : ℤ) : (trivialWalk a h).LegalTurns := by
  intro t ht; simp [trivialWalk] at ht


theorem trivialWalk_isSAW (a : ℂ) (h : ℤ) : (trivialWalk a h).IsSAW := by
  unfold IsSAW vertices; simp [trivialWalk]


theorem trivialWalk_isLegalSAW (a : ℂ) (h : ℤ) : (trivialWalk a h).IsLegalSAW :=
  ⟨trivialWalk_legalTurns a h, trivialWalk_isSAW a h⟩










theorem turnCount_append (a : ℂ) (h : ℤ) (s t : List ℤ) :
    turnCount ⟨a, h, s ++ t⟩ = turnCount ⟨a, h, s⟩ + turnCount ⟨a, h, t⟩ := by
  simp [turnCount, List.sum_append]




theorem turning_append (a : ℂ) (h : ℤ) (s t : List ℤ) :
    turning ⟨a, h, s ++ t⟩ = turning ⟨a, h, s⟩ + turning ⟨a, h, t⟩ := by
  simp only [turning, turnCount_append]
  push_cast
  ring




theorem turning_concat (a : ℂ) (h : ℤ) (s : List ℤ) (t : ℤ) :
    turning ⟨a, h, s ++ [t]⟩ = turning ⟨a, h, s⟩ + (Real.pi / 3) * (t : ℝ) := by
  rw [turning_append]
  congr 1
  simp [turning, turnCount]











def ofTurns (a : ℂ) (h0 : ℤ) (ts : List ℤ) : HexWalk := ⟨a, h0, ts⟩

@[simp] theorem ofTurns_turns (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (ofTurns a h0 ts).turns = ts := rfl
@[simp] theorem ofTurns_startMid (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (ofTurns a h0 ts).startMid = a := rfl
@[simp] theorem ofTurns_h0 (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (ofTurns a h0 ts).h0 = h0 := rfl

end HexWalk










open HexWalk




noncomputable def hexZSummand (a : ℂ) (h0 : ℤ) (x : ℝ) (ts : List ℤ) : ℝ≥0∞ :=
  haveI := Classical.propDecidable ((ofTurns a h0 ts).IsLegalSAW)
  if (ofTurns a h0 ts).IsLegalSAW then ENNReal.ofReal (x ^ (ofTurns a h0 ts).numVertices) else 0





noncomputable def hexZ (a : ℂ) (h0 : ℤ) (x : ℝ) : ℝ≥0∞ :=
  ∑' ts : List ℤ, hexZSummand a h0 x ts



@[simp]
theorem hexZSummand_nil (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hexZSummand a h0 x [] = ENNReal.ofReal x := by
  unfold hexZSummand
  rw [if_pos]
  · simp
  · exact trivialWalk_isLegalSAW a h0













def HexWalk.StaysIn (inRegion : ℂ → Prop) (w : HexWalk) : Prop :=
  ∀ m ∈ w.mids, inRegion m


def HexWalk.EndsAt (z : ℂ) (w : HexWalk) : Prop := w.endMid = z






noncomputable def parafSummand (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (σ x : ℝ) (ts : List ℤ) : ℂ :=
  haveI := Classical.propDecidable ((ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt z)
  if (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt z then
    Complex.exp (-Complex.I * (σ : ℂ) * ((ofTurns a h0 ts).turning : ℂ))
      * ((x : ℂ) ^ (ofTurns a h0 ts).numVertices)
  else 0







noncomputable def parafObservable (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (σ x : ℝ) : ℂ :=
  ∑' ts : List ℤ, parafSummand inRegion a h0 z σ x ts










def IsBoundaryOf (boundary region : ℂ → Prop) : Prop := ∀ m, boundary m → region m















theorem trivialWalk_endMid (a : ℂ) (h0 : ℤ) : HexWalk.endMid (trivialWalk a h0) = a := by
  unfold HexWalk.endMid
  have : (trivialWalk a h0).mids = [a] := by
    unfold HexWalk.mids; simp [trivialWalk]
  simp [this]






theorem parafSummand_self (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (σ x : ℝ)
    (hreg : region a) :
    parafSummand region a h0 a σ x [] = (x : ℂ) := by
  have hofeq : ofTurns a h0 [] = trivialWalk a h0 := rfl
  have hmids : (trivialWalk a h0).mids = [a] := by
    unfold HexWalk.mids; simp [trivialWalk]
  unfold parafSummand
  rw [if_pos]
  · have hturn : (trivialWalk a h0).turning = 0 := trivialWalk_turning a h0
    have hnum : (trivialWalk a h0).numVertices = 1 := rfl
    rw [hofeq, hturn, hnum]
    simp
  · rw [hofeq]
    refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
    intro m hm
    rw [hmids] at hm
    simp only [List.mem_singleton] at hm
    rw [hm]; exact hreg

end StatMech.Universality
