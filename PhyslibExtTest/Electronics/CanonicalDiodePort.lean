/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibExt.Electronics.CanonicalDiodePort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

open Matrix
open PhyslibExt.Circuits.ArcPortSigns
open PhyslibExt.Electronics.CanonicalDiodePort

namespace PhyslibExtTest.Electronics.CanonicalDiodePort

/-! ### Thermal voltage -/

/-- A negative carrier charge gives a positive thermal voltage: `kB = 2`,
`T = 3`, `q = -4` give `VT = 3 / 2`, while the signed quotient `2 * 3 / (-4)`
would be negative. -/
example : thermalVoltage 2 3 (-4) = 3 / 2 ∧ (2 * 3 / (-4) : ℝ) < 0 := by
  norm_num [thermalVoltage]

example : thermalVoltage 2 3 (-4) = thermalVoltage 2 3 4 :=
  thermalVoltage_neg_charge 2 3 4

/-- The Einstein ratio of the transport model at mobility `5` is the same
thermal voltage. -/
example :
    PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves.diffusionCoeff 5 2 3 (-4) / 5 =
      3 / 2 := by
  rw [einstein_ratio_eq_thermalVoltage (by norm_num) (by norm_num)]
  norm_num [thermalVoltage]

/-! ### Unit parameters: `Is = n = kB = T = 1`, `q = -1` -/

/-- At unit parameters the diode current is `exp V - 1`. -/
lemma diodeCurrent_unit (x : ℝ) : diodeCurrent 1 1 1 1 (-1) x = Real.exp x - 1 := by
  simp [diodeCurrent, PhyslibExt.Electronics.EbersMollTerminalBalance.forwardBranchCurrent,
    thermalVoltage]

example : diodeCurrent 1 1 1 1 (-1) 0 = 0 :=
  diodeCurrent_zero 1 1 1 1 (-1)

/-- Small-signal conductance at zero bias is `Is / (n * VT) = 1`. -/
example : HasDerivAt (diodeCurrent 1 1 1 1 (-1)) 1 0 := by
  have h := hasDerivAt_diodeCurrent 1 1 1 1 (-1) 0
  norm_num [thermalVoltage] at h
  exact h

/-- Forward bias `V = 1` conducts; reverse bias `V = -1` gives a negative current
above `-Is = -1`. -/
example : 0 < diodeCurrent 1 1 1 1 (-1) 1 ∧ diodeCurrent 1 1 1 1 (-1) (-1) < 0 ∧
    -1 < diodeCurrent 1 1 1 1 (-1) (-1) := by
  have hpos (x : ℝ) : 0 < diodeCurrent 1 1 1 1 (-1) x ↔ 0 < x :=
    diodeCurrent_pos_iff one_pos one_pos one_pos one_pos (by norm_num)
  refine ⟨(hpos 1).2 one_pos, ?_,
    neg_saturation_lt_diodeCurrent (-1) one_pos one_pos one_pos one_pos (by norm_num)⟩
  rw [diodeCurrent_unit]
  linarith [Real.exp_lt_one_iff.mpr (show (-1 : ℝ) < 0 by norm_num)]

example : Filter.Tendsto (diodeCurrent 1 1 1 1 (-1)) Filter.atBot (nhds (-1)) :=
  tendsto_diodeCurrent_atBot one_pos one_pos one_pos (by norm_num)

/-- At `T = 0` the formula collapses to zero current and is not strictly
increasing, so the temperature premise is needed. -/
example : ¬ StrictMono (diodeCurrent 1 1 1 0 (-1)) := by
  intro hm
  have h := hm (show (0 : ℝ) < 1 by norm_num)
  rw [diodeCurrent_eq_zero_of_invalid (Or.inr (Or.inl rfl))] at h
  exact lt_irrefl _ h

example : diodeCurrent 2 0 1 1 (-1) 5 = 0 := by
  rw [diodeCurrent_eq_zero_of_invalid (Or.inl rfl)]

example : diodeCurrent 2 1 1 1 0 5 = 0 := by
  rw [diodeCurrent_eq_zero_of_invalid (Or.inr (Or.inr rfl))]

/-! ### A two-node branch: anode at node `0`, cathode at node `1`, `phi = (1, 0)` -/

/-- Forward orientation: the branch runs from the anode (tail) to the cathode
(head), so the anode sign is `+1` and the branch voltage is `1`. -/
lemma sign_forward : electricalIncidence (V := Fin 2) (E := Fin 1) ![0] ![1] 0 0 = 1 := by
  rw [electricalIncidence_apply]
  norm_num

/-- Reversed orientation: the anode is the head, so the anode sign is `-1` and the
branch voltage is `-1`. -/
lemma sign_reversed : electricalIncidence (V := Fin 2) (E := Fin 1) ![1] ![0] 0 0 = -1 := by
  rw [electricalIncidence_apply]
  norm_num

lemma kvl_forward : (![1] : Fin 1 → ℝ) =
    (electricalIncidence (V := Fin 2) (E := Fin 1) ![0] ![1]).transpose *ᵥ ![1, 0] := by
  ext e
  fin_cases e
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, electricalIncidence_apply,
    Fin.sum_univ_two]

lemma kvl_reversed : (![-1] : Fin 1 → ℝ) =
    (electricalIncidence (V := Fin 2) (E := Fin 1) ![1] ![0]).transpose *ᵥ ![1, 0] := by
  ext e
  fin_cases e
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, electricalIncidence_apply,
    Fin.sum_univ_two]

lemma diodeBranch_forward :
    DiodeBranch 1 1 1 1 (-1) (V := Fin 2) (E := Fin 1) ![0] ![1] 0 1 0 ![1]
      ![diodeCurrent 1 1 1 1 (-1) 1] := by
  simp [DiodeBranch, sign_forward]

lemma diodeBranch_reversed :
    DiodeBranch 1 1 1 1 (-1) (V := Fin 2) (E := Fin 1) ![1] ![0] 0 1 0 ![-1]
      ![-diodeCurrent 1 1 1 1 (-1) 1] := by
  simp [DiodeBranch, sign_reversed]

/-- Forward orientation through the headline: the anode current is
`I_D (phi 0 - phi 1) = e - 1`, and it is positive. -/
example :
    electricalIncidence (V := Fin 2) (E := Fin 1) ![0] ![1] 0 0 *
        (![diodeCurrent 1 1 1 1 (-1) 1] : Fin 1 → ℝ) 0 = Real.exp 1 - 1 ∧
      0 < (![diodeCurrent 1 1 1 1 (-1) 1] : Fin 1 → ℝ) 0 := by
  have h := (canonicalDiodePort_correct one_pos one_pos one_pos one_pos (by norm_num)
    (show (0 : Fin 2) ≠ 1 by decide) kvl_forward diodeBranch_forward).2.2.2.2.2.2.2.2.1
  have hpos (x : ℝ) : 0 < diodeCurrent 1 1 1 1 (-1) x ↔ 0 < x :=
    diodeCurrent_pos_iff one_pos one_pos one_pos one_pos (by norm_num)
  refine ⟨?_, by simpa using (hpos 1).2 one_pos⟩
  rw [h, diodeCurrent_unit]
  norm_num

/-- Reversed orientation: the same physical diode, so the anode current is still
`e - 1`, while the branch current measured tail to head is negative. -/
example :
    electricalIncidence (V := Fin 2) (E := Fin 1) ![1] ![0] 0 0 *
        (![-diodeCurrent 1 1 1 1 (-1) 1] : Fin 1 → ℝ) 0 = Real.exp 1 - 1 ∧
      (![-diodeCurrent 1 1 1 1 (-1) 1] : Fin 1 → ℝ) 0 < 0 := by
  have h := anodeCurrent_of_diodeBranch (show (0 : Fin 2) ≠ 1 by decide) kvl_reversed
    diodeBranch_reversed
  refine ⟨?_, ?_⟩
  · rw [h, diodeCurrent_unit]
    norm_num
  · have := (diodeCurrent_pos_iff (V := 1) one_pos one_pos one_pos one_pos
      (show (-1 : ℝ) ≠ 0 by norm_num)).2 one_pos
    simpa using this

/-- Reversing the forward branch, its voltage and its current gives a diode
branch again. -/
example :
    DiodeBranch 1 1 1 1 (-1) (V := Fin 2) (E := Fin 1)
      (Function.update ![0] 0 ((![1] : Fin 1 → Fin 2) 0))
      (Function.update ![1] 0 ((![0] : Fin 1 → Fin 2) 0)) 0 1 0
      (Function.update ![1] 0 (-(![1] : Fin 1 → ℝ) 0))
      (Function.update ![diodeCurrent 1 1 1 1 (-1) 1] 0
        (-(![diodeCurrent 1 1 1 1 (-1) 1] : Fin 1 → ℝ) 0)) :=
  diodeBranch_reverse diodeBranch_forward

/-- The orientation sign cannot be dropped: on the reversed branch, the relation
`i = I_D v` is not a diode branch. -/
example :
    ¬ DiodeBranch 1 1 1 1 (-1) (V := Fin 2) (E := Fin 1) ![1] ![0] 0 1 0 ![-1]
      ![diodeCurrent 1 1 1 1 (-1) (-1)] := by
  intro h
  have h' := h.2
  simp only [sign_reversed, Matrix.cons_val_fin_one, diodeCurrent_unit] at h'
  have h1 := Real.exp_pos (-1)
  have h2 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have h3 := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
  norm_num at h'
  linarith

end PhyslibExtTest.Electronics.CanonicalDiodePort
