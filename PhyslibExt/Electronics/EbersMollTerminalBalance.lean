/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Ebers-Moll terminal-current balance

## i. Overview

The Ebers-Moll model gives the collector, base and emitter
currents of a bipolar transistor from forward and reverse
saturation currents, current gains and the two junction
voltages. The three terminal currents balance, each junction
current is smooth with the stated derivative, the collector
transconductance at zero collector-base voltage is the stated
forward expression, the and in transport form the
collector current is the forward transport current minus the
reverse transport current. When the forward and reverse
saturation currents satisfy the reciprocity relation
`alphaF * IsF = alphaR * IsR`, both derive from one transport
saturation current. At zero bias every terminal current
vanishes; in forward-active operation (positive forward
saturation and gain, zero reverse drive) the collector and
emitter currents are positive.

## ii. Key results

- `terminal_current_balance`: collector plus base minus emitter
  current is zero.
- `hasDerivAt_collectorCurrent_vbe` and the companion derivative
  lemmas: each terminal current is smooth in each junction
  voltage.
- `collectorTransconductance_of_vbc_zero`: the forward-active
  transconductance.
- `collectorCurrent_of_transportSaturation` and
  `emitterCurrent_of_transportSaturation`: with both saturation
  currents derived from one transport current `IS` (the physical
  reciprocal parameterization), the terminal currents take
  transport form. `reciprocal_parameterization` states the
  equivalence with the relation `alphaF * IsF = alphaR * IsR`.

## iii. Table of contents

- A. Ebers-Moll terminal currents

## iv. References

- D. A. Neamen, *Semiconductor Physics and Devices: Basic
Principles*, fourth edition, McGraw-Hill, 2012: the Ebers-Moll model, terminal currents and the
  transport form.

## A. Ebers-Moll terminal currents
-/

@[expose] public section

namespace PhyslibExt.Electronics.EbersMollTerminalBalance

/-- Forward (base-emitter) branch current `F = IsF * (exp (Vbe / VT) - 1)`. -/
noncomputable def forwardBranchCurrent (IsF VT Vbe : ℝ) : ℝ :=
  IsF * (Real.exp (Vbe / VT) - 1)

/-- Reverse (base-collector) branch current `R = IsR * (exp (Vbc / VT) - 1)`. -/
noncomputable def reverseBranchCurrent (IsR VT Vbc : ℝ) : ℝ :=
  IsR * (Real.exp (Vbc / VT) - 1)

/-- Collector current, positive into the collector: `Ic = alphaF * F - R`. -/
noncomputable def collectorCurrent (IsF IsR alphaF VT Vbe Vbc : ℝ) : ℝ :=
  alphaF * forwardBranchCurrent IsF VT Vbe - reverseBranchCurrent IsR VT Vbc

/-- Emitter current, positive out of the emitter: `Ie = F - alphaR * R`. -/
noncomputable def emitterCurrent (IsF IsR alphaR VT Vbe Vbc : ℝ) : ℝ :=
  forwardBranchCurrent IsF VT Vbe - alphaR * reverseBranchCurrent IsR VT Vbc

/-- Base current, positive into the base, declared independently of `Ic` and `Ie`:
`Ib = (1 - alphaF) * F + (1 - alphaR) * R`. -/
noncomputable def baseCurrent (IsF IsR alphaF alphaR VT Vbe Vbc : ℝ) : ℝ :=
  (1 - alphaF) * forwardBranchCurrent IsF VT Vbe +
    (1 - alphaR) * reverseBranchCurrent IsR VT Vbc

private theorem forwardBranchCurrent_zero (IsF VT : ℝ) :
    forwardBranchCurrent IsF VT 0 = 0 := by
  simp [forwardBranchCurrent]

private theorem reverseBranchCurrent_zero (IsR VT : ℝ) :
    reverseBranchCurrent IsR VT 0 = 0 := by
  simp [reverseBranchCurrent]

private theorem forwardBranchCurrent_pos_of_pos (IsF VT Vbe : ℝ) (hVT : 0 < VT)
    (hIsF : 0 < IsF) (hVbe : 0 < Vbe) : 0 < forwardBranchCurrent IsF VT Vbe := by
  have hdiv : 0 < Vbe / VT := div_pos hVbe hVT
  have hexp : 1 < Real.exp (Vbe / VT) := Real.one_lt_exp_iff.mpr hdiv
  have hsub : 0 < Real.exp (Vbe / VT) - 1 := by linarith
  unfold forwardBranchCurrent
  exact mul_pos hIsF hsub

private theorem forwardBranchCurrent_neg_of_neg (IsF VT Vbe : ℝ) (hVT : 0 < VT)
    (hIsF : 0 < IsF) (hVbe : Vbe < 0) : forwardBranchCurrent IsF VT Vbe < 0 := by
  have hdiv : Vbe / VT < 0 := div_neg_of_neg_of_pos hVbe hVT
  have hexp : Real.exp (Vbe / VT) < 1 := Real.exp_lt_one_iff.mpr hdiv
  have hsub : Real.exp (Vbe / VT) - 1 < 0 := by linarith
  unfold forwardBranchCurrent
  exact mul_neg_of_pos_of_neg hIsF hsub

private theorem reverseBranchCurrent_pos_of_pos (IsR VT Vbc : ℝ) (hVT : 0 < VT)
    (hIsR : 0 < IsR) (hVbc : 0 < Vbc) : 0 < reverseBranchCurrent IsR VT Vbc := by
  have hdiv : 0 < Vbc / VT := div_pos hVbc hVT
  have hexp : 1 < Real.exp (Vbc / VT) := Real.one_lt_exp_iff.mpr hdiv
  have hsub : 0 < Real.exp (Vbc / VT) - 1 := by linarith
  unfold reverseBranchCurrent
  exact mul_pos hIsR hsub

private theorem reverseBranchCurrent_neg_of_neg (IsR VT Vbc : ℝ) (hVT : 0 < VT)
    (hIsR : 0 < IsR) (hVbc : Vbc < 0) : reverseBranchCurrent IsR VT Vbc < 0 := by
  have hdiv : Vbc / VT < 0 := div_neg_of_neg_of_pos hVbc hVT
  have hexp : Real.exp (Vbc / VT) < 1 := Real.exp_lt_one_iff.mpr hdiv
  have hsub : Real.exp (Vbc / VT) - 1 < 0 := by linarith
  unfold reverseBranchCurrent
  exact mul_neg_of_pos_of_neg hIsR hsub

private theorem hasDerivAt_forwardBranch (IsF VT Vbe : ℝ) :
    HasDerivAt (fun x => forwardBranchCurrent IsF VT x)
      (IsF / VT * Real.exp (Vbe / VT)) Vbe := by
  have h1 : HasDerivAt (fun x : ℝ => x / VT) (1 / VT) Vbe :=
    (hasDerivAt_id Vbe).div_const VT
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (x / VT))
      (Real.exp (Vbe / VT) * (1 / VT)) Vbe := h1.exp
  have h3 : HasDerivAt (fun x : ℝ => Real.exp (x / VT) - 1)
      (Real.exp (Vbe / VT) * (1 / VT)) Vbe := h2.sub_const 1
  have h4 : HasDerivAt (fun x : ℝ => IsF * (Real.exp (x / VT) - 1))
      (IsF * (Real.exp (Vbe / VT) * (1 / VT))) Vbe := h3.const_mul IsF
  have heq : IsF * (Real.exp (Vbe / VT) * (1 / VT)) =
      IsF / VT * Real.exp (Vbe / VT) := by ring
  rw [heq] at h4
  exact h4

private theorem hasDerivAt_reverseBranch (IsR VT Vbc : ℝ) :
    HasDerivAt (fun y => reverseBranchCurrent IsR VT y)
      (IsR / VT * Real.exp (Vbc / VT)) Vbc := by
  have h1 : HasDerivAt (fun y : ℝ => y / VT) (1 / VT) Vbc :=
    (hasDerivAt_id Vbc).div_const VT
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (y / VT))
      (Real.exp (Vbc / VT) * (1 / VT)) Vbc := h1.exp
  have h3 : HasDerivAt (fun y : ℝ => Real.exp (y / VT) - 1)
      (Real.exp (Vbc / VT) * (1 / VT)) Vbc := h2.sub_const 1
  have h4 : HasDerivAt (fun y : ℝ => IsR * (Real.exp (y / VT) - 1))
      (IsR * (Real.exp (Vbc / VT) * (1 / VT))) Vbc := h3.const_mul IsR
  have heq : IsR * (Real.exp (Vbc / VT) * (1 / VT)) =
      IsR / VT * Real.exp (Vbc / VT) := by ring
  rw [heq] at h4
  exact h4

/-- **Terminal current balance (KCL)** with emitter-out convention: `Ic + Ib - Ie = 0`. -/
lemma terminal_current_balance (IsF IsR alphaF alphaR VT Vbe Vbc : ℝ) :
    collectorCurrent IsF IsR alphaF VT Vbe Vbc + baseCurrent IsF IsR alphaF alphaR VT Vbe Vbc -
      emitterCurrent IsF IsR alphaR VT Vbe Vbc = 0 := by
  simp only [collectorCurrent, baseCurrent, emitterCurrent, forwardBranchCurrent,
    reverseBranchCurrent]
  ring

/-- All-zero biases give zero terminal currents. -/
lemma terminalCurrents_zero_bias (IsF IsR alphaF alphaR VT : ℝ) :
    collectorCurrent IsF IsR alphaF VT 0 0 = 0 ∧
      baseCurrent IsF IsR alphaF alphaR VT 0 0 = 0 ∧
      emitterCurrent IsF IsR alphaR VT 0 0 = 0 := by
  have hF := forwardBranchCurrent_zero IsF VT
  have hR := reverseBranchCurrent_zero IsR VT
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [collectorCurrent, baseCurrent, emitterCurrent, hF, hR] <;> ring

/-! ### Small-signal derivatives (positive thermal voltage) -/

/-- Transconductance `∂Ic/∂Vbe = alphaF * IsF / VT * exp (Vbe / VT)`. -/
lemma hasDerivAt_collectorCurrent_vbe (IsF IsR alphaF VT Vbe Vbc : ℝ) (_hVT : 0 < VT) :
    HasDerivAt (fun x => collectorCurrent IsF IsR alphaF VT x Vbc)
      (alphaF * IsF / VT * Real.exp (Vbe / VT)) Vbe := by
  have hF := hasDerivAt_forwardBranch IsF VT Vbe
  have hFc := hF.const_mul alphaF
  have h := hFc.sub_const (reverseBranchCurrent IsR VT Vbc)
  have heq : alphaF * (IsF / VT * Real.exp (Vbe / VT)) =
      alphaF * IsF / VT * Real.exp (Vbe / VT) := by ring
  rw [heq] at h
  exact h

/-- `∂Ic/∂Vbc = -(IsR / VT) * exp (Vbc / VT)`. -/
lemma hasDerivAt_collectorCurrent_vbc (IsF IsR alphaF VT Vbe Vbc : ℝ) (_hVT : 0 < VT) :
    HasDerivAt (fun y => collectorCurrent IsF IsR alphaF VT Vbe y)
      (-(IsR / VT) * Real.exp (Vbc / VT)) Vbc := by
  have hR := hasDerivAt_reverseBranch IsR VT Vbc
  have h := hR.const_sub (alphaF * forwardBranchCurrent IsF VT Vbe)
  have heq : -(IsR / VT * Real.exp (Vbc / VT)) =
      -(IsR / VT) * Real.exp (Vbc / VT) := by ring
  rw [heq] at h
  exact h

/-- `∂Ie/∂Vbe = IsF / VT * exp (Vbe / VT)`. -/
lemma hasDerivAt_emitterCurrent_vbe (IsF IsR alphaR VT Vbe Vbc : ℝ) (_hVT : 0 < VT) :
    HasDerivAt (fun x => emitterCurrent IsF IsR alphaR VT x Vbc)
      (IsF / VT * Real.exp (Vbe / VT)) Vbe := by
  have hF := hasDerivAt_forwardBranch IsF VT Vbe
  have h := hF.sub_const (alphaR * reverseBranchCurrent IsR VT Vbc)
  exact h

/-- `∂Ie/∂Vbc = -(alphaR * IsR / VT) * exp (Vbc / VT)`. -/
lemma hasDerivAt_emitterCurrent_vbc (IsF IsR alphaR VT Vbe Vbc : ℝ) (_hVT : 0 < VT) :
    HasDerivAt (fun y => emitterCurrent IsF IsR alphaR VT Vbe y)
      (-(alphaR * IsR / VT) * Real.exp (Vbc / VT)) Vbc := by
  have hR := hasDerivAt_reverseBranch IsR VT Vbc
  have hRm := hR.const_mul alphaR
  have h := hRm.const_sub (forwardBranchCurrent IsF VT Vbe)
  have heq : -(alphaR * (IsR / VT * Real.exp (Vbc / VT))) =
      -(alphaR * IsR / VT) * Real.exp (Vbc / VT) := by ring
  rw [heq] at h
  exact h

/-- Input conductance `∂Ib/∂Vbe = (1 - alphaF) * IsF / VT * exp (Vbe / VT)`. -/
lemma hasDerivAt_baseCurrent_vbe (IsF IsR alphaF alphaR VT Vbe Vbc : ℝ) (_hVT : 0 < VT) :
    HasDerivAt (fun x => baseCurrent IsF IsR alphaF alphaR VT x Vbc)
      ((1 - alphaF) * IsF / VT * Real.exp (Vbe / VT)) Vbe := by
  have hF := hasDerivAt_forwardBranch IsF VT Vbe
  have hFm := hF.const_mul (1 - alphaF)
  have h := hFm.add_const ((1 - alphaR) * reverseBranchCurrent IsR VT Vbc)
  have heq : (1 - alphaF) * (IsF / VT * Real.exp (Vbe / VT)) =
      (1 - alphaF) * IsF / VT * Real.exp (Vbe / VT) := by ring
  rw [heq] at h
  exact h

/-- `∂Ib/∂Vbc = (1 - alphaR) * IsR / VT * exp (Vbc / VT)`. -/
lemma hasDerivAt_baseCurrent_vbc (IsF IsR alphaF alphaR VT Vbe Vbc : ℝ) (_hVT : 0 < VT) :
    HasDerivAt (fun y => baseCurrent IsF IsR alphaF alphaR VT Vbe y)
      ((1 - alphaR) * IsR / VT * Real.exp (Vbc / VT)) Vbc := by
  have hR := hasDerivAt_reverseBranch IsR VT Vbc
  have hRm := hR.const_mul (1 - alphaR)
  have h := hRm.const_add ((1 - alphaF) * forwardBranchCurrent IsF VT Vbe)
  have heq : (1 - alphaR) * (IsR / VT * Real.exp (Vbc / VT)) =
      (1 - alphaR) * IsR / VT * Real.exp (Vbc / VT) := by ring
  rw [heq] at h
  exact h

/-- Exact transconductance in terms of terminal quantities, any region:
`gm * VT = Ic + R + alphaF * IsF`. -/
lemma collectorTransconductance_mul_thermalVoltage (IsF IsR alphaF VT Vbe Vbc : ℝ)
    (hVT : 0 < VT) :
    alphaF * IsF / VT * Real.exp (Vbe / VT) * VT =
      collectorCurrent IsF IsR alphaF VT Vbe Vbc + reverseBranchCurrent IsR VT Vbc +
        alphaF * IsF := by
  have hVT' : VT ≠ 0 := ne_of_gt hVT
  simp only [collectorCurrent, forwardBranchCurrent, reverseBranchCurrent]
  field_simp
  ring

/-- Forward-active boundary `Vbc = 0`: `gm = (Ic + alphaF * IsF) / VT` exactly
(the precise form of the textbook `gm ≈ Ic / VT`). -/
lemma collectorTransconductance_of_vbc_zero (IsF IsR alphaF VT Vbe : ℝ) (hVT : 0 < VT) :
    alphaF * IsF / VT * Real.exp (Vbe / VT) =
      (collectorCurrent IsF IsR alphaF VT Vbe 0 + alphaF * IsF) / VT := by
  have hVT' : VT ≠ 0 := ne_of_gt hVT
  have hR := reverseBranchCurrent_zero IsR VT
  simp only [collectorCurrent, forwardBranchCurrent, hR]
  field_simp
  ring

/-! ### Bias-region examples -/

/-- Forward active (`Vbe > 0`, `Vbc < 0`): collector and emitter currents are positive.
(The base current's sign is not determined here: `R < 0` can dominate.) -/
lemma forwardActive_currents_pos (IsF IsR alphaF alphaR VT Vbe Vbc : ℝ) (hVT : 0 < VT)
    (hIsF : 0 < IsF) (hIsR : 0 < IsR) (hαF : 0 < alphaF) (hαR : 0 < alphaR)
    (hVbe : 0 < Vbe) (hVbc : Vbc < 0) :
    0 < collectorCurrent IsF IsR alphaF VT Vbe Vbc ∧
      0 < emitterCurrent IsF IsR alphaR VT Vbe Vbc := by
  have hF := forwardBranchCurrent_pos_of_pos IsF VT Vbe hVT hIsF hVbe
  have hR := reverseBranchCurrent_neg_of_neg IsR VT Vbc hVT hIsR hVbc
  have hαFF := mul_pos hαF hF
  have hαRR := mul_neg_of_pos_of_neg hαR hR
  simp only [collectorCurrent, emitterCurrent]
  constructor <;> linarith

/-- At `Vbc = 0`: `Ic = alphaF * Ie` and `Ib = (1 - alphaF) * Ie`. -/
lemma collector_eq_alphaF_mul_emitter_of_vbc_zero (IsF IsR alphaF alphaR VT Vbe : ℝ) :
    collectorCurrent IsF IsR alphaF VT Vbe 0 = alphaF * emitterCurrent IsF IsR alphaR VT Vbe 0 ∧
      baseCurrent IsF IsR alphaF alphaR VT Vbe 0 =
        (1 - alphaF) * emitterCurrent IsF IsR alphaR VT Vbe 0 := by
  have hR := reverseBranchCurrent_zero IsR VT
  simp only [collectorCurrent, emitterCurrent, baseCurrent, hR]
  constructor <;> ring

/-- Reverse active (`Vbe < 0`, `Vbc > 0`): collector and emitter currents are negative. -/
lemma reverseActive_currents_neg (IsF IsR alphaF alphaR VT Vbe Vbc : ℝ) (hVT : 0 < VT)
    (hIsF : 0 < IsF) (hIsR : 0 < IsR) (hαF : 0 < alphaF) (hαR : 0 < alphaR)
    (hVbe : Vbe < 0) (hVbc : 0 < Vbc) :
    collectorCurrent IsF IsR alphaF VT Vbe Vbc < 0 ∧
      emitterCurrent IsF IsR alphaR VT Vbe Vbc < 0 := by
  have hF := forwardBranchCurrent_neg_of_neg IsF VT Vbe hVT hIsF hVbe
  have hR := reverseBranchCurrent_pos_of_pos IsR VT Vbc hVT hIsR hVbc
  have hαFF := mul_neg_of_pos_of_neg hαF hF
  have hαRR := mul_pos hαR hR
  simp only [collectorCurrent, emitterCurrent]
  constructor <;> linarith

/-- At `Vbe = 0`: `Ie = alphaR * Ic`. -/
lemma emitter_eq_alphaR_mul_collector_of_vbe_zero (IsF IsR alphaF alphaR VT Vbc : ℝ) :
    emitterCurrent IsF IsR alphaR VT 0 Vbc = alphaR * collectorCurrent IsF IsR alphaF VT 0 Vbc := by
  have hF := forwardBranchCurrent_zero IsF VT
  simp only [collectorCurrent, emitterCurrent, hF]
  ring

/-! ### Sign-error test: emitter-out value read as emitter-in, `Ib` fixed -/

/-- Using the emitter-out `Ie` in the all-inflow law `Ic + Ib + Ie` (no sign change),
with the independently defined `Ib`, leaves `2 * Ie` instead of `0`. -/
lemma collector_add_base_add_emitterOut_eq (IsF IsR alphaF alphaR VT Vbe Vbc : ℝ) :
    collectorCurrent IsF IsR alphaF VT Vbe Vbc + baseCurrent IsF IsR alphaF alphaR VT Vbe Vbc +
      emitterCurrent IsF IsR alphaR VT Vbe Vbc =
        2 * emitterCurrent IsF IsR alphaR VT Vbe Vbc := by
  simp only [collectorCurrent, baseCurrent, emitterCurrent, forwardBranchCurrent,
    reverseBranchCurrent]
  ring

/-- The mis-signed KCL fails at every forward-active operating point. -/
lemma collector_add_base_add_emitterOut_ne_zero_of_forwardActive
    (IsF IsR alphaF alphaR VT Vbe Vbc : ℝ) (hVT : 0 < VT) (hIsF : 0 < IsF) (hIsR : 0 < IsR)
    (hαR : 0 < alphaR) (hVbe : 0 < Vbe) (hVbc : Vbc < 0) :
    collectorCurrent IsF IsR alphaF VT Vbe Vbc + baseCurrent IsF IsR alphaF alphaR VT Vbe Vbc +
      emitterCurrent IsF IsR alphaR VT Vbe Vbc ≠ 0 := by
  have hF := forwardBranchCurrent_pos_of_pos IsF VT Vbe hVT hIsF hVbe
  have hR := reverseBranchCurrent_neg_of_neg IsR VT Vbc hVT hIsR hVbc
  have hαRR := mul_neg_of_pos_of_neg hαR hR
  have hIe : 0 < emitterCurrent IsF IsR alphaR VT Vbe Vbc := by
    simp only [emitterCurrent]
    linarith
  rw [collector_add_base_add_emitterOut_eq]
  have h2 : 0 < 2 * emitterCurrent IsF IsR alphaR VT Vbe Vbc := by linarith
  exact ne_of_gt h2

/-! ### Reciprocal parameterization -/

/-- **Reciprocal parameterization.** When the branch saturation currents satisfy
`alphaF * IsF = alphaR * IsR`, both derive from the single transport saturation
current `IS = alphaF * IsF`: `IsF = IS / alphaF` and `IsR = IS / alphaR`. The
collector and emitter-out currents then depend on `IsF`, `IsR` only through `IS`,
in transport form. This is a parameterization equivalence: it does not derive
reciprocity from device physics, it states what reciprocity means for the
currents. The `_of_transportSaturation` lemmas below use the parameterization
directly. -/
lemma reciprocal_parameterization (IsF IsR alphaF alphaR VT Vbe Vbc : ℝ)
    (_hVT : 0 < VT) (hαF : alphaF ≠ 0) (hαR : alphaR ≠ 0) :
    alphaF * IsF = alphaR * IsR ↔
    ∃ IS : ℝ, IS = alphaF * IsF ∧ IsF = IS / alphaF ∧ IsR = IS / alphaR ∧
      collectorCurrent IsF IsR alphaF VT Vbe Vbc =
        IS * (Real.exp (Vbe / VT) - Real.exp (Vbc / VT)) -
          IS * ((1 - alphaR) / alphaR) * (Real.exp (Vbc / VT) - 1) ∧
      emitterCurrent IsF IsR alphaR VT Vbe Vbc =
        IS * (Real.exp (Vbe / VT) - Real.exp (Vbc / VT)) +
          IS * ((1 - alphaF) / alphaF) * (Real.exp (Vbe / VT) - 1) := by
  constructor
  · intro hrec
    have hIsR : IsR = alphaF * IsF / alphaR := by
      rw [eq_div_iff hαR]
      linear_combination -hrec
    refine ⟨alphaF * IsF, rfl, by field_simp, hIsR, ?_, ?_⟩
    · simp only [collectorCurrent, forwardBranchCurrent, reverseBranchCurrent]
      rw [hIsR]
      field_simp
      ring
    · simp only [emitterCurrent, forwardBranchCurrent, reverseBranchCurrent]
      rw [hIsR]
      field_simp
      ring
  · rintro ⟨IS, -, hF, hR, -, -⟩
    rw [hF, hR, mul_comm alphaF (IS / alphaF), div_mul_cancel₀ _ hαF,
      mul_comm alphaR (IS / alphaR), div_mul_cancel₀ _ hαR]


/-- With both saturation currents derived from one transport current `IS`
(`IsF = IS / alphaF`, `IsR = IS / alphaR`, the physical reciprocal
parameterization), the collector current takes transport form in `IS` alone. -/
lemma collectorCurrent_of_transportSaturation (IS alphaF alphaR VT Vbe Vbc : ℝ)
    (hαF : alphaF ≠ 0) (hαR : alphaR ≠ 0) :
    collectorCurrent (IS / alphaF) (IS / alphaR) alphaF VT Vbe Vbc =
      IS * (Real.exp (Vbe / VT) - Real.exp (Vbc / VT)) -
        IS * ((1 - alphaR) / alphaR) * (Real.exp (Vbc / VT) - 1) := by
  simp only [collectorCurrent, forwardBranchCurrent, reverseBranchCurrent]
  field_simp
  ring

/-- With both saturation currents derived from one transport current `IS`, the
emitter-out current takes transport form in `IS` alone. -/
lemma emitterCurrent_of_transportSaturation (IS alphaF alphaR VT Vbe Vbc : ℝ)
    (hαF : alphaF ≠ 0) (hαR : alphaR ≠ 0) :
    emitterCurrent (IS / alphaF) (IS / alphaR) alphaR VT Vbe Vbc =
      IS * (Real.exp (Vbe / VT) - Real.exp (Vbc / VT)) +
        IS * ((1 - alphaF) / alphaF) * (Real.exp (Vbe / VT) - 1) := by
  simp only [emitterCurrent, forwardBranchCurrent, reverseBranchCurrent]
  field_simp
  ring

/-- Under reciprocity `alphaF * IsF = alphaR * IsR`, the collector current in transport form
`Ic = IS (e^{Vbe/VT} - e^{Vbc/VT}) - IS (1 - alphaR) / alphaR (e^{Vbc/VT} - 1)`,
`IS = alphaF * IsF`. -/
lemma collectorCurrent_transport_form (IsF IsR alphaF alphaR VT Vbe Vbc : ℝ)
    (_hVT : 0 < VT) (hαR : 0 < alphaR) (hrec : alphaF * IsF = alphaR * IsR) :
    collectorCurrent IsF IsR alphaF VT Vbe Vbc =
      alphaF * IsF * (Real.exp (Vbe / VT) - Real.exp (Vbc / VT)) -
        alphaF * IsF * ((1 - alphaR) / alphaR) * (Real.exp (Vbc / VT) - 1) := by
  have hR : alphaR ≠ 0 := ne_of_gt hαR
  have hIsR : IsR = alphaF * IsF / alphaR := by
    rw [eq_div_iff hR]
    linear_combination -hrec
  simp only [collectorCurrent, forwardBranchCurrent, reverseBranchCurrent]
  rw [hIsR]
  field_simp
  ring

/-- Under reciprocity, the emitter-out current in transport form
`Ie = IS (e^{Vbe/VT} - e^{Vbc/VT}) + IS (1 - alphaF) / alphaF (e^{Vbe/VT} - 1)`. -/
lemma emitterCurrent_transport_form (IsF IsR alphaF alphaR VT Vbe Vbc : ℝ)
    (_hVT : 0 < VT) (hαF : 0 < alphaF) (hrec : alphaF * IsF = alphaR * IsR) :
    emitterCurrent IsF IsR alphaR VT Vbe Vbc =
      alphaF * IsF * (Real.exp (Vbe / VT) - Real.exp (Vbc / VT)) +
        alphaF * IsF * ((1 - alphaF) / alphaF) * (Real.exp (Vbe / VT) - 1) := by
  have hF : alphaF ≠ 0 := ne_of_gt hαF
  have hIsF : IsF = alphaR * IsR / alphaF := by
    rw [eq_div_iff hF]
    linear_combination hrec
  simp only [emitterCurrent, forwardBranchCurrent, reverseBranchCurrent]
  rw [hIsF]
  field_simp
  ring

end PhyslibExt.Electronics.EbersMollTerminalBalance
