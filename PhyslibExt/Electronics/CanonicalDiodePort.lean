/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.ArcPortSigns
public import PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves
public import PhyslibExt.Electronics.EbersMollTerminalBalance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ideal diode as a network branch port

## i. Overview

An ideal p-n junction diode carries the Shockley current
`Is * (exp (V / (n * VT)) - 1)` from anode to cathode at
anode-to-cathode voltage `V`, with saturation current `Is`, emission
coefficient `n` and thermal voltage `VT = kB * T / |q|`. The thermal
voltage uses the carrier-charge magnitude, so it does not depend on
the carrier sign, and it equals the Einstein ratio `D / mu` of
`ElectrostaticsAndLinearWaves`. The exponential law itself is the
junction branch law `EbersMollTerminalBalance.forwardBranchCurrent`
at the scale `n * VT`; this file declares no second junction or
transport model.

For positive parameters the current vanishes at zero bias, is
smooth with the stated small-signal conductance, is strictly
increasing, is positive exactly in forward bias, stays above `-Is`,
and tends to `-Is` in deep reverse bias. If `n`, `T` or `q` is zero
the scale vanishes and the formula collapses to zero current, so
those premises cannot be dropped.

A diode occupies a network branch in either orientation. With the
electrical incidence of `ArcPortSigns` (tail `+1`, head `-1`) the
orientation sign `s` of the anode is `+1` when the anode is the
branch tail and `-1` when it is the head, and the passive branch
current is `s * I_D (s * v)`. With branch voltages defined from node
potentials, the physical anode current is `I_D (phi a - phi c)` in
both orientations, and reversing the branch together with its
voltage and current describes the same diode.

## ii. Key results

- `einstein_ratio_eq_thermalVoltage`: the thermal voltage is the
  Einstein ratio `D / mu`.
- `hasDerivAt_diodeCurrent`: the small-signal conductance
  `Is / (n * VT) * exp (V / (n * VT))`.
- `tendsto_diodeCurrent_atBot`: the reverse saturation limit `-Is`.
- `canonicalDiodePort_correct`: the headline statement, combining the
  device law properties with the orientation-independent anode
  current and branch reversal.

## iii. Table of contents

- A. Thermal voltage
- B. Diode current law
- C. Diode branches in a network
- D. Headline statement

## iv. References

- W. Shockley, "The theory of p-n junctions in semiconductors and
  p-n junction transistors", *Bell System Technical Journal* 28
  (1949), 435-489: the ideal junction current law.
- S. M. Sze and K. K. Ng, *Physics of Semiconductor Devices*, third
  edition, Wiley, 2007: the ideality factor, the thermal voltage and
  the Einstein relation.
- L. O. Chua, C. A. Desoer and E. S. Kuh, *Linear and Nonlinear
  Circuits*, McGraw-Hill, 1987: two-terminal resistors on oriented
  branches and the passive sign convention.
-/

@[expose] public section

namespace PhyslibExt.Electronics.CanonicalDiodePort

open Matrix

/-! ## A. Thermal voltage -/

/-- Thermal voltage `VT = kB * T / |q|`. The denominator is the carrier-charge
magnitude `|q|`, never the signed carrier charge `q`. Here `kB` is the coordinate
of the positive Boltzmann constant in the chosen coherent unit system. -/
noncomputable def thermalVoltage (kB T q : ℝ) : ℝ := kB * T / |q|

/-- The thermal voltage is positive for positive `kB`, `T` and nonzero carrier
charge of either sign. -/
lemma thermalVoltage_pos {kB T q : ℝ} (hkB : 0 < kB) (hT : 0 < T) (hq : q ≠ 0) :
    0 < thermalVoltage kB T q := by
  unfold thermalVoltage
  exact div_pos (mul_pos hkB hT) (abs_pos.mpr hq)

/-- The thermal voltage does not depend on the carrier sign. -/
lemma thermalVoltage_neg_charge (kB T q : ℝ) :
    thermalVoltage kB T (-q) = thermalVoltage kB T q := by
  simp [thermalVoltage]

/-- The thermal voltage is the canonical Einstein ratio `D / mu` of the
dilute-carrier transport model; it is a consumer of that model, not a second one. -/
theorem einstein_ratio_eq_thermalVoltage {mu kB T q : ℝ} (hmu : mu ≠ 0) (hq : q ≠ 0) :
    PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves.diffusionCoeff mu kB T q / mu =
      thermalVoltage kB T q :=
  PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves.einstein_ratio hmu hq

/-! ## B. Diode current law -/

/-- Ideal Shockley diode current from anode to cathode at anode-to-cathode
voltage `V`, with saturation current `Is` and emission coefficient `n`:
`Is * (exp (V / (n * VT)) - 1)`. This reuses the exponential junction law
`EbersMollTerminalBalance.forwardBranchCurrent` with the scale `n * VT`; no second
exponential law or transport model is declared. -/
noncomputable def diodeCurrent (Is n kB T q V : ℝ) : ℝ :=
  PhyslibExt.Electronics.EbersMollTerminalBalance.forwardBranchCurrent Is
    (n * thermalVoltage kB T q) V

/-- Zero bias: no current. -/
lemma diodeCurrent_zero (Is n kB T q : ℝ) : diodeCurrent Is n kB T q 0 = 0 := by
  simp [diodeCurrent,
    PhyslibExt.Electronics.EbersMollTerminalBalance.forwardBranchCurrent]

/-- Derivative of the diode current in the anode-to-cathode voltage (small-signal
conductance). -/
theorem hasDerivAt_diodeCurrent (Is n kB T q V : ℝ) :
    HasDerivAt (diodeCurrent Is n kB T q)
      (Is / (n * thermalVoltage kB T q) * Real.exp (V / (n * thermalVoltage kB T q))) V := by
  have h1 : HasDerivAt (fun x : ℝ => x / (n * thermalVoltage kB T q))
      (1 / (n * thermalVoltage kB T q)) V :=
    (hasDerivAt_id V).div_const _
  have h4 : HasDerivAt (fun x : ℝ => Is * (Real.exp (x / (n * thermalVoltage kB T q)) - 1))
      (Is * (Real.exp (V / (n * thermalVoltage kB T q)) * (1 / (n * thermalVoltage kB T q))))
      V :=
    (h1.exp.sub_const _).const_mul _
  change HasDerivAt (fun x : ℝ => Is * (Real.exp (x / (n * thermalVoltage kB T q)) - 1))
    (Is / (n * thermalVoltage kB T q) * Real.exp (V / (n * thermalVoltage kB T q))) V
  convert h4 using 1
  ring

/-- With positive saturation current, emission coefficient, `kB`, `T` and nonzero
carrier charge, the diode current is strictly increasing in voltage. -/
lemma strictMono_diodeCurrent {Is n kB T q : ℝ} (hIs : 0 < Is) (hn : 0 < n) (hkB : 0 < kB)
    (hT : 0 < T) (hq : q ≠ 0) : StrictMono (diodeCurrent Is n kB T q) := by
  have hc : 0 < n * thermalVoltage kB T q := mul_pos hn (thermalVoltage_pos hkB hT hq)
  intro a b hab
  change Is * (Real.exp (a / (n * thermalVoltage kB T q)) - 1) <
    Is * (Real.exp (b / (n * thermalVoltage kB T q)) - 1)
  refine mul_lt_mul_of_pos_left ?_ hIs
  rw [sub_lt_sub_iff_right, Real.exp_lt_exp, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_right hab (inv_pos.mpr hc)

/-- Forward bias conducts anode to cathode; reverse bias gives negative current. -/
lemma diodeCurrent_pos_iff {Is n kB T q V : ℝ} (hIs : 0 < Is) (hn : 0 < n) (hkB : 0 < kB)
    (hT : 0 < T) (hq : q ≠ 0) : 0 < diodeCurrent Is n kB T q V ↔ 0 < V := by
  have hc : 0 < n * thermalVoltage kB T q := mul_pos hn (thermalVoltage_pos hkB hT hq)
  change 0 < Is * (Real.exp (V / (n * thermalVoltage kB T q)) - 1) ↔ 0 < V
  rw [mul_pos_iff_of_pos_left hIs, sub_pos, Real.one_lt_exp_iff, div_pos_iff_of_pos_right hc]

/-- The reverse current never reaches the saturation current. The bound itself
needs only `0 < Is`; the other premises place it in the physical regime, where the
scale `n * VT` is positive. -/
lemma neg_saturation_lt_diodeCurrent {Is n kB T q : ℝ} (V : ℝ) (hIs : 0 < Is) (hn : 0 < n)
    (hkB : 0 < kB) (hT : 0 < T) (hq : q ≠ 0) : -Is < diodeCurrent Is n kB T q V := by
  have _ : 0 < n * thermalVoltage kB T q := mul_pos hn (thermalVoltage_pos hkB hT hq)
  have hexp : 0 < Real.exp (V / (n * thermalVoltage kB T q)) := Real.exp_pos _
  change -Is < Is * (Real.exp (V / (n * thermalVoltage kB T q)) - 1)
  have hpos : 0 < Is * Real.exp (V / (n * thermalVoltage kB T q)) := mul_pos hIs hexp
  linarith [mul_sub_one Is (Real.exp (V / (n * thermalVoltage kB T q)))]

/-- Reverse saturation limit: as the voltage tends to minus infinity the current
tends to `-Is`. -/
theorem tendsto_diodeCurrent_atBot {Is n kB T q : ℝ} (hn : 0 < n) (hkB : 0 < kB) (hT : 0 < T)
    (hq : q ≠ 0) :
    Filter.Tendsto (diodeCurrent Is n kB T q) Filter.atBot (nhds (-Is)) := by
  have hc : 0 < n * thermalVoltage kB T q := mul_pos hn (thermalVoltage_pos hkB hT hq)
  have h1 : Filter.Tendsto (fun V : ℝ => V / (n * thermalVoltage kB T q)) Filter.atBot
      Filter.atBot :=
    Filter.tendsto_id.atBot_div_const hc
  have h4 : Filter.Tendsto (diodeCurrent Is n kB T q) Filter.atBot (nhds (Is * (0 - 1))) :=
    ((Real.tendsto_exp_atBot.comp h1).sub_const _).const_mul _
  rwa [zero_sub, mul_neg_one] at h4

/-- Invalid division cases: with `n = 0`, `T = 0` or `q = 0` the scale
`n * VT` vanishes and the formula collapses to the zero current, so the positivity
premises above cannot be dropped. -/
lemma diodeCurrent_eq_zero_of_invalid {Is n kB T q : ℝ} (h : n = 0 ∨ T = 0 ∨ q = 0) :
    diodeCurrent Is n kB T q = fun _ => 0 := by
  funext V
  have hc : n * thermalVoltage kB T q = 0 := by
    rcases h with rfl | rfl | rfl
    · simp
    · simp [thermalVoltage]
    · simp [thermalVoltage]
  change Is * (Real.exp (V / (n * thermalVoltage kB T q)) - 1) = 0
  rw [hc]
  simp

/-! ## C. Diode branches in a network -/

/-- A diode with anode at node `a` and cathode at node `c` occupies network
branch `e` (in either orientation), and the passive branch current `i e`
(tail to head) is `s * diodeCurrent (s * v e)`, where
`s = ArcPortSigns.electricalIncidence tail head a e` is `+1` when the anode is the
branch tail and `-1` when the anode is the branch head. -/
def DiodeBranch {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (Is n kB T q : ℝ) (tail head : E → V) (a c : V) (e : E)
    (v i : E → ℝ) : Prop :=
  ((tail e = a ∧ head e = c) ∨ (tail e = c ∧ head e = a)) ∧
    i e = PhyslibExt.Circuits.ArcPortSigns.electricalIncidence tail head a e *
      diodeCurrent Is n kB T q
        (PhyslibExt.Circuits.ArcPortSigns.electricalIncidence tail head a e * v e)

/-- Terminal direction: with branch voltages defined from node potentials, the
physical anode-to-cathode current `s * i e` of a diode branch is the diode current
at `phi a - phi c`, whichever way the branch is oriented. -/
lemma anodeCurrent_of_diodeBranch {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] {Is n kB T q : ℝ} {tail head : E → V} {a c : V} {e : E}
    {phi : V → ℝ} {v i : E → ℝ} (hac : a ≠ c)
    (hKVL : v = (PhyslibExt.Circuits.ArcPortSigns.electricalIncidence tail head).transpose *ᵥ phi)
    (h : DiodeBranch Is n kB T q tail head a c e v i) :
    PhyslibExt.Circuits.ArcPortSigns.electricalIncidence tail head a e * i e =
      diodeCurrent Is n kB T q (phi a - phi c) := by
  obtain ⟨hor, hi⟩ := h
  have hca : c ≠ a := Ne.symm hac
  have hve :=
    PhyslibExt.Circuits.ArcPortSigns.branchVoltage_eq_tail_sub_head tail head phi v hKVL e
  rw [hi]
  rcases hor with ⟨hte, hhe⟩ | ⟨hte, hhe⟩
  · have hs : PhyslibExt.Circuits.ArcPortSigns.electricalIncidence tail head a e = 1 := by
      simp [PhyslibExt.Circuits.ArcPortSigns.electricalIncidence_apply, hte, hhe, hca]
    rw [hs, hve, hte, hhe]
    simp
  · have hs : PhyslibExt.Circuits.ArcPortSigns.electricalIncidence tail head a e = -1 := by
      simp [PhyslibExt.Circuits.ArcPortSigns.electricalIncidence_apply, hte, hhe, hca]
    rw [hs, hve, hte, hhe]
    have harg : (-1 : ℝ) * (phi c - phi a) = phi a - phi c := by ring
    rw [harg]
    ring

/-- Branch reversal: reversing branch `e` together with its voltage and current
keeps the same physical diode (anode `a`, cathode `c`) on that branch. -/
lemma diodeBranch_reverse {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] {Is n kB T q : ℝ} {tail head : E → V} {a c : V} {e : E} {v i : E → ℝ}
    (h : DiodeBranch Is n kB T q tail head a c e v i) :
    DiodeBranch Is n kB T q (Function.update tail e (head e)) (Function.update head e (tail e))
      a c e (Function.update v e (-v e)) (Function.update i e (-i e)) := by
  obtain ⟨hor, hi⟩ := h
  have hs' : PhyslibExt.Circuits.ArcPortSigns.electricalIncidence
        (Function.update tail e (head e)) (Function.update head e (tail e)) a e =
      -PhyslibExt.Circuits.ArcPortSigns.electricalIncidence tail head a e := by
    rw [PhyslibExt.Circuits.ArcPortSigns.electricalIncidence_apply,
      PhyslibExt.Circuits.ArcPortSigns.electricalIncidence_apply,
      Function.update_self, Function.update_self]
    ring
  refine ⟨?_, ?_⟩
  · simp only [Function.update_self]
    rcases hor with ⟨hte, hhe⟩ | ⟨hte, hhe⟩
    · exact Or.inr ⟨hhe, hte⟩
    · exact Or.inl ⟨hhe, hte⟩
  · simp only [Function.update_self]
    rw [hs', neg_mul_neg, hi]
    ring

/-! ## D. Headline statement -/

/-- Headline: the Shockley law, adapted to thermal voltage `kB * T / |q|` and to
network terminal directions, is positive-scaled, vanishes at zero bias, has the
stated derivative, is strictly increasing, is bounded below by `-Is` with that
reverse limit, and gives an orientation-independent anode-to-cathode current that
survives branch reversal. -/
theorem canonicalDiodePort_correct {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] {Is n kB T q : ℝ} (hIs : 0 < Is) (hn : 0 < n) (hkB : 0 < kB)
    (hT : 0 < T) (hq : q ≠ 0) {tail head : E → V} {a c : V} {e : E} {phi : V → ℝ}
    {v i : E → ℝ} (hac : a ≠ c)
    (hKVL : v = (PhyslibExt.Circuits.ArcPortSigns.electricalIncidence tail head).transpose *ᵥ phi)
    (h : DiodeBranch Is n kB T q tail head a c e v i) :
    0 < thermalVoltage kB T q ∧
      thermalVoltage kB T (-q) = thermalVoltage kB T q ∧
      diodeCurrent Is n kB T q 0 = 0 ∧
      (∀ x, HasDerivAt (diodeCurrent Is n kB T q)
        (Is / (n * thermalVoltage kB T q) * Real.exp (x / (n * thermalVoltage kB T q))) x) ∧
      StrictMono (diodeCurrent Is n kB T q) ∧
      (∀ x, 0 < diodeCurrent Is n kB T q x ↔ 0 < x) ∧
      (∀ x, -Is < diodeCurrent Is n kB T q x) ∧
      Filter.Tendsto (diodeCurrent Is n kB T q) Filter.atBot (nhds (-Is)) ∧
      PhyslibExt.Circuits.ArcPortSigns.electricalIncidence tail head a e * i e =
        diodeCurrent Is n kB T q (phi a - phi c) ∧
      DiodeBranch Is n kB T q (Function.update tail e (head e))
        (Function.update head e (tail e)) a c e (Function.update v e (-v e))
        (Function.update i e (-i e)) :=
  ⟨thermalVoltage_pos hkB hT hq, thermalVoltage_neg_charge _ _ _,
    diodeCurrent_zero _ _ _ _ _, fun x => hasDerivAt_diodeCurrent _ _ _ _ _ x,
    strictMono_diodeCurrent hIs hn hkB hT hq,
    fun _ => diodeCurrent_pos_iff hIs hn hkB hT hq,
    fun x => neg_saturation_lt_diodeCurrent x hIs hn hkB hT hq,
    tendsto_diodeCurrent_atBot hn hkB hT hq, anodeCurrent_of_diodeBranch hac hKVL h,
    diodeBranch_reverse h⟩

end PhyslibExt.Electronics.CanonicalDiodePort
