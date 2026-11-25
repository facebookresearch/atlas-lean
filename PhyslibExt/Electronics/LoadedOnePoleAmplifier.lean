/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import PhyslibExt.Electronics.FiniteGainFeedback
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Loaded one-pole amplifier

## i. Overview

A unilateral one-pole amplifier with open-loop response
`A(s) = A0 / (1 + s / wp)` is driven through a source divider
`a = Rin / (Rs + Rin)` and drives a load through a load divider
`b = RL / (Ro + RL)`. The feedback error is
`a * vi - beta * vo`. The amplifier's unloaded output `vamp`,
before the load divider, obeys
`vamp = A(s) * (a * vi - beta * vo)`, and the loaded output is
`vo = b * vamp`, with feedback sensing the loaded output. Clearing the
two denominators that occur in these equations gives the loaded
closed-loop transfer
`G(s) = a * b * A0 / (1 + s / wp + beta * b * A0)`, valid away from
the two denominator zeros: the open-loop denominator zero, where
`1 + s / wp = 0`, and the loaded denominator zero, where
`1 + s / wp + beta * b * A0 = 0`. The loaded denominator vanishes
at `s = -wp * (1 + beta * b * A0)`; this is a zero of the transfer
denominator, and it is not claimed to be an uncancelled pole of
the transfer for every parameter choice (with `a = 0`, for
instance, the transfer is identically zero). Under the positive
sign hypotheses stated below, that denominator zero lies in the
open left half-plane, and the denominator is nonzero at every
point of the closed right half-plane. At `s = 0` the transfer
expression equals the real expression
`a * b * A0 / (1 + beta * b * A0)` for every parameter choice,
since both use the same division; this real number is the loaded
DC gain only when `1 + beta * b * A0 ≠ 0`, and the signal-level
DC statement carries that hypothesis together with `wp ≠ 0`. The
DC gain factors as the source divider times the canonical
closed-loop gain of the load-referred open-loop gain `b * A0`.
Parasitic poles, nonlinear rails and frequency-dependent loading
are not modeled.

## ii. Key results

- `output_eq_loadedTransfer_mul_input`: any unloaded and loaded
  output signals satisfying the two model equations, away from both
  denominator zeros and with `wp ≠ 0`, satisfy
  `vo = G(s) * vi` for the loaded transfer `G`.
- `output_eq_loadedDcGain_mul_input`: at `s = 0`, with `wp ≠ 0`
  and `1 + beta * b * A0 ≠ 0`, any signals satisfying the two model
  equations satisfy `vo = loadedDcGain A0 beta a b * vi`.
- `loadedDcGain_eq_sourceDivider_mul_closedLoopGain`: the loaded
  DC gain is the source divider times the canonical closed-loop
  gain `closedLoopGain (b * A0) beta`.
- `loadedDcGain_pos_and_lt`: under positive signs the loaded DC
  gain is positive and below the divider-scaled ideal gain
  `a / beta`.
- `denominator_eq_zero_iff`: for `wp > 0`, the loaded transfer
  denominator vanishes exactly at the cast of
  `closedLoopPole wp beta b A0`.
- `denominator_ne_zero_of_re_nonneg`: under positive signs the
  loaded denominator is nonzero at every point with nonnegative
  real part, by comparing real parts at a hypothetical zero.

## iii. Table of contents

- A. Source and load dividers
- B. Open-loop and loaded transfer
- C. Direct-current gain
- D. Denominator zero and stability
- E. Lossless dividers and a concrete example

## iv. References

- A. S. Sedra and K. C. Smith, *Microelectronic Circuits*, eighth
  edition, Oxford University Press, 2020: feedback amplifier
  analysis with finite open-loop gain, source and load divider
  effects on the closed-loop gain, and the one-pole closed-loop
  response whose denominator zero moves with the loop gain.

## A. Source and load dividers
-/

@[expose] public section

namespace PhyslibExt.Electronics.LoadedOnePoleAmplifier

/-- The source divider `Rin / (Rs + Rin)`. -/
noncomputable def sourceDivider (Rs Rin : ℝ) : ℝ :=
  Rin / (Rs + Rin)

/-- The load divider `RL / (Ro + RL)`. -/
noncomputable def loadDivider (Ro RL : ℝ) : ℝ :=
  RL / (Ro + RL)

/-- The source divider lies in `(0, 1]` for positive input resistance and
nonnegative source resistance. -/
lemma sourceDivider_pos_and_le_one (Rs Rin : ℝ) (hRin : 0 < Rin)
    (hRs : 0 ≤ Rs) :
    0 < sourceDivider Rs Rin ∧ sourceDivider Rs Rin ≤ 1 := by
  unfold sourceDivider
  have hsum : 0 < Rs + Rin := add_pos_of_nonneg_of_pos hRs hRin
  constructor
  · exact div_pos hRin hsum
  · rw [div_le_one hsum]
    exact le_add_of_nonneg_left hRs

/-- The load divider lies in `(0, 1]` for positive load resistance and
nonnegative output resistance. -/
lemma loadDivider_pos_and_le_one (Ro RL : ℝ) (hRL : 0 < RL)
    (hRo : 0 ≤ Ro) :
    0 < loadDivider Ro RL ∧ loadDivider Ro RL ≤ 1 := by
  unfold loadDivider
  have hsum : 0 < Ro + RL := add_pos_of_nonneg_of_pos hRo hRL
  constructor
  · exact div_pos hRL hsum
  · rw [div_le_one hsum]
    exact le_add_of_nonneg_left hRo

/-! ## B. Open-loop and loaded transfer -/

/-- The one-pole open-loop response `A0 / (1 + s / wp)`. -/
noncomputable def openLoopGain (A0 wp : ℝ) (s : ℂ) : ℂ :=
  (A0 : ℂ) / (1 + s / (wp : ℂ))

/-- The loaded closed-loop transfer
`a * b * A0 / (1 + s / wp + beta * b * A0)`. -/
noncomputable def loadedTransfer (A0 wp beta a b : ℝ) (s : ℂ) : ℂ :=
  ((a * b * A0 : ℝ) : ℂ) / (1 + s / (wp : ℂ) + ((beta * b * A0 : ℝ) : ℂ))

/-- **Loaded closed-loop transfer.** Any unloaded and loaded output
signals obeying `vamp = A(s) * (a * vi - beta * vo)` and
`vo = b * vamp`, where `a * vi - beta * vo` is the feedback error,
away from both denominator zeros (the open-loop denominator zero, where
`1 + s / wp = 0`, and the loaded denominator zero, where
`1 + s / wp + beta * b * A0 = 0`) and with `wp ≠ 0`, satisfy
`vo = G(s) * vi` for the loaded transfer `G`. The proof clears the
open-loop denominator using `1 + s / wp ≠ 0`, rearranges the two
model equations, and divides by the loaded denominator. -/
theorem output_eq_loadedTransfer_mul_input (A0 wp beta a b : ℝ) (s vi vo vamp : ℂ)
    (hwp : (wp : ℂ) ≠ 0)
    (hopen : 1 + s / (wp : ℂ) ≠ 0)
    (hden : 1 + s / (wp : ℂ) + ((beta * b * A0 : ℝ) : ℂ) ≠ 0)
    (hvamp : vamp = openLoopGain A0 wp s * ((a : ℂ) * vi - (beta : ℂ) * vo))
    (hvo : vo = (b : ℂ) * vamp) :
    vo = loadedTransfer A0 wp beta a b s * vi := by
  unfold openLoopGain at hvamp
  unfold loadedTransfer
  have hcast1 : (((beta * b * A0 : ℝ)) : ℂ) = (beta : ℂ) * (b : ℂ) * (A0 : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
  have hcast2 : (((a * b * A0 : ℝ)) : ℂ) = (a : ℂ) * (b : ℂ) * (A0 : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
  have hvamp' : vamp * (1 + s / (wp : ℂ))
      = (A0 : ℂ) * ((a : ℂ) * vi - (beta : ℂ) * vo) := by
    rw [hvamp, div_mul_eq_mul_div, div_mul_cancel₀ _ hopen]
  have step1 : (b : ℂ) * (vamp * (1 + s / (wp : ℂ)))
      = (b : ℂ) * ((A0 : ℂ) * ((a : ℂ) * vi - (beta : ℂ) * vo)) := by
    rw [hvamp']
  have step2 : ((b : ℂ) * vamp) * (1 + s / (wp : ℂ))
      = (b : ℂ) * ((A0 : ℂ) * ((a : ℂ) * vi - (beta : ℂ) * vo)) := by
    calc ((b : ℂ) * vamp) * (1 + s / (wp : ℂ))
        = (b : ℂ) * (vamp * (1 + s / (wp : ℂ))) := by ring
      _ = (b : ℂ) * ((A0 : ℂ) * ((a : ℂ) * vi - (beta : ℂ) * vo)) := step1
  have key : vo * (1 + s / (wp : ℂ) + ((beta * b * A0 : ℝ) : ℂ))
      = ((a * b * A0 : ℝ) : ℂ) * vi := by
    rw [hcast1, hcast2, hvo]
    have step3 : ((b : ℂ) * vamp) * (1 + s / (wp : ℂ) + (beta : ℂ) * (b : ℂ) * (A0 : ℂ))
        = ((b : ℂ) * vamp) * (1 + s / (wp : ℂ))
          + ((b : ℂ) * vamp) * ((beta : ℂ) * (b : ℂ) * (A0 : ℂ)) := by ring
    rw [step3, step2, hvo]
    ring
  have hgoal : vo = ((a * b * A0 : ℝ) : ℂ) * vi
      / (1 + s / (wp : ℂ) + ((beta * b * A0 : ℝ) : ℂ)) := by
    rw [eq_div_iff hden]
    exact key
  rw [hgoal]
  ring

/-! ## C. Direct-current gain -/

/-- The loaded DC gain `a * b * A0 / (1 + beta * b * A0)` as a real number.
It is the physical DC gain only when `1 + beta * b * A0 ≠ 0`; at the
singular parameter choices the division is the totalized one and the
value carries no physical meaning. -/
noncomputable def loadedDcGain (A0 beta a b : ℝ) : ℝ :=
  a * b * A0 / (1 + beta * b * A0)

/-- At `s = 0` the loaded transfer expression is the cast of the real
loaded DC gain expression. This is an identity between the two
expressions for every parameter choice, because both use the same
division; it makes no physical claim at the singular parameters
where `1 + beta * b * A0 = 0`. The guarded signal-level statement is
`output_eq_loadedDcGain_mul_input`. -/
lemma loadedTransfer_zero (A0 wp beta a b : ℝ) :
    loadedTransfer A0 wp beta a b 0 = ((loadedDcGain A0 beta a b : ℝ) : ℂ) := by
  unfold loadedTransfer loadedDcGain
  simp only [zero_div, add_zero, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_one]

/-- **Loaded DC gain of the signal model.** At `s = 0`, with `wp ≠ 0`
and `1 + beta * b * A0 ≠ 0`, any unloaded and loaded output signals
obeying the two model equations satisfy
`vo = loadedDcGain A0 beta a b * vi`. The open-loop denominator is
`1` at `s = 0`, the loaded denominator reduces to
`1 + beta * b * A0`, and the transfer theorem then applies. -/
theorem output_eq_loadedDcGain_mul_input (A0 wp beta a b : ℝ) (vi vo vamp : ℂ)
    (hwp : (wp : ℂ) ≠ 0)
    (hdc : 1 + beta * b * A0 ≠ 0)
    (hvamp : vamp = openLoopGain A0 wp 0 * ((a : ℂ) * vi - (beta : ℂ) * vo))
    (hvo : vo = (b : ℂ) * vamp) :
    vo = ((loadedDcGain A0 beta a b : ℝ) : ℂ) * vi := by
  have hopen : 1 + (0 : ℂ) / (wp : ℂ) ≠ 0 := by
    rw [zero_div, add_zero]
    exact one_ne_zero
  have hden : 1 + (0 : ℂ) / (wp : ℂ) + ((beta * b * A0 : ℝ) : ℂ) ≠ 0 := by
    rw [zero_div, add_zero]
    exact_mod_cast hdc
  rw [← loadedTransfer_zero A0 wp beta a b]
  exact output_eq_loadedTransfer_mul_input A0 wp beta a b 0 vi vo vamp hwp hopen hden
    hvamp hvo

/-- **DC gain through the canonical finite-gain law.** The loaded DC gain
is the source divider times the canonical closed-loop gain of the
load-referred open-loop gain `b * A0`. This is a rearrangement of the
two real divisions after rewriting `1 + (b * A0) * beta` as
`1 + beta * b * A0`. -/
lemma loadedDcGain_eq_sourceDivider_mul_closedLoopGain (A0 beta a b : ℝ) :
    loadedDcGain A0 beta a b =
      a * PhyslibExt.Electronics.FiniteGainFeedback.closedLoopGain (b * A0) beta := by
  unfold loadedDcGain PhyslibExt.Electronics.FiniteGainFeedback.closedLoopGain
  have h : (1 : ℝ) + (b * A0) * beta = 1 + beta * b * A0 := by ring
  rw [h]
  ring

/-- The loaded DC gain is positive and below the divider-scaled ideal gain
`a / beta` under the stated positive signs. -/
theorem loadedDcGain_pos_and_lt (A0 beta a b : ℝ) (hA0 : 0 < A0)
    (hbeta : 0 < beta) (ha : 0 < a) (hb : 0 < b) :
    0 < loadedDcGain A0 beta a b ∧ loadedDcGain A0 beta a b < a / beta := by
  unfold loadedDcGain
  have hX : (0 : ℝ) < beta * b * A0 := mul_pos (mul_pos hbeta hb) hA0
  have hD : (0 : ℝ) < 1 + beta * b * A0 := add_pos zero_lt_one hX
  have hN : (0 : ℝ) < a * b * A0 := mul_pos (mul_pos ha hb) hA0
  constructor
  · exact div_pos hN hD
  · rw [div_lt_iff₀ hD, div_mul_eq_mul_div, lt_div_iff₀ hbeta]
    have h : a * (1 + beta * b * A0) = a + a * b * A0 * beta := by ring
    rw [h]
    exact lt_add_of_pos_left _ ha

/-! ## D. Denominator zero and stability -/

/-- The closed-loop pole location `-wp * (1 + beta * b * A0)` as a real
number; its cast to `ℂ` is the loaded denominator zero characterized
below. -/
noncomputable def closedLoopPole (wp beta b A0 : ℝ) : ℝ :=
  -wp * (1 + beta * b * A0)

/-- **Denominator zero characterization.** For `wp > 0`, the transfer
denominator vanishes exactly at the cast of the closed-loop pole
location. Both directions clear the denominator `wp` and rearrange. -/
theorem denominator_eq_zero_iff (wp beta b A0 : ℝ) (hwp : 0 < wp) (s : ℂ) :
    (1 + s / (wp : ℂ) + ((beta * b * A0 : ℝ) : ℂ) = 0) ↔
      s = ((closedLoopPole wp beta b A0 : ℝ) : ℂ) := by
  have hwp' : (wp : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hwp
  constructor
  · intro h
    have h1 : s / (wp : ℂ) = -(1 + ((beta * b * A0 : ℝ) : ℂ)) := by
      rw [eq_neg_iff_add_eq_zero]
      have h2 : s / (wp : ℂ) + (1 + ((beta * b * A0 : ℝ) : ℂ))
          = 1 + s / (wp : ℂ) + ((beta * b * A0 : ℝ) : ℂ) := by ring
      rw [h2, h]
    rw [div_eq_iff hwp'] at h1
    have hcast : (-(1 + ((beta * b * A0 : ℝ) : ℂ)) * (wp : ℂ))
        = (((closedLoopPole wp beta b A0 : ℝ)) : ℂ) := by
      unfold closedLoopPole
      push_cast
      ring
    rw [h1, hcast]
  · intro h
    rw [h]
    have h3 : (((closedLoopPole wp beta b A0 : ℝ)) : ℂ) / (wp : ℂ)
        = -(1 + ((beta * b * A0 : ℝ) : ℂ)) := by
      rw [div_eq_iff hwp']
      unfold closedLoopPole
      push_cast
      ring
    rw [h3]
    ring

/-- The closed-loop pole location is strictly negative under the stated
positive signs, so the denominator zero lies in the open left
half-plane. -/
theorem closedLoopPole_neg (wp beta b A0 : ℝ) (hwp : 0 < wp)
    (hbeta : 0 < beta) (hb : 0 < b) (hA0 : 0 < A0) :
    closedLoopPole wp beta b A0 < 0 := by
  unfold closedLoopPole
  have h1 : (0 : ℝ) < 1 + beta * b * A0 :=
    add_pos zero_lt_one (mul_pos (mul_pos hbeta hb) hA0)
  have h2 : -wp < (0 : ℝ) := neg_lt_zero.mpr hwp
  exact mul_neg_of_neg_of_pos h2 h1

/-- **No denominator zero in the closed right half-plane.** Under the
stated positive signs, the transfer denominator is nonzero at every
point with nonnegative real part. At a hypothetical zero the point
would equal the cast of a strictly negative real number, which
contradicts the sign of its real part. -/
theorem denominator_ne_zero_of_re_nonneg (A0 wp beta b : ℝ) (hA0 : 0 < A0)
    (hwp : 0 < wp) (hbeta : 0 < beta) (hb : 0 < b) (s : ℂ)
    (hs : 0 ≤ s.re) :
    1 + s / (wp : ℂ) + ((beta * b * A0 : ℝ) : ℂ) ≠ 0 := by
  intro h
  have hwp' : (wp : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hwp
  have h1 : s / (wp : ℂ) = -(1 + ((beta * b * A0 : ℝ) : ℂ)) := by
    rw [eq_neg_iff_add_eq_zero]
    have h2 : s / (wp : ℂ) + (1 + ((beta * b * A0 : ℝ) : ℂ))
        = 1 + s / (wp : ℂ) + ((beta * b * A0 : ℝ) : ℂ) := by ring
    rw [h2, h]
  rw [div_eq_iff hwp'] at h1
  have hcast : (-(1 + ((beta * b * A0 : ℝ) : ℂ)) * (wp : ℂ))
      = (((-(1 + beta * b * A0) * wp : ℝ)) : ℂ) := by
    push_cast
    ring
  have hre : s.re = (-(1 + beta * b * A0) * wp : ℝ) := by
    rw [h1, hcast, Complex.ofReal_re]
  have hpos : (0 : ℝ) < (1 + beta * b * A0) * wp :=
    mul_pos (add_pos zero_lt_one (mul_pos (mul_pos hbeta hb) hA0)) hwp
  have hneg : (-(1 + beta * b * A0) * wp : ℝ) < 0 := by
    have h3 : (-(1 + beta * b * A0) * wp : ℝ) = -((1 + beta * b * A0) * wp) := by
      ring
    rw [h3]
    exact neg_lt_zero.mpr hpos
  rw [hre] at hs
  exact not_le_of_gt hneg hs

/-! ## E. Lossless dividers and a concrete example -/

/-- With no source or output resistance, both dividers equal one. -/
lemma dividers_eq_one_of_no_source_output_resistance (Rin RL : ℝ)
    (hRin : 0 < Rin) (hRL : 0 < RL) :
    sourceDivider 0 Rin = 1 ∧ loadDivider 0 RL = 1 := by
  unfold sourceDivider loadDivider
  constructor
  · rw [zero_add, div_self (ne_of_gt hRin)]
  · rw [zero_add, div_self (ne_of_gt hRL)]

/-- At unit dividers the loaded transfer is the unloaded one-pole
closed-loop transfer. -/
lemma loadedTransfer_at_unit_dividers (A0 wp beta : ℝ) (s : ℂ) :
    loadedTransfer A0 wp beta 1 1 s =
      (A0 : ℂ) / (1 + s / (wp : ℂ) + ((beta * A0 : ℝ) : ℂ)) := by
  unfold loadedTransfer
  have h1 : (1 * 1 * A0 : ℝ) = A0 := by ring
  have h2 : (beta * 1 * A0 : ℝ) = beta * A0 := by ring
  rw [h1, h2]

/-- **Concrete loaded example.** Equal source and load resistances halve
both dividers; with `A0 = 10`, `beta = 1` and `wp = 2` the DC gain is
`5 / 12` and the pole location is `-12`. -/
lemma loaded_example :
    sourceDivider 1 1 = 1 / 2 ∧ loadDivider 1 1 = 1 / 2 ∧
      loadedTransfer 10 2 1 (1 / 2) (1 / 2) 0 = ((5 / 12 : ℝ) : ℂ) ∧
      closedLoopPole 2 1 (1 / 2) 10 = -12 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold sourceDivider
    norm_num
  · unfold loadDivider
    norm_num
  · rw [loadedTransfer_zero]
    congr 1
    unfold loadedDcGain
    norm_num
  · unfold closedLoopPole
    norm_num

end PhyslibExt.Electronics.LoadedOnePoleAmplifier
