/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PhyslibExt.Chemistry.FiniteEnsembles

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!

# Entropy, heat engines and the third law

Second-law bounds through Carnot efficiency, ideal-gas entropy changes, entropy of mixing and
absolute entropy with the third-law convention.

## i. Overview

Temperatures are absolute, `R` is the molar gas constant (a symbolic real parameter; no
numerical value is fixed), `n` is the amount of substance in mol and `cv` a constant molar heat
capacity. Each lemma states the positivity hypotheses it uses (`0 < T`, `0 < R`, `0 < n`,
`0 < cv`); the definitions and the purely algebraic identities hold for all real arguments, and
their physical reading is at positive values.

Junk values: the definitions are total, so outside its domain each returns a value fixed by
Lean's conventions (`x / 0 = 0`, `Real.log 0 = 0`, `Real.log (-x) = Real.log x`, and `0` for a
non-integrable interval integral). Such a value is not a physical quantity. Each definition's
docstring names its domain, and no lemma draws a physical conclusion from a junk value: the
lemmas that read a value physically have hypotheses that keep it in the domain (for
`absoluteEntropy`, integrability of `Cp t / t`, automatic at `T = 0`), and the remaining lemmas
about the definitions only rewrite a formula, so they hold on junk inputs too.

The physics inputs are carried as explicit hypotheses and definitions, never derived here.
The adiabatic relations of §A, the Clausius inequality (the second-law input, LAW), the
integrated ideal-gas entropy differential of §B and the third-law convention `S(0) = 0` of §D
are MODEL inputs. No entropy is derived from statistics (CH34 territory) and no Gibbs or
Helmholtz Legendre development is claimed (CH14 territory).

The entropy of mixing is `n * R` times the Shannon entropy
`Chemistry.FiniteEnsembles.shannonEntropy` of the mole fractions, so the Shannon-entropy API of
`PhyslibExt.Chemistry.FiniteEnsembles` (`shannonEntropy_nonneg`, `shannonEntropy_eq_zero_iff`)
applies to it directly; that module is the only non-Mathlib import. Proofs use `Real.log`
algebra (`Real.log_div`, `Real.log_mul`, `Real.log_rpow`), `Real.log_injOn_pos`,
`intervalIntegral.integral_hasDerivAt_right` and `Finset` sum lemmas.

## ii. Key results

- `carnotEfficiency`, `carnot_heat_pos` : `η = 1 - Tc / Th` and positivity of the
  isothermal heats.
- `carnot_volume_ratio` : the adiabatic legs force `V₂ / V₁ = V₃ / V₄`.
- `carnot_heat_ratio`, `carnot_cycle_efficiency` : positive heats with `Qc / Qh = Tc / Th` and
  `1 - Qc / Qh = carnotEfficiency Tc Th` for the reversible cycle.
- `engine_efficiency_le_carnotEfficiency`, `engine_efficiency_eq_carnotEfficiency` : the
  second-law bound for any engine and its equality case for reversible engines.
- `idealGasEntropyChange` : `ΔS = n * cv * log (T₂ / T₁) + n * R * log (V₂ / V₁)`.
- `idealGasEntropyChange_totalCV` : the no-double-counting `CV` form.
- `idealGasEntropyChange_add`, `idealGasEntropyChange_isothermal`,
  `idealGasEntropyChange_adiabatic`, `idealGasEntropyChange_symm` : additivity, the isothermal
  case, the reversible-adiabatic case and sign reversal.
- `entropyOfMixing`, `entropyOfMixing_eq_neg_sum` : `ΔS_mix = n * R * H(x)` with `H` the
  Shannon entropy, that is `-n * R * ∑ i, x i * log (x i)`.
- `moleFraction_le_one`, `entropyOfMixing_nonneg`, `entropyOfMixing_eq_zero_iff`,
  `entropyOfMixing_binary` : the mole-fraction bound, nonnegativity, the single-component
  equality case and the binary case.
- `absoluteEntropy` : `S(T) = ∫ t in 0..T, Cp t / t + ∑ transitions below T, ΔH / Tt`.
- `absoluteEntropy_zero`, `hasDerivAt_absoluteEntropy`, `absoluteEntropy_mono`,
  `absoluteEntropy_insert_of_lt` : the third-law convention, `S' = Cp / T`, monotonicity and the
  transition filter.

## iii. Table of contents

- A. Carnot efficiency and the second-law bound
- B. Ideal-gas entropy changes
- C. Entropy of mixing
- D. Absolute entropy and the third law

## iv. References

- MIT OpenCourseWare, 5.60 *Thermodynamics & Kinetics* (Spring 2008): reversible cycles,
  Carnot efficiency, the Clausius inequality, ideal-gas entropy changes, entropy of mixing,
  the third law.
- OpenStax *Chemistry 2e*, Ch. 16 (Thermodynamics): the second law, entropy, Gibbs energy
  (context only).
- IUPAC Green Book: entropy `S` in J/K, molar entropy in J/(mol·K), absolute temperature.

-/

@[expose] public section

namespace Chemistry.Thermodynamics

open scoped BigOperators Matrix Topology

/-!

## A. Carnot efficiency and the second-law bound

-/

/-- The Carnot efficiency `1 - Tc / Th` of a reversible engine operating between a cold
reservoir at absolute temperature `Tc` and a hot reservoir at absolute temperature `Th`.
Domain: `0 < Th`. At `Th = 0`, Lean's `x / 0 = 0` gives the junk value `1`, which is not an
efficiency; the lemmas that read it assume `0 < Th`, directly or through `0 < Tc < Th`. -/
noncomputable def carnotEfficiency (Tc Th : ℝ) : ℝ := 1 - Tc / Th

/-- An isothermal leg with heat `Q = n * R * T * log (V₂ / V₁)` absorbs positive heat
for an expansion leg: `0 < Q` needs `V₁ < V₂`. Applied to the hot leg (`V₁ < V₂`) and the
cold leg (`V₄ < V₃`, with the rejected heat counted positive). -/
lemma carnot_heat_pos {n R T V1 V2 : ℝ} (hn : 0 < n) (hR : 0 < R) (hT : 0 < T)
    (hV1 : 0 < V1) (hexp : V1 < V2) : 0 < n * R * T * Real.log (V2 / V1) := by
  have hL : 0 < Real.log (V2 / V1) := Real.log_pos ((one_lt_div hV1).mpr hexp)
  exact mul_pos (mul_pos (mul_pos hn hR) hT) hL

/-- The adiabatic legs of a reversible ideal-gas Carnot cycle force equal volume ratios:
from the MODEL hypotheses `Th * V₂ ^ k = Tc * V₃ ^ k` and `Tc * V₄ ^ k = Th * V₁ ^ k` with
`k = R / cv`, `V₂ / V₁ = V₃ / V₄`. The adiabatic relations themselves are model inputs, not
derived from the first law here. Route: `Real.log` of both relations (`Real.log_mul`,
`Real.log_rpow`), added (`linear_combination`), the factor `k ≠ 0` cancelled
(`mul_left_cancel₀`), and injectivity of `Real.log` on positives (`Real.log_injOn_pos`). -/
lemma carnot_volume_ratio {Tc Th V1 V2 V3 V4 R cv : ℝ}
    (hTc : 0 < Tc) (hT : Tc < Th)
    (hR : 0 < R) (hcv : 0 < cv)
    (hV1 : 0 < V1) (hV2 : 0 < V2) (hV3 : 0 < V3) (hV4 : 0 < V4)
    (had1 : Th * V2 ^ (R / cv) = Tc * V3 ^ (R / cv))
    (had2 : Tc * V4 ^ (R / cv) = Th * V1 ^ (R / cv)) :
    V2 / V1 = V3 / V4 := by
  have hTh : 0 < Th := lt_trans hTc hT
  have hk : R / cv ≠ 0 := div_ne_zero hR.ne' hcv.ne'
  have e1 := congrArg Real.log had1
  have e2 := congrArg Real.log had2
  rw [Real.log_mul hTh.ne' (Real.rpow_pos_of_pos hV2 _).ne',
    Real.log_mul hTc.ne' (Real.rpow_pos_of_pos hV3 _).ne',
    Real.log_rpow hV2, Real.log_rpow hV3] at e1
  rw [Real.log_mul hTc.ne' (Real.rpow_pos_of_pos hV4 _).ne',
    Real.log_mul hTh.ne' (Real.rpow_pos_of_pos hV1 _).ne',
    Real.log_rpow hV4, Real.log_rpow hV1] at e2
  have hfactor : (R / cv) * (Real.log V2 - Real.log V1)
      = (R / cv) * (Real.log V3 - Real.log V4) := by
    linear_combination e1 + e2
  have hsub : Real.log V2 - Real.log V1 = Real.log V3 - Real.log V4 :=
    mul_left_cancel₀ hk hfactor
  have hlog : Real.log (V2 / V1) = Real.log (V3 / V4) := by
    rw [Real.log_div hV2.ne' hV1.ne', Real.log_div hV3.ne' hV4.ne']
    exact hsub
  exact Real.log_injOn_pos (div_pos hV2 hV1) (div_pos hV3 hV4) hlog

/-- For the reversible cycle, both isothermal heats are positive and the rejected-to-absorbed
heat ratio equals the temperature ratio: with `Qh = n * R * Th * log (V₂ / V₁)` and
`Qc = n * R * Tc * log (V₃ / V₄)`, `0 < Qh ∧ 0 < Qc ∧ Qc / Qh = Tc / Th`. Positivity of
the heats needs the expansion hypotheses `V₁ < V₂` and `V₄ < V₃`. -/
lemma carnot_heat_ratio {Tc Th n R V1 V2 V3 V4 Qh Qc : ℝ}
    (hTc : 0 < Tc) (hT : Tc < Th)
    (hn : 0 < n) (hR : 0 < R)
    (hV1 : 0 < V1) (hV4 : 0 < V4)
    (hexp : V1 < V2) (hcomp : V4 < V3)
    (hV : V2 / V1 = V3 / V4)
    (hQh : Qh = n * R * Th * Real.log (V2 / V1))
    (hQc : Qc = n * R * Tc * Real.log (V3 / V4)) :
    0 < Qh ∧ 0 < Qc ∧ Qc / Qh = Tc / Th := by
  have hTh : 0 < Th := lt_trans hTc hT
  have hQhpos : 0 < Qh := by
    rw [hQh]
    exact carnot_heat_pos hn hR hTh hV1 hexp
  have hQcpos : 0 < Qc := by
    rw [hQc]
    exact carnot_heat_pos hn hR hTc hV4 hcomp
  have hL : 0 < Real.log (V2 / V1) := Real.log_pos ((one_lt_div hV1).mpr hexp)
  have hD : n * R * Th * Real.log (V2 / V1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hn.ne' hR.ne') hTh.ne') hL.ne'
  have hTh0 : Th ≠ 0 := hTh.ne'
  have hratio : Qc / Qh = Tc / Th := by
    rw [hQh, hQc, ← hV]
    field_simp
  exact ⟨hQhpos, hQcpos, hratio⟩

/-- The reversible ideal-gas Carnot cycle attains the Carnot efficiency: the full chain from
the adiabatic MODEL hypotheses through `carnot_volume_ratio` and `carnot_heat_ratio` gives
`1 - Qc / Qh = carnotEfficiency Tc Th`. -/
lemma carnot_cycle_efficiency {Tc Th n R V1 V2 V3 V4 Qh Qc cv : ℝ}
    (hTc : 0 < Tc) (hT : Tc < Th)
    (hn : 0 < n) (hR : 0 < R) (hcv : 0 < cv)
    (hV1 : 0 < V1) (hV2 : 0 < V2) (hV3 : 0 < V3) (hV4 : 0 < V4)
    (hexp : V1 < V2) (hcomp : V4 < V3)
    (had1 : Th * V2 ^ (R / cv) = Tc * V3 ^ (R / cv))
    (had2 : Tc * V4 ^ (R / cv) = Th * V1 ^ (R / cv))
    (hQh : Qh = n * R * Th * Real.log (V2 / V1))
    (hQc : Qc = n * R * Tc * Real.log (V3 / V4)) :
    1 - Qc / Qh = carnotEfficiency Tc Th := by
  have hV := carnot_volume_ratio hTc hT hR hcv hV1 hV2 hV3 hV4 had1 had2
  have hheat := carnot_heat_ratio hTc hT hn hR hV1 hV4 hexp hcomp hV hQh hQc
  rw [hheat.2.2]
  rfl

/-- The second-law bound: any engine between the same reservoirs, with heat absorbed `Qh`,
heat rejected `Qc`, work `W = Qh - Qc` (first law) and the Clausius inequality
`Qh / Th - Qc / Tc ≤ 0` as the second-law input (LAW), satisfies
`W / Qh ≤ carnotEfficiency Tc Th`. The Clausius inequality is a model hypothesis, not a
theorem derived in this module. -/
lemma engine_efficiency_le_carnotEfficiency {Qh Qc W Tc Th : ℝ}
    (hTc : 0 < Tc) (hTh : 0 < Th) (hQh : 0 < Qh)
    (hW : W = Qh - Qc) (hClausius : Qh / Th - Qc / Tc ≤ 0) :
    W / Qh ≤ carnotEfficiency Tc Th := by
  have h1 : Qh / Th ≤ Qc / Tc := by linarith
  have h2 : Qh * Tc ≤ Qc * Th := (div_le_div_iff₀ hTh hTc).mp h1
  have h3 : Tc / Th ≤ Qc / Qh := (div_le_div_iff₀ hTh hQh).mpr (by linarith)
  rw [hW, sub_div, div_self hQh.ne']
  unfold carnotEfficiency
  linarith

/-- A reversible engine attains the Carnot efficiency: with `W = Qh - Qc` and the Clausius
relation as an equality, `W / Qh = carnotEfficiency Tc Th`. -/
lemma engine_efficiency_eq_carnotEfficiency {Qh Qc W Tc Th : ℝ}
    (hTc : 0 < Tc) (hTh : 0 < Th) (hQh : 0 < Qh)
    (hW : W = Qh - Qc) (hClausius : Qh / Th - Qc / Tc = 0) :
    W / Qh = carnotEfficiency Tc Th := by
  have h1 : Qh / Th = Qc / Tc := by linarith
  have hTh0 : Th ≠ 0 := hTh.ne'
  have hTc0 : Tc ≠ 0 := hTc.ne'
  have hQh0 : Qh ≠ 0 := hQh.ne'
  have h2 : Qh * Tc = Qc * Th := by
    field_simp at h1
    linarith
  have h3 : Tc / Th = Qc / Qh := by
    field_simp
    linarith
  rw [hW, sub_div, div_self hQh.ne']
  unfold carnotEfficiency
  linarith

/-!

## B. Ideal-gas entropy changes

-/

/-- The integrated ideal-gas entropy change
`ΔS = n * cv * log (T₂ / T₁) + n * R * log (V₂ / V₁)` with constant molar heat capacity
`cv`: the integral of the MODEL differential `dS = n * cv * dT / T + n * R * dV / V`. The
lemmas below are consequences of this definition, not a derivation of the differential from
statistics. Domain: positive ratios `T₂ / T₁` and `V₂ / V₁`, as for positive temperatures and
volumes. At `T₁ = 0` or `V₁ = 0`, Lean's `x / 0 = 0` and `Real.log 0 = 0` give junk (with
constant `cv`, heating from `T₁ → 0` has a divergent `ΔS`, yet `T₁ = 0` returns a finite value),
and a negative ratio meets `Real.log (-x) = Real.log x`. The lemmas that read `ΔS` physically
have hypotheses that keep both ratios positive; `idealGasEntropyChange_totalCV` and
`idealGasEntropyChange_isothermal` only rewrite the formula and hold on junk inputs too. -/
noncomputable def idealGasEntropyChange (n cv R T1 V1 T2 V2 : ℝ) : ℝ :=
  n * cv * Real.log (T2 / T1) + n * R * Real.log (V2 / V1)

/-- No-double-counting: with total heat capacity `CV = n * cv`, the change is
`CV * log (T₂ / T₁) + n * R * log (V₂ / V₁)` — using total `CV` one does NOT multiply by
`n` again. -/
lemma idealGasEntropyChange_totalCV {n cv R T1 V1 T2 V2 CV : ℝ} (hCV : CV = n * cv) :
    idealGasEntropyChange n cv R T1 V1 T2 V2
      = CV * Real.log (T2 / T1) + n * R * Real.log (V2 / V1) := by
  unfold idealGasEntropyChange
  rw [hCV]

/-- Additivity (state-function property): `ΔS(1→2) + ΔS(2→3) = ΔS(1→3)`. -/
lemma idealGasEntropyChange_add {n cv R T1 V1 T2 V2 T3 V3 : ℝ}
    (hT1 : 0 < T1) (hT2 : 0 < T2) (hT3 : 0 < T3)
    (hV1 : 0 < V1) (hV2 : 0 < V2) (hV3 : 0 < V3) :
    idealGasEntropyChange n cv R T1 V1 T2 V2 + idealGasEntropyChange n cv R T2 V2 T3 V3
      = idealGasEntropyChange n cv R T1 V1 T3 V3 := by
  unfold idealGasEntropyChange
  rw [Real.log_div hT2.ne' hT1.ne', Real.log_div hV2.ne' hV1.ne',
    Real.log_div hT3.ne' hT2.ne', Real.log_div hV3.ne' hV2.ne',
    Real.log_div hT3.ne' hT1.ne', Real.log_div hV3.ne' hV1.ne']
  ring

/-- Isothermal case: if `T₂ = T₁` then `ΔS = n * R * log (V₂ / V₁)`. -/
lemma idealGasEntropyChange_isothermal {n cv R T1 V1 T2 V2 : ℝ}
    (hT1 : 0 < T1) (hT : T2 = T1) :
    idealGasEntropyChange n cv R T1 V1 T2 V2 = n * R * Real.log (V2 / V1) := by
  unfold idealGasEntropyChange
  rw [hT, div_self hT1.ne', Real.log_one]
  ring

/-- Isothermal expansion increases entropy: if `T₂ = T₁` and `V₁ < V₂` then `0 < ΔS`. -/
lemma idealGasEntropyChange_isothermal_pos {n cv R T1 V1 T2 V2 : ℝ}
    (hn : 0 < n) (hR : 0 < R) (hT1 : 0 < T1) (hV1 : 0 < V1)
    (hT : T2 = T1) (hexp : V1 < V2) :
    0 < idealGasEntropyChange n cv R T1 V1 T2 V2 := by
  rw [idealGasEntropyChange_isothermal hT1 hT]
  exact mul_pos (mul_pos hn hR) (Real.log_pos ((one_lt_div hV1).mpr hexp))

/-- Reversible-adiabatic case: if `T₂ / T₁ = (V₁ / V₂) ^ (R / cv)` (the adiabatic relation
for constant `cv`) then `ΔS = 0`. Route: `Real.log` algebra (`Real.log_div`,
`Real.log_rpow`), then `field_simp` and `ring`. -/
lemma idealGasEntropyChange_adiabatic {n cv R T1 V1 T2 V2 : ℝ}
    (hcv : 0 < cv)
    (hV1 : 0 < V1) (hV2 : 0 < V2)
    (had : T2 / T1 = (V1 / V2) ^ (R / cv)) :
    idealGasEntropyChange n cv R T1 V1 T2 V2 = 0 := by
  have hlogT : Real.log (T2 / T1) = (R / cv) * Real.log (V1 / V2) := by
    rw [had, Real.log_rpow (div_pos hV1 hV2)]
  have hneg : Real.log (V1 / V2) = -Real.log (V2 / V1) := by
    rw [Real.log_div hV1.ne' hV2.ne', Real.log_div hV2.ne' hV1.ne']
    ring
  unfold idealGasEntropyChange
  rw [hlogT, hneg]
  have hcv0 : cv ≠ 0 := hcv.ne'
  field_simp
  ring

/-- Sign reversal: `ΔS(1→2) = -ΔS(2→1)`. -/
lemma idealGasEntropyChange_symm {n cv R T1 V1 T2 V2 : ℝ}
    (hT1 : 0 < T1) (hT2 : 0 < T2) (hV1 : 0 < V1) (hV2 : 0 < V2) :
    idealGasEntropyChange n cv R T1 V1 T2 V2
      = -idealGasEntropyChange n cv R T2 V2 T1 V1 := by
  unfold idealGasEntropyChange
  rw [Real.log_div hT2.ne' hT1.ne', Real.log_div hV2.ne' hV1.ne',
    Real.log_div hT1.ne' hT2.ne', Real.log_div hV1.ne' hV2.ne']
  ring

/-!

## C. Entropy of mixing

-/

/-- The entropy of mixing `ΔS_mix = n * R * H(x)` for mole fractions `x : ι → ℝ`, where
`H(x) = -∑ i, x i * log (x i)` is the Shannon entropy
`Chemistry.FiniteEnsembles.shannonEntropy`. With Mathlib's convention `Real.log 0 = 0`, a
component with `x i = 0` contributes `0 * log 0 = 0` automatically, the continuous extension of
`x * log x` and so the correct value. Domain: mole fractions (`0 ≤ x i`, `∑ i, x i = 1`),
which `entropyOfMixing_nonneg` and `entropyOfMixing_eq_zero_iff` assume; a negative entry meets
Lean's `Real.log (-x) = Real.log x`, and the value is then not an entropy (it can be negative).
Gibbs-paradox remark: mixing identical gases gives zero here only because they are counted as
one component; the identical-gas resolution (indistinguishability) is CH34 territory and is NOT
claimed here. -/
noncomputable def entropyOfMixing {ι : Type*} [Fintype ι] (n R : ℝ) (x : ι → ℝ) : ℝ :=
  n * R * FiniteEnsembles.shannonEntropy x

/-- The entropy of mixing in explicit form: `ΔS_mix = -n * R * ∑ i, x i * log (x i)`. -/
lemma entropyOfMixing_eq_neg_sum {ι : Type*} [Fintype ι] (n R : ℝ) (x : ι → ℝ) :
    entropyOfMixing n R x = -n * R * ∑ i, x i * Real.log (x i) := by
  rw [entropyOfMixing, FiniteEnsembles.shannonEntropy]
  ring

/-- Mole fractions are bounded by `1`: from `∀ i, 0 ≤ x i` and `∑ i, x i = 1`, `x i ≤ 1`
for every `i`. -/
lemma moleFraction_le_one {ι : Type*} [Fintype ι] {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) (i : ι) : x i ≤ 1 := by
  calc x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
  _ = 1 := hsum

/-- The entropy of mixing is nonnegative for `0 ≤ n`, `0 ≤ R` and genuine mole fractions:
`n * R ≥ 0` times the nonnegative Shannon entropy `FiniteEnsembles.shannonEntropy_nonneg`. -/
lemma entropyOfMixing_nonneg {ι : Type*} [Fintype ι] {n R : ℝ} {x : ι → ℝ}
    (hn : 0 ≤ n) (hR : 0 ≤ R) (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    0 ≤ entropyOfMixing n R x :=
  mul_nonneg (mul_nonneg hn hR) (FiniteEnsembles.shannonEntropy_nonneg hx hsum)

/-- The entropy of mixing vanishes exactly for a single component: for `0 < n` and `0 < R`,
`entropyOfMixing n R x = 0 ↔ ∃ i, x i = 1 ∧ ∀ j, j ≠ i → x j = 0`. Since `n * R ≠ 0`, this is
the equality case `FiniteEnsembles.shannonEntropy_eq_zero_iff` of the Shannon entropy. -/
lemma entropyOfMixing_eq_zero_iff {ι : Type*} [Fintype ι] {n R : ℝ} {x : ι → ℝ}
    (hn : 0 < n) (hR : 0 < R) (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    entropyOfMixing n R x = 0 ↔ (∃ i, x i = 1 ∧ ∀ j, j ≠ i → x j = 0) := by
  rw [entropyOfMixing, mul_eq_zero, or_iff_right (mul_pos hn hR).ne',
    FiniteEnsembles.shannonEntropy_eq_zero_iff hx hsum]

/-- Binary case: for `ι = Fin 2` and `x = ![a, 1 - a]`, the mixing entropy unfolds to
`-n * R * (a * log a + (1 - a) * log (1 - a))`. -/
lemma entropyOfMixing_binary (n R a : ℝ) :
    entropyOfMixing n R (![a, 1 - a] : Fin 2 → ℝ)
      = -n * R * (a * Real.log a + (1 - a) * Real.log (1 - a)) := by
  rw [entropyOfMixing_eq_neg_sum, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-!

## D. Absolute entropy and the third law

-/

/-- The absolute molar entropy
`S(T) = ∫ t in 0..T, Cp t / t + ∑ k ∈ trans with Tt k ≤ T, ΔH k / Tt k` for molar heat
capacity `Cp : ℝ → ℝ`, finitely many first-order transitions (`trans`, with temperatures
`Tt k > 0` and molar enthalpies `ΔH k`), at absolute temperature `T ≥ 0`. The third-law
convention `S(0) = 0` for a perfect crystal is built in (integral from `0`).

Domain: the value is an entropy only when the entropy integral converges, that is under
`IntervalIntegrable (fun t => Cp t / t) MeasureTheory.volume 0 T`. Otherwise Mathlib's
interval integral takes its junk value `0` (`intervalIntegral.integral_undef`) and the
definition returns just the transition sum, which is NOT an entropy: `Cp = 1`, `T = 1` and no
transitions give `0` although `∫₀¹ dt / t` diverges. The lemmas that read `absoluteEntropy` as
an entropy assume this integrability (`hasDerivAt_absoluteEntropy`, `absoluteEntropy_mono`);
`absoluteEntropy_zero` needs none because the interval `0..0` is degenerate, and
`absoluteEntropy_insert_of_lt` is an identity of the transition sum. Likewise a transition at
`Tt k = 0` would contribute Lean's junk `ΔH k / 0 = 0`; the lemmas that use transition values
assume `0 < Tt k`. Debye remark (EF = empirical fit): the low-`T` Debye `T³` extrapolation
`Cp t ≈ a * t^3` makes `Cp t / t ≈ a * t^2` integrable at `0`; Debye's law itself is NOT
proved here. -/
noncomputable def absoluteEntropy {ι : Type*} (Cp : ℝ → ℝ) (trans : Finset ι)
    (Tt : ι → ℝ) (dH : ι → ℝ) (T : ℝ) : ℝ :=
  (∫ t in (0:ℝ)..T, Cp t / t) + ∑ k ∈ trans.filter (fun k => Tt k ≤ T), dH k / Tt k

/-- Third-law convention: `S(0) = 0` (empty integral plus empty transition sum). No
integrability hypothesis is needed: on the degenerate interval `0..0` every function is
interval integrable (`IntervalIntegrable.refl`), so this `0` is the genuine integral, not a junk
value. -/
lemma absoluteEntropy_zero {ι : Type*} (Cp : ℝ → ℝ) (trans : Finset ι)
    (Tt : ι → ℝ) (dH : ι → ℝ) (hTt : ∀ k ∈ trans, 0 < Tt k) :
    absoluteEntropy Cp trans Tt dH 0 = 0 := by
  unfold absoluteEntropy
  rw [intervalIntegral.integral_same]
  have hfilter : trans.filter (fun k => Tt k ≤ (0:ℝ)) = ∅ :=
    Finset.filter_false_of_mem (fun k hk => not_le.mpr (hTt k hk))
  rw [hfilter, Finset.sum_empty, add_zero]

/-- The temperature derivative of absolute entropy is `Cp / T`: for `0 < T`, under
continuity of `Cp` on positive temperatures and integrability of `Cp t / t` on `0..T`,
`HasDerivAt (absoluteEntropy Cp trans Tt dH) (Cp T / T) T` at points `T` that are not
transition temperatures. Via Mathlib's FTC `intervalIntegral.integral_hasDerivAt_right`; the
transition sum is locally constant near such `T`. -/
lemma hasDerivAt_absoluteEntropy {ι : Type*} (Cp : ℝ → ℝ) (trans : Finset ι)
    (Tt : ι → ℝ) (dH : ι → ℝ) {T : ℝ}
    (hT : 0 < T)
    (hCp : ContinuousOn Cp (Set.Ioi 0))
    (hInt : IntervalIntegrable (fun t => Cp t / t) MeasureTheory.volume 0 T)
    (hnotmem : ∀ k ∈ trans, Tt k ≠ T) :
    HasDerivAt (absoluteEntropy Cp trans Tt dH) (Cp T / T) T := by
  have hfg : ContinuousOn (fun t => Cp t / t) (Set.Ioi 0) :=
    hCp.div continuousOn_id (fun t ht => ne_of_gt ht)
  have hcont : ContinuousAt (fun t => Cp t / t) T :=
    hfg.continuousAt (isOpen_Ioi.mem_nhds hT)
  have hmeas : StronglyMeasurableAtFilter (fun t => Cp t / t) (𝓝 T) MeasureTheory.volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun x hx => hfg.continuousAt (isOpen_Ioi.mem_nhds hx)) T hT
  have hFTC : HasDerivAt (fun u => ∫ t in (0:ℝ)..u, Cp t / t) (Cp T / T) T :=
    intervalIntegral.integral_hasDerivAt_right hInt hmeas hcont
  have hstab : ∀ k ∈ trans, ∀ᶠ T' in 𝓝 T, ((Tt k ≤ T') ↔ (Tt k ≤ T)) := by
    intro k hk
    rcases lt_or_gt_of_ne (hnotmem k hk) with hlt | hgt
    · filter_upwards [Ioi_mem_nhds hlt] with T' hT'
      exact ⟨fun _ => le_of_lt hlt, fun _ => le_of_lt hT'⟩
    · filter_upwards [Iio_mem_nhds hgt] with T' hT'
      exact ⟨fun hle => absurd hle (not_le.mpr hT'),
        fun hle => absurd hle (not_le.mpr hgt)⟩
  have hloc : ∀ᶠ T' in 𝓝 T, ∀ k ∈ trans, ((Tt k ≤ T') ↔ (Tt k ≤ T)) :=
    (Filter.eventually_all_finset trans).mpr hstab
  have hloc2 : ∀ᶠ T' in 𝓝 T,
      trans.filter (fun k => Tt k ≤ T') = trans.filter (fun k => Tt k ≤ T) :=
    hloc.mono (fun T' h => Finset.filter_congr h)
  have hsumEq : (fun T' => ∑ k ∈ trans.filter (fun k => Tt k ≤ T'), dH k / Tt k) =ᶠ[𝓝 T]
      (fun _ => ∑ k ∈ trans.filter (fun k => Tt k ≤ T), dH k / Tt k) :=
    hloc2.mono (fun T' h => congrArg (fun s : Finset ι => ∑ k ∈ s, dH k / Tt k) h)
  have hsum0 : HasDerivAt
      (fun T' => ∑ k ∈ trans.filter (fun k => Tt k ≤ T'), dH k / Tt k) 0 T :=
    (hasDerivAt_const T _).congr_of_eventuallyEq hsumEq
  have h2 := hFTC.add hsum0
  rw [add_zero] at h2
  exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => rfl)

/-- Absolute entropy is monotone: with `0 ≤ Cp` on `[0, T]`, nonnegative transition
enthalpies, positive transition temperatures and `Cp t / t` integrable on `0..T₂` (so both
values are genuine entropies), `S(T₁) ≤ S(T₂)` for `T₁ ≤ T₂` (both in `[0, T]`). Via integral
monotonicity and growth of the transition sums. -/
lemma absoluteEntropy_mono {ι : Type*} (Cp : ℝ → ℝ) (trans : Finset ι)
    (Tt : ι → ℝ) (dH : ι → ℝ) {T T₁ T₂ : ℝ}
    (hCp : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Cp t)
    (hdH : ∀ k ∈ trans, 0 ≤ dH k)
    (hTt : ∀ k ∈ trans, 0 < Tt k)
    (hInt : IntervalIntegrable (fun t => Cp t / t) MeasureTheory.volume 0 T₂)
    (h10 : 0 ≤ T₁) (h12 : T₁ ≤ T₂) (h2T : T₂ ≤ T) :
    absoluteEntropy Cp trans Tt dH T₁ ≤ absoluteEntropy Cp trans Tt dH T₂ := by
  have h01 : IntervalIntegrable (fun t => Cp t / t) MeasureTheory.volume 0 T₁ :=
    hInt.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc_of_le h10 h12))
  have h12' : IntervalIntegrable (fun t => Cp t / t) MeasureTheory.volume T₁ T₂ :=
    hInt.mono_set (Set.uIcc_subset_uIcc_right (Set.mem_uIcc_of_le h10 h12))
  have hsplit : (∫ t in (0:ℝ)..T₁, Cp t / t) + (∫ t in T₁..T₂, Cp t / t)
      = ∫ t in (0:ℝ)..T₂, Cp t / t :=
    intervalIntegral.integral_add_adjacent_intervals h01 h12'
  have hnn : 0 ≤ ∫ t in T₁..T₂, Cp t / t :=
    intervalIntegral.integral_nonneg h12 (fun u hu => div_nonneg
      (hCp u ⟨le_trans h10 hu.1, le_trans hu.2 h2T⟩) (le_trans h10 hu.1))
  have hint : (∫ t in (0:ℝ)..T₁, Cp t / t) ≤ ∫ t in (0:ℝ)..T₂, Cp t / t := by
    linarith [hsplit, hnn]
  have hsub : trans.filter (fun k => Tt k ≤ T₁) ⊆ trans.filter (fun k => Tt k ≤ T₂) := by
    intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, le_trans hk.2 h12⟩
  have hsum : (∑ k ∈ trans.filter (fun k => Tt k ≤ T₁), dH k / Tt k)
      ≤ ∑ k ∈ trans.filter (fun k => Tt k ≤ T₂), dH k / Tt k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => div_nonneg
      (hdH k (Finset.mem_filter.mp hk).1) (le_of_lt (hTt k (Finset.mem_filter.mp hk).1)))
  unfold absoluteEntropy
  exact add_le_add hint hsum

/-- Transitions above `T` do not contribute: inserting a transition with `Tt k > T` does not
change `S(T)`. An identity of the transition sum, valid whatever value the integral term
takes. -/
lemma absoluteEntropy_insert_of_lt {ι : Type*} [DecidableEq ι] (Cp : ℝ → ℝ)
    (trans : Finset ι) (Tt : ι → ℝ) (dH : ι → ℝ) (k : ι) {T : ℝ}
    (habove : T < Tt k) :
    absoluteEntropy Cp (insert k trans) Tt dH T
      = absoluteEntropy Cp trans Tt dH T := by
  have hfilter : (insert k trans).filter (fun k => Tt k ≤ T)
      = trans.filter (fun k => Tt k ≤ T) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hj, hpj⟩
      · exact absurd hpj (not_le.mpr habove)
      · exact ⟨hj, hpj⟩
    · rintro ⟨hj, hpj⟩
      exact ⟨Or.inr hj, hpj⟩
  unfold absoluteEntropy
  rw [hfilter]

end Chemistry.Thermodynamics
