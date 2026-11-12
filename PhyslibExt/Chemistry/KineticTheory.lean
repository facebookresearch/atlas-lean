/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Kinetic theory of gases

The Maxwell-Boltzmann speed density and its normalization, the mean, rms and most probable
speeds, the elastic-wall pressure law `p * V = (1 / 3) * N * m * ⟨v²⟩`, and Graham's law of
effusion.

## i. Overview

All quantities are SI coordinate values in `ℝ`: absolute temperature `T` (K), molar mass `M`
(kg/mol), gas constant `R` (J/(mol K)), particle mass `m` (kg), Boltzmann constant `kB` (J/K).
The speed density is parametrized by `R` and `M`: `R` is the first argument of every speed
definition, and `0 < R`, `0 < T`, `0 < M` are explicit hypotheses. The Avogadro constant `NA`
is never fixed; the bridges `N = n * NA` and `R = NA * kB` are explicit hypotheses of the molar
form of the pressure law, the only place they are used.

The Maxwell-Boltzmann density `mbSpeed R T M` is a model input on `[0, ∞)`, not derived from
statistical mechanics. Integrals over `[0, ∞)` are set integrals over `Set.Ioi 0`, the form of
Mathlib's Gamma-function integrals (the endpoint `0` is a null set). The mean and rms speeds
are defined as these integrals and their closed forms are lemmas. The most probable speed
`√(2 * R * T / M)` is a definition, and a direct inequality shows that it is the unique
maximizer of the density on `[0, ∞)`.

The pressure law is proved for a finite ensemble of particles in a cube, with every model
hypothesis explicit: elastic reversal of the `x`-momentum at the wall, free flight between the
walls, and isotropy `⟨vx²⟩ = ⟨vy²⟩ = ⟨vz²⟩ = (1 / 3) * ⟨v²⟩`. The pressure is defined as momentum
transfer per unit area per unit time. The identification `⟨E_k⟩ = (3 / 2) * kB * T` is a
modeling step: it is a hypothesis of `wallPressure_mul_volume_of_kineticEnergy` and is never
derived. The pressure lemmas carry the physical-domain hypotheses `0 < N` and `0 < m`, and the
consistency steps also `0 < kB` and `0 < T`, although the algebra does not use them. The
effusion rate of each gas is assumed proportional to its mean speed, `rate = k * ⟨v⟩`; this
proportionality is a hypothesis, not derived. The factor `k` packages the hole area, the
pressure and the flow regime, and the model does not resolve `k` into these components (the
mean free path is out of scope). The cross-gas lemmas give each gas its own factor `k₁`, `k₂`
and assume `k₁ = k₂`, the formal content of "same hole, same pressure, molecular flow".
`rate ∝ √(T / M)` holds with the proportionality factor held fixed.

Out of scope: the mean free path, collision diameters, non-ideal gases, and any claim that real
gases follow these models exactly.

## ii. Key results

- `Chemistry.KineticTheory.integral_mbSpeed`: `∫ v in Ioi 0, mbSpeed R T M v = 1`.
- `Chemistry.KineticTheory.mbSpeed_nonneg`: the density is nonnegative.
- `Chemistry.KineticTheory.meanSpeed_eq`: `⟨v⟩ = √(8 * R * T / (π * M))`.
- `Chemistry.KineticTheory.rmsSpeed_eq`: `v_rms = √(3 * R * T / M)`.
- `Chemistry.KineticTheory.isMaxOn_mbSpeed_iff`: `√(2 * R * T / M)` is the unique maximizer
  of the density on `[0, ∞)`.
- `Chemistry.KineticTheory.mostProbableSpeed_lt_meanSpeed`,
  `Chemistry.KineticTheory.meanSpeed_lt_rmsSpeed`: `v_mp < ⟨v⟩ < v_rms`.
- `Chemistry.KineticTheory.wallPressure_mul_volume`: `p * V = (1 / 3) * N * m * ⟨v²⟩`.
- `Chemistry.KineticTheory.wallPressure_mul_volume_of_kineticEnergy`: `p * V = N * kB * T`
  under the identification hypothesis.
- `Chemistry.KineticTheory.wallPressure_mul_volume_molar`: `p * V = n * R * T`.
- `Chemistry.KineticTheory.effusion_rate_eq`: `rate ∝ √(T / M)`.
- `Chemistry.KineticTheory.effusion_rate_ratio`: Graham's law
  `rate₁ / rate₂ = √(M₂ / M₁)` for equal factors `k₁ = k₂`.

## iii. Table of contents

- A. Maxwell-Boltzmann speed density
- B. Characteristic speeds
- C. Pressure from momentum flux
- D. Effusion

## iv. References

- OpenStax, *Chemistry 2e* (CC BY-NC-SA 4.0).
- Mathlib: `integral_rpow_mul_exp_neg_mul_rpow`, `Real.Gamma_nat_add_half`, `Real.Gamma_two`,
  `Real.mul_exp_neg_le_exp_neg_one`, `Real.add_one_lt_exp`, `Real.pi_gt_three`,
  `Real.pi_lt_four`, `Finset.expect`.

## A. Maxwell-Boltzmann speed density
-/

@[expose] public section

namespace Chemistry.KineticTheory

open Real MeasureTheory
open scoped BigOperators

/-- Maxwell-Boltzmann speed density (CH08.1, model input), for the gas constant `R`, absolute
temperature `T`, molar mass `M` and speed `v`:
`4 * π * (M / (2 * π * R * T)) ^ (3 / 2) * v ^ 2 * exp (-(M * v ^ 2) / (2 * R * T))`.
Mathlib, Physlib and ATLAS `main` provide no Maxwell-Boltzmann speed density to reuse. -/
noncomputable def mbSpeed (R T M v : ℝ) : ℝ :=
  4 * π * (M / (2 * π * R * T)) ^ (3 / 2 : ℝ) * v ^ 2 * Real.exp (-(M * v ^ 2) / (2 * R * T))

private lemma rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * √x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

private lemma rpow_five_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (5 / 2 : ℝ) = x ^ 2 * √x := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_two,
    Real.sqrt_eq_rpow]

private lemma div_two_mul_mul {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) :
    M / (2 * R * T) = π * (M / (2 * π * R * T)) := by
  field_simp

/-- The `n`-th moment of `mbSpeed` through `integral_rpow_mul_exp_neg_mul_rpow`; `e` and `g`
are the exponent and the Gamma argument in normal form. -/
private lemma integral_pow_mul_mbSpeed (n : ℕ) {R T M e g : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hM : 0 < M) (he : -((n : ℝ) + 3) / 2 = e) (hg : ((n : ℝ) + 3) / 2 = g) :
    ∫ v in Set.Ioi (0 : ℝ), v ^ n * mbSpeed R T M v =
      4 * π * (M / (2 * π * R * T)) ^ (3 / 2 : ℝ) *
        ((M / (2 * R * T)) ^ e * (1 / 2) * Gamma g) := by
  subst he hg
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (n : ℝ) + 2)
    (b := M / (2 * R * T)) two_pos (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
    (by positivity)
  rw [show (n : ℝ) + 2 + 1 = n + 3 by ring] at h
  rw [← h, ← integral_const_mul]
  congr 1
  funext v
  rw [show (n : ℝ) + 2 = ((n + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, Real.rpow_two,
    pow_add, mbSpeed, show -(M * v ^ 2) / (2 * R * T) = -(M / (2 * R * T)) * v ^ 2 by ring]
  ring

/-- The Maxwell-Boltzmann speed density is nonnegative (CH08.1), in particular on `[0, ∞)`. -/
lemma mbSpeed_nonneg {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M) (v : ℝ) :
    0 ≤ mbSpeed R T M v := by
  unfold mbSpeed
  positivity

/-- Normalization of the Maxwell-Boltzmann speed density on `[0, ∞)` (CH08.1). -/
lemma integral_mbSpeed {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M) :
    ∫ v in Set.Ioi (0 : ℝ), mbSpeed R T M v = 1 := by
  have h := integral_pow_mul_mbSpeed 0 hR hT hM (e := -(3 / 2)) (g := 3 / 2) (by norm_num)
    (by norm_num)
  simp only [pow_zero, one_mul] at h
  have ha : 0 < M / (2 * π * R * T) := by positivity
  have hπ : √π ≠ 0 := (Real.sqrt_pos.mpr pi_pos).ne'
  have ha' : √(M / (2 * π * R * T)) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hΓ := Real.Gamma_nat_add_half 1
  norm_num at hΓ
  rw [h, div_two_mul_mul hR hT, Real.mul_rpow pi_pos.le ha.le, Real.rpow_neg pi_pos.le,
    Real.rpow_neg ha.le, rpow_three_halves pi_pos.le, rpow_three_halves ha.le, hΓ]
  field_simp
  ring

/-! ## B. Characteristic speeds -/

/-- Mean speed `⟨v⟩ = ∫ v in Ioi 0, v * mbSpeed R T M v` (CH08.2), defined as the integral; its
closed form is `meanSpeed_eq`. It is new because `mbSpeed` is. -/
noncomputable def meanSpeed (R T M : ℝ) : ℝ :=
  ∫ v in Set.Ioi (0 : ℝ), v * mbSpeed R T M v

/-- Root-mean-square speed `v_rms = √(∫ v in Ioi 0, v ^ 2 * mbSpeed R T M v)` (CH08.2), defined
from the integral; its closed form is `rmsSpeed_eq`. It is new because `mbSpeed` is. -/
noncomputable def rmsSpeed (R T M : ℝ) : ℝ :=
  Real.sqrt (∫ v in Set.Ioi (0 : ℝ), v ^ 2 * mbSpeed R T M v)

/-- Most probable speed `v_mp = √(2 * R * T / M)` (CH08.2), new because `mbSpeed` is. That it
is the unique maximizer of `mbSpeed` on `[0, ∞)` is the lemma `isMaxOn_mbSpeed_iff`, not part of
the definition. -/
noncomputable def mostProbableSpeed (R T M : ℝ) : ℝ :=
  Real.sqrt (2 * R * T / M)

/-- Closed form of the mean speed (CH08.2): `⟨v⟩ = √(8 * R * T / (π * M))`. -/
lemma meanSpeed_eq {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M) :
    meanSpeed R T M = Real.sqrt (8 * R * T / (π * M)) := by
  have h := integral_pow_mul_mbSpeed 1 hR hT hM (e := -2) (g := 2) (by norm_num) (by norm_num)
  simp only [pow_one] at h
  have ha : 0 < M / (2 * π * R * T) := by positivity
  rw [meanSpeed, h, div_two_mul_mul hR hT, Real.rpow_neg (by positivity), Real.rpow_two,
    rpow_three_halves ha.le, Gamma_two, eq_comm,
    Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  set a := M / (2 * π * R * T) with ha_def
  rw [show 4 * π * (a * √a) * (((π * a) ^ 2)⁻¹ * (1 / 2) * 1) *
      (4 * π * (a * √a) * (((π * a) ^ 2)⁻¹ * (1 / 2) * 1)) =
      (4 * π * a * (((π * a) ^ 2)⁻¹ * (1 / 2))) ^ 2 * (√a * √a) by ring,
    Real.mul_self_sqrt ha.le, ha_def]
  field_simp
  ring

/-- Second moment of the Maxwell-Boltzmann density (CH08.2):
`∫ v in Ioi 0, v ^ 2 * mbSpeed R T M v = 3 * R * T / M`. -/
lemma integral_sq_mul_mbSpeed {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M) :
    ∫ v in Set.Ioi (0 : ℝ), v ^ 2 * mbSpeed R T M v = 3 * R * T / M := by
  have h := integral_pow_mul_mbSpeed 2 hR hT hM (e := -(5 / 2)) (g := 5 / 2) (by norm_num)
    (by norm_num)
  have ha : 0 < M / (2 * π * R * T) := by positivity
  have hπ : √π ≠ 0 := (Real.sqrt_pos.mpr pi_pos).ne'
  have ha' : √(M / (2 * π * R * T)) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hΓ := Real.Gamma_nat_add_half 2
  norm_num at hΓ
  rw [h, div_two_mul_mul hR hT, Real.mul_rpow pi_pos.le ha.le, Real.rpow_neg pi_pos.le,
    Real.rpow_neg ha.le, rpow_five_halves pi_pos.le, rpow_five_halves ha.le,
    rpow_three_halves ha.le, hΓ]
  field_simp

/-- Closed form of the rms speed (CH08.2): `v_rms = √(3 * R * T / M)`. -/
lemma rmsSpeed_eq {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M) :
    rmsSpeed R T M = Real.sqrt (3 * R * T / M) := by
  rw [rmsSpeed, integral_sq_mul_mbSpeed hR hT hM]

private lemma mul_exp_neg_lt_exp_neg_one {x : ℝ} (hx : x ≠ 1) :
    x * Real.exp (-x) < Real.exp (-1) := by
  have h := Real.add_one_lt_exp (sub_ne_zero.mpr hx)
  calc x * Real.exp (-x) < Real.exp (x - 1) * Real.exp (-x) :=
        mul_lt_mul_of_pos_right (by linarith) (Real.exp_pos _)
    _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring

/-- `mbSpeed R T M v = K * (x * exp (-x))` with `x = M * v ^ 2 / (2 * R * T)`. -/
private lemma mbSpeed_eq_mul {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M) (v : ℝ) :
    mbSpeed R T M v = 4 * π * (M / (2 * π * R * T)) ^ (3 / 2 : ℝ) * (2 * R * T / M) *
      (M * v ^ 2 / (2 * R * T) * Real.exp (-(M * v ^ 2 / (2 * R * T)))) := by
  have h : 2 * R * T / M * (M * v ^ 2 / (2 * R * T)) = v ^ 2 := by field_simp
  rw [mbSpeed, neg_div, ← mul_assoc, mul_assoc _ (2 * R * T / M), h]

private lemma mul_mostProbableSpeed_sq_div {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M) :
    M * mostProbableSpeed R T M ^ 2 / (2 * R * T) = 1 := by
  rw [mostProbableSpeed, Real.sq_sqrt (by positivity)]
  field_simp

/-- Maximality of the most probable speed (CH08.2): `mbSpeed R T M v ≤ mbSpeed R T M v_mp` for
every `v`, by `x * exp (-x) ≤ exp (-1)` at `x = M * v ^ 2 / (2 * R * T)`. -/
lemma mbSpeed_le_mbSpeed_mostProbableSpeed {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M)
    (v : ℝ) : mbSpeed R T M v ≤ mbSpeed R T M (mostProbableSpeed R T M) := by
  rw [mbSpeed_eq_mul hR hT hM v, mbSpeed_eq_mul hR hT hM, mul_mostProbableSpeed_sq_div hR hT hM,
    one_mul]
  exact mul_le_mul_of_nonneg_left (Real.mul_exp_neg_le_exp_neg_one _) (by positivity)

/-- Strict maximality (CH08.2): on `[0, ∞)`, every speed other than `v_mp` has strictly smaller
density. -/
lemma mbSpeed_lt_mbSpeed_mostProbableSpeed {R T M v : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M)
    (hv : 0 ≤ v) (hne : v ≠ mostProbableSpeed R T M) :
    mbSpeed R T M v < mbSpeed R T M (mostProbableSpeed R T M) := by
  have hx : M * v ^ 2 / (2 * R * T) ≠ 1 := by
    intro h1
    apply hne
    have hv2 : v ^ 2 = 2 * R * T / M := by
      field_simp at h1 ⊢
      linarith
    rw [mostProbableSpeed, ← hv2, Real.sqrt_sq hv]
  rw [mbSpeed_eq_mul hR hT hM v, mbSpeed_eq_mul hR hT hM, mul_mostProbableSpeed_sq_div hR hT hM,
    one_mul]
  exact mul_lt_mul_of_pos_left (mul_exp_neg_lt_exp_neg_one hx) (by positivity)

/-- The most probable speed is the unique maximizer of the Maxwell-Boltzmann density on
`[0, ∞)` (CH08.2): for `0 ≤ w`, `w` maximizes `mbSpeed R T M` on `Set.Ici 0` iff
`w = mostProbableSpeed R T M`. -/
lemma isMaxOn_mbSpeed_iff {R T M w : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M) (hw : 0 ≤ w) :
    IsMaxOn (mbSpeed R T M) (Set.Ici 0) w ↔ w = mostProbableSpeed R T M := by
  constructor
  · intro h
    by_contra hne
    have h1 := mbSpeed_lt_mbSpeed_mostProbableSpeed hR hT hM hw hne
    have h2 := isMaxOn_iff.mp h _ (Set.mem_Ici.mpr (Real.sqrt_nonneg (2 * R * T / M)))
    exact absurd h2 (not_le.mpr h1)
  · rintro rfl
    exact isMaxOn_iff.mpr fun v _ => mbSpeed_le_mbSpeed_mostProbableSpeed hR hT hM v

/-- Ordering `v_mp < ⟨v⟩` (CH08.2): `2 < 8 / π` by `Real.pi_lt_four`. -/
lemma mostProbableSpeed_lt_meanSpeed {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M) :
    mostProbableSpeed R T M < meanSpeed R T M := by
  rw [meanSpeed_eq hR hT hM, mostProbableSpeed]
  apply Real.sqrt_lt_sqrt (by positivity)
  have h : 2 < 8 / π := by
    rw [lt_div_iff₀ pi_pos]
    linarith [pi_lt_four]
  calc 2 * R * T / M = 2 * (R * T / M) := by ring
    _ < 8 / π * (R * T / M) := mul_lt_mul_of_pos_right h (by positivity)
    _ = 8 * R * T / (π * M) := by ring

/-- Ordering `⟨v⟩ < v_rms` (CH08.2): `8 / π < 3` by `Real.pi_gt_three`. -/
lemma meanSpeed_lt_rmsSpeed {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M) :
    meanSpeed R T M < rmsSpeed R T M := by
  rw [meanSpeed_eq hR hT hM, rmsSpeed_eq hR hT hM]
  apply Real.sqrt_lt_sqrt (by positivity)
  have h : 8 / π < 3 := by
    rw [div_lt_iff₀ pi_pos]
    linarith [pi_gt_three]
  calc 8 * R * T / (π * M) = 8 / π * (R * T / M) := by ring
    _ < 3 * (R * T / M) := mul_lt_mul_of_pos_right h (by positivity)
    _ = 3 * R * T / M := by ring

/-! ## C. Pressure from momentum flux -/

/-- Pressure on a wall in the elastic-wall model (CH08.3), defined as momentum transfer per unit
area per unit time: particle `i ∈ s` delivers momentum `Δp i` to the wall once every `τ i`, so
the wall receives momentum at the rate `∑ i ∈ s, Δp i / τ i`, spread over its area `A` (a term
with `τ i = 0` is `0` by Lean's `x / 0 = 0`). Neither
Mathlib nor ATLAS `main` defines a kinetic (momentum-flux) pressure; Physlib's
`NVEHamiltonian.pressure` (used by `IdealGas.ideal_gas_law`) is the thermodynamic pressure
`-∂A/∂V`, a different quantity. -/
noncomputable def wallPressure {ι : Type*} (s : Finset ι) (Δp τ : ι → ℝ) (A : ℝ) : ℝ :=
  (∑ i ∈ s, Δp i / τ i) / A

/-- Under the isotropy hypothesis of `wallPressure_mul_volume`, `v2` is the mean square speed
`⟨vx ^ 2 + vy ^ 2 + vz ^ 2⟩` of the ensemble (CH08.3). -/
lemma expect_speed_sq_of_isotropy {ι : Type*} {s : Finset ι} {vx vy vz : ι → ℝ} {v2 : ℝ}
    (hiso : (𝔼 i ∈ s, vx i ^ 2) = 𝔼 i ∈ s, vy i ^ 2 ∧ (𝔼 i ∈ s, vy i ^ 2) = 𝔼 i ∈ s, vz i ^ 2 ∧
      (𝔼 i ∈ s, vz i ^ 2) = 1 / 3 * v2) :
    𝔼 i ∈ s, (vx i ^ 2 + vy i ^ 2 + vz i ^ 2) = v2 := by
  rw [Finset.expect_add_distrib, Finset.expect_add_distrib, hiso.1, hiso.2.1, hiso.2.2]
  ring

-- `hNpos` and `hm` are frozen contract domain conditions, unused by the proof.
set_option linter.unusedVariables false in
/-- Elastic-wall pressure law (CH08.3): `p * V = (1 / 3) * N * m * ⟨v²⟩`.

Model hypotheses: the gas is the finite ensemble `s` of `N` particles of mass `m` in a cube of
side `L > 0` and volume `V = L ^ 3`, with wall area `L ^ 2`; particle `i` has velocity
components `vx i`, `vy i`, `vz i`; a collision with the wall perpendicular to `x` reverses the
`x`-momentum and transfers `Δp i = 2 * m * |vx i|`; the particle returns to that wall after the
round-trip time `τ i = 2 * L / |vx i|`; and isotropy
`⟨vx²⟩ = ⟨vy²⟩ = ⟨vz²⟩ = (1 / 3) * v2` holds for the ensemble mean `⟨·⟩ = 𝔼 i ∈ s, ·`, where
`v2` is the mean square speed (`expect_speed_sq_of_isotropy`). `V > 0` follows from `0 < L`.
The algebraic identity holds generally, but the lemma carries the physical-domain hypotheses
`hNpos : 0 < N` and `hm : 0 < m`. A particle with `vx i = 0` contributes `0`. -/
lemma wallPressure_mul_volume {ι : Type*} {s : Finset ι} {Δp τ vx vy vz : ι → ℝ}
    {m L V N v2 : ℝ} (hL : 0 < L) (hV : V = L ^ 3) (hN : (s.card : ℝ) = N) (hNpos : 0 < N)
    (hm : 0 < m) (hΔp : ∀ i ∈ s, Δp i = 2 * m * |vx i|) (hτ : ∀ i ∈ s, τ i = 2 * L / |vx i|)
    (hiso : (𝔼 i ∈ s, vx i ^ 2) = 𝔼 i ∈ s, vy i ^ 2 ∧ (𝔼 i ∈ s, vy i ^ 2) = 𝔼 i ∈ s, vz i ^ 2 ∧
      (𝔼 i ∈ s, vz i ^ 2) = 1 / 3 * v2) :
    wallPressure s Δp τ (L ^ 2) * V = 1 / 3 * N * m * v2 := by
  have hrate : ∀ i ∈ s, Δp i / τ i = m / L * vx i ^ 2 := by
    intro i hi
    rw [hΔp i hi, hτ i hi, div_div_eq_mul_div, mul_assoc (2 * m), abs_mul_abs_self]
    ring
  rw [wallPressure, Finset.sum_congr rfl hrate, ← Finset.mul_sum, ← Finset.card_mul_expect,
    hiso.1, hiso.2.1, hiso.2.2, hN, hV]
  field_simp

-- `hkB` and `hT` are frozen contract domain conditions, unused by the proof.
set_option linter.unusedVariables false in
/-- Consistency step (CH08.3): if, besides the hypotheses of `wallPressure_mul_volume`, `hEk`
names the mean kinetic energy `Ek = (1 / 2) * m * v2` and the identification
`hident : Ek = (3 / 2) * kB * T` holds, then `p * V = N * kB * T`. The identification is a
modeling step, taken as a hypothesis and not derived. The lemma also carries the
physical-domain hypotheses `hkB : 0 < kB` and `hT : 0 < T`, which the algebra does not use. -/
lemma wallPressure_mul_volume_of_kineticEnergy {ι : Type*} {s : Finset ι}
    {Δp τ vx vy vz : ι → ℝ} {m L V N v2 Ek kB T : ℝ} (hL : 0 < L) (hV : V = L ^ 3)
    (hN : (s.card : ℝ) = N) (hNpos : 0 < N) (hm : 0 < m) (hΔp : ∀ i ∈ s, Δp i = 2 * m * |vx i|)
    (hτ : ∀ i ∈ s, τ i = 2 * L / |vx i|)
    (hiso : (𝔼 i ∈ s, vx i ^ 2) = 𝔼 i ∈ s, vy i ^ 2 ∧ (𝔼 i ∈ s, vy i ^ 2) = 𝔼 i ∈ s, vz i ^ 2 ∧
      (𝔼 i ∈ s, vz i ^ 2) = 1 / 3 * v2)
    (hEk : Ek = 1 / 2 * m * v2) (hident : Ek = 3 / 2 * kB * T) (hkB : 0 < kB) (hT : 0 < T) :
    wallPressure s Δp τ (L ^ 2) * V = N * kB * T := by
  rw [wallPressure_mul_volume hL hV hN hNpos hm hΔp hτ hiso]
  linear_combination (2 / 3 * N) * (hEk.symm.trans hident)

/-- Molar form of the consistency step (CH08.3): with the explicit bridges `N = n * NA` and
`R = NA * kB`, `p * V = n * R * T`. -/
lemma wallPressure_mul_volume_molar {ι : Type*} {s : Finset ι} {Δp τ vx vy vz : ι → ℝ}
    {m L V N v2 Ek kB T n NA R : ℝ} (hL : 0 < L) (hV : V = L ^ 3) (hN : (s.card : ℝ) = N)
    (hNpos : 0 < N) (hm : 0 < m) (hΔp : ∀ i ∈ s, Δp i = 2 * m * |vx i|)
    (hτ : ∀ i ∈ s, τ i = 2 * L / |vx i|)
    (hiso : (𝔼 i ∈ s, vx i ^ 2) = 𝔼 i ∈ s, vy i ^ 2 ∧ (𝔼 i ∈ s, vy i ^ 2) = 𝔼 i ∈ s, vz i ^ 2 ∧
      (𝔼 i ∈ s, vz i ^ 2) = 1 / 3 * v2)
    (hEk : Ek = 1 / 2 * m * v2) (hident : Ek = 3 / 2 * kB * T) (hkB : 0 < kB) (hT : 0 < T)
    (hNn : N = n * NA) (hR : R = NA * kB) :
    wallPressure s Δp τ (L ^ 2) * V = n * R * T := by
  rw [wallPressure_mul_volume_of_kineticEnergy hL hV hN hNpos hm hΔp hτ hiso hEk hident hkB hT,
    hNn, hR]
  ring

/-! ## D. Effusion -/

/-- Dependence of the effusion rate on `T` and `M` (CH08.4): under the model hypothesis
`rate = k * ⟨v⟩`, `rate = k * √(8 * R / π) * √(T / M)`; for a proportionality factor `k` held
fixed, `rate ∝ √(T / M)`. -/
lemma effusion_rate_eq {R T M k rate : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 < M)
    (h : rate = k * meanSpeed R T M) :
    rate = k * Real.sqrt (8 * R / π) * Real.sqrt (T / M) := by
  rw [h, meanSpeed_eq hR hT hM, mul_assoc k,
    ← Real.sqrt_mul (show (0 : ℝ) ≤ 8 * R / π by positivity)]
  congr 2
  ring

/-- Graham's law of effusion (CH08.4): two gases at the same temperature `T`, with rates
proportional to their mean speeds with their own factors (model hypothesis),
`rate₁ = k₁ * meanSpeed R T M₁` and `rate₂ = k₂ * meanSpeed R T M₂`, and with `k₁ > 0` and
`hk : k₁ = k₂`, satisfy `rate₁ / rate₂ = √(M₂ / M₁)`. In this model the factor `k` packages the
hole area, the pressure and the flow regime, so `hk` is the formal content of "same hole, same
pressure, molecular flow"; the model does not resolve `k` into area, pressure and flow
components (the mean free path is out of scope). -/
theorem effusion_rate_ratio {R T M₁ M₂ k₁ k₂ rate₁ rate₂ : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hk₁ : 0 < k₁) (hk : k₁ = k₂)
    (h₁ : rate₁ = k₁ * meanSpeed R T M₁) (h₂ : rate₂ = k₂ * meanSpeed R T M₂) :
    rate₁ / rate₂ = Real.sqrt (M₂ / M₁) := by
  subst hk
  rw [h₁, h₂, meanSpeed_eq hR hT hM₁, meanSpeed_eq hR hT hM₂, mul_div_mul_left _ _ hk₁.ne',
    ← Real.sqrt_div' _ (show (0 : ℝ) ≤ 8 * R * T / (π * M₂) by positivity)]
  congr 1
  field_simp

/-- Equal effusion rates (CH08.4): under the model hypothesis of `effusion_rate_eq` for each gas,
with its own factor (`rate₁ = k₁ * meanSpeed R T₁ M₁`, `rate₂ = k₂ * meanSpeed R T₂ M₂`), and
with `k₁ > 0` and `hk : k₁ = k₂`, `rate₁ = rate₂ ↔ T₁ / M₁ = T₂ / M₂`; equal rates need the
temperature ratio to compensate the molar-mass ratio. As in `effusion_rate_ratio`, `k` packages
the hole area, the pressure and the flow regime, which the model does not resolve, so `hk` is
the formal content of "same hole, same pressure, molecular flow"; the model holds `k` fixed as
the temperature changes. -/
lemma effusion_rate_eq_iff {R T₁ T₂ M₁ M₂ k₁ k₂ rate₁ rate₂ : ℝ} (hR : 0 < R) (hT₁ : 0 < T₁)
    (hT₂ : 0 < T₂) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hk₁ : 0 < k₁) (hk : k₁ = k₂)
    (h₁ : rate₁ = k₁ * meanSpeed R T₁ M₁) (h₂ : rate₂ = k₂ * meanSpeed R T₂ M₂) :
    rate₁ = rate₂ ↔ T₁ / M₁ = T₂ / M₂ := by
  subst hk
  rw [effusion_rate_eq hR hT₁ hM₁ h₁, effusion_rate_eq hR hT₂ hM₂ h₂,
    mul_right_inj' (show k₁ * Real.sqrt (8 * R / π) ≠ 0 by positivity),
    Real.sqrt_inj (by positivity) (by positivity)]

/-- Non-claim (CH08.4): under the same model hypothesis, with `k₁ > 0` and `hk : k₁ = k₂`, gases
of equal molar mass at different temperatures do not effuse at equal rates. As in
`effusion_rate_ratio`, `hk` is the formal content of "same hole, same pressure, molecular flow",
since `k` packages the hole area, the pressure and the flow regime, which the model does not
resolve; the model holds `k` fixed as the temperature changes. -/
lemma effusion_rate_ne_of_temperature_ne {R T₁ T₂ M k₁ k₂ rate₁ rate₂ : ℝ} (hR : 0 < R)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hM : 0 < M) (hk₁ : 0 < k₁) (hk : k₁ = k₂)
    (h₁ : rate₁ = k₁ * meanSpeed R T₁ M) (h₂ : rate₂ = k₂ * meanSpeed R T₂ M) (hT : T₁ ≠ T₂) :
    rate₁ ≠ rate₂ := by
  rw [Ne, effusion_rate_eq_iff hR hT₁ hT₂ hM hM hk₁ hk h₁ h₂, div_left_inj' hM.ne']
  exact hT

end Chemistry.KineticTheory
