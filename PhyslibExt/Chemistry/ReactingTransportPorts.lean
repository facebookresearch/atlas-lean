/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import MathlibExt.Analysis.ODE.MaximalSolution

/-!
# Exothermic stirred-tank reactor: the concentration and temperature box

## i. Overview

A continuous stirred-tank reactor with one exothermic first-order reaction, written in reduced
coordinates: concentration `c`, absolute temperature `T`, dilution rate `a = Q / V > 0`, inlet
concentration `cin ≥ 0` and temperature `Tin > 0`, coolant temperature `Tc > 0` with cooling rate
`h = U A_w / (ρ c_p V) ≥ 0`, adiabatic temperature rise per unit concentration
`b = (-ΔH_r) / (ρ c_p) ≥ 0` (exothermic, constant heat capacity), and the Arrhenius rate
`k(T) = A * exp(-B / T)` with `A ≥ 0` and activation temperature `B = E_a / R > 0`:

* `c' = a (cin - c) - k(T) c`,
* `T' = a (Tin - T) + b k(T) c - h (T - Tc)`.

From the initial state `(c0, T0)` with `c0 ≥ 0`, `T0 > 0`, every forward solution stays in the box
`0 ≤ c ≤ cmax`, `Tmin ≤ T ≤ Tmax`, where `cmax = max c0 cin`,
`Tmin = min T0 ((a Tin + h Tc) / (a + h)) > 0` and
`Tmax = max T0 ((a Tin + h Tc + b A cmax) / (a + h))`. On each face the field points into the
box, and outside each face it points back, because `0 ≤ k(T) ≤ A` for `T > 0`; a one-sided
barrier argument on each face gives the invariance for every rate law with values in `[0, A]`.

For existence the rate is extended below the floor as `A * exp(-B / max (Tmin / 2) T)`, a proof
device that equals the physical rate on the box and makes the field locally Lipschitz on the whole
plane. The maximal solution of the extended field leaves every compact set at a finite end of its
interval (`ode_maximal_solution_exit_compact`); it stays in the compact box, so it exists for all
forward time, and there it solves the physical system.

Model inputs: the two balance laws above with explicit rate and constant heat-capacity models,
stated over explicit real coordinates with no shared reactor or stream structure; the extension
is not a physical claim below the admitted temperature range. The isothermal first-order reactor
and its explicit solution are `PhyslibExt.Engineering.Process.CSTR`. Endothermic reactions
(`b < 0`) are not covered: the lower temperature bound then fails. Without positive inlet and
coolant temperatures the floor `Tmin` is not positive. No uniqueness, stability, empirical
adequacy or system safety claim is made.

## ii. Key results

- `Chemistry.ReactingTransportPorts.temperatureFloor_pos`: the floor `Tmin` is positive.
- `Chemistry.ReactingTransportPorts.flooredRateConstant_eq`,
  `Chemistry.ReactingTransportPorts.flooredRateConstant_mem_Icc`: the extended rate is the
  Arrhenius rate on the box and lies in `[0, A]` everywhere.
- `Chemistry.ReactingTransportPorts.locallyLipschitz_cstrField_flooredRateConstant`: the
  extended field is locally Lipschitz on the plane.
- `Chemistry.ReactingTransportPorts.box_face_signs`: inward signs on the four faces.
- `Chemistry.ReactingTransportPorts.box_invariant_of_rate_bounds`,
  `Chemistry.ReactingTransportPorts.arrhenius_box_invariant`: invariance of the box.
- `Chemistry.ReactingTransportPorts.exists_arrhenius_path`: the physical path exists for all
  forward time and stays in the box.

## iii. Table of contents

- A. Rates, balances and the box
- B. Positive floor and the extended rate
- C. Boundary signs
- D. Invariance of the box
- E. Local existence and compact continuation

## iv. References

- R. Aris and N. R. Amundson, An analysis of chemical reactor stability and control I,
  *Chemical Engineering Science* 7 (1958) 121-131 (the exothermic CSTR model).
- H. S. Fogler, *Elements of Chemical Reaction Engineering*, 5th edition, 2016, chapters 11-12
  (CSTR mole and energy balances, Arrhenius rate).
- G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, 2012, section 2.4
  (maximal solutions leave every compact set).
-/

@[expose] public section

namespace Chemistry.ReactingTransportPorts

/-! ## A. Rates, balances and the box -/

/-- Arrhenius rate coefficient `k(T) = A * exp(-B / T)`, with prefactor `A` (per time) and
activation temperature `B = E_a / R`. It is read for `T > 0`; by the convention `-B / 0 = 0`,
`k(0) = A`, and `k(T) > A` for `T < 0` when `A, B > 0`. -/
noncomputable def arrheniusRateConstant (A B T : ℝ) : ℝ :=
  A * Real.exp (-B / T)

/-- The proof-device rate `A * exp(-B / max (Tfloor / 2) T)`: the Arrhenius rate at the
temperature raised to at least `Tfloor / 2`. It is defined for all real arguments: when
`max (Tfloor / 2) T = 0` the convention `x / 0 = 0` makes it `A`. The intended domain is
`Tfloor > 0`, where the floored temperature is positive. -/
noncomputable def flooredRateConstant (A B Tfloor T : ℝ) : ℝ :=
  arrheniusRateConstant A B (max (Tfloor / 2) T)

/-- Concentration balance `a (cin - c) - k c` for the rate value `k`. -/
def concentrationRhs (a cin k c : ℝ) : ℝ :=
  a * (cin - c) - k * c

/-- Temperature balance `a (Tin - T) + b k c - h (T - Tc)` for the rate value `k`. -/
def temperatureRhs (a b h Tin Tc k c T : ℝ) : ℝ :=
  a * (Tin - T) + b * k * c - h * (T - Tc)

/-- The CSTR vector field on states `(c, T)` for the rate law `κ`. -/
def cstrField (a b h cin Tin Tc : ℝ) (κ : ℝ → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (concentrationRhs a cin (κ x.2) x.1, temperatureRhs a b h Tin Tc (κ x.2) x.1 x.2)

/-- Concentration ceiling `cmax = max c0 cin`. -/
noncomputable def concentrationCeiling (c0 cin : ℝ) : ℝ :=
  max c0 cin

/-- Temperature floor `Tmin = min T0 ((a Tin + h Tc) / (a + h))`. It is defined for all real
arguments: for `a + h = 0` the convention `x / 0 = 0` makes it `min T0 0`. The intended domain is
`a > 0` and `h ≥ 0`, where `a + h > 0`. -/
noncomputable def temperatureFloor (a h Tin Tc T0 : ℝ) : ℝ :=
  min T0 ((a * Tin + h * Tc) / (a + h))

/-- Temperature ceiling `Tmax = max T0 ((a Tin + h Tc + b A cmax) / (a + h))`. It is defined for
all real arguments: for `a + h = 0` the convention `x / 0 = 0` makes it `max T0 0`. The intended
domain is `a > 0` and `h ≥ 0`, where `a + h > 0`. -/
noncomputable def temperatureCeiling (a b h A Tin Tc T0 cmax : ℝ) : ℝ :=
  max T0 ((a * Tin + h * Tc + b * A * cmax) / (a + h))

/-! ## B. Positive floor and the extended rate -/

/-- The Arrhenius rate is nonnegative for a nonnegative prefactor, at every real `T`. -/
lemma arrheniusRateConstant_nonneg {A : ℝ} (hA : 0 ≤ A) (B T : ℝ) :
    0 ≤ arrheniusRateConstant A B T := by
  exact mul_nonneg hA (Real.exp_pos _).le

/-- For `0 ≤ A` and `0 ≤ B`, above absolute zero the Arrhenius rate is at most its prefactor. -/
lemma arrheniusRateConstant_le {A B T : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 < T) :
    arrheniusRateConstant A B T ≤ A := by
  unfold arrheniusRateConstant
  have hle : Real.exp (-B / T) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hT.le
  calc A * Real.exp (-B / T) ≤ A * 1 := mul_le_mul_of_nonneg_left hle hA
    _ = A := mul_one A

/-- The temperature floor is positive: positive dilution rate, inlet, coolant and initial
temperatures, nonnegative cooling rate. -/
lemma temperatureFloor_pos {a h Tin Tc T0 : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (hTin : 0 < Tin)
    (hTc : 0 < Tc) (hT0 : 0 < T0) : 0 < temperatureFloor a h Tin Tc T0 := by
  unfold temperatureFloor
  refine lt_min hT0 (div_pos ?_ ?_)
  · exact add_pos_of_pos_of_nonneg (mul_pos ha hTin) (mul_nonneg hh hTc.le)
  · exact add_pos_of_pos_of_nonneg ha hh

/-- The extended rate is the physical Arrhenius rate at and above a nonnegative floor. -/
lemma flooredRateConstant_eq {A B Tfloor T : ℝ} (hfloor : 0 ≤ Tfloor) (hT : Tfloor ≤ T) :
    flooredRateConstant A B Tfloor T = arrheniusRateConstant A B T := by
  unfold flooredRateConstant
  rw [max_eq_right (by linarith)]

/-- For `0 ≤ A`, `0 ≤ B` and a positive floor, the extended rate takes values in `[0, A]` at every
real `T`. -/
lemma flooredRateConstant_mem_Icc {A B Tfloor : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hfloor : 0 < Tfloor)
    (T : ℝ) : flooredRateConstant A B Tfloor T ∈ Set.Icc 0 A := by
  exact ⟨arrheniusRateConstant_nonneg hA _ _,
    arrheniusRateConstant_le hA hB (lt_of_lt_of_le (half_pos hfloor) (le_max_left _ _))⟩

/-- For a positive floor the extended rate is locally Lipschitz: the smooth map
`y ↦ A * exp(-B / y)` near `max (Tfloor / 2) T` composed with the 1-Lipschitz
`T ↦ max (Tfloor / 2) T`. -/
private lemma locallyLipschitz_flooredRateConstant (A B : ℝ) {Tfloor : ℝ} (hfloor : 0 < Tfloor) :
    LocallyLipschitz (flooredRateConstant A B Tfloor) := by
  intro T0
  have hε : 0 < Tfloor / 2 := half_pos hfloor
  have hy0 : max (Tfloor / 2) T0 ≠ 0 := (lt_of_lt_of_le hε (le_max_left _ _)).ne'
  have hf : ContDiffAt ℝ 1 (fun y : ℝ => A * Real.exp (-B / y)) (max (Tfloor / 2) T0) := by
    have hdiv : ContDiffAt ℝ 1 (fun y : ℝ => -B / y) (max (Tfloor / 2) T0) :=
      contDiffAt_const.div contDiffAt_id hy0
    exact contDiffAt_const.mul hdiv.exp
  obtain ⟨K, t, ht, hK⟩ := hf.exists_lipschitzOnWith
  have hm : LipschitzWith 1 (fun T : ℝ => max (Tfloor / 2) T) := LipschitzWith.id.const_max _
  refine ⟨K * 1, (fun T : ℝ => max (Tfloor / 2) T) ⁻¹' t,
    hm.continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
  exact hK.comp hm.lipschitzOnWith (Set.mapsTo_preimage _ _)

/-- Local regularity: for a positive floor the extended CSTR field is locally Lipschitz on the
whole plane. -/
lemma locallyLipschitz_cstrField_flooredRateConstant (a b h cin Tin Tc A B : ℝ) {Tfloor : ℝ}
    (hfloor : 0 < Tfloor) :
    LocallyLipschitz (cstrField a b h cin Tin Tc (flooredRateConstant A B Tfloor)) := by
  have hκ := locallyLipschitz_flooredRateConstant A B hfloor
  have hΦ : LocallyLipschitz (fun p : ℝ × ℝ × ℝ =>
      ((a * (cin - p.1) - p.2.2 * p.1 : ℝ),
        (a * (Tin - p.2.1) + b * p.2.2 * p.1 - h * (p.2.1 - Tc) : ℝ))) := by
    exact (show ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ =>
      ((a * (cin - p.1) - p.2.2 * p.1 : ℝ),
        (a * (Tin - p.2.1) + b * p.2.2 * p.1 - h * (p.2.1 - Tc) : ℝ))) by fun_prop).locallyLipschitz
  have hψ : LocallyLipschitz (fun x : ℝ × ℝ => (x.1, x.2, flooredRateConstant A B Tfloor x.2)) :=
    LipschitzWith.prod_fst.locallyLipschitz.prodMk
      (LipschitzWith.prod_snd.locallyLipschitz.prodMk
        (hκ.comp LipschitzWith.prod_snd.locallyLipschitz))
  have h := hΦ.comp hψ
  convert h using 1
  funext x
  simp [cstrField, concentrationRhs, temperatureRhs, mul_assoc]

/-! ## C. Boundary signs -/

/-- Inward signs on the four faces of the box, for `0 < a`, nonnegative `b`, `h` and `cin`, any rate
value `0 ≤ k ≤ A` and a state with `0 ≤ c ≤ cmax`: `c' ≥ 0` at `c = 0`, `c' ≤ 0` at `c = cmax`,
`T' ≥ 0` at `T = Tmin` and `T' ≤ 0` at `T = Tmax`. -/
lemma box_face_signs {a b h A cin Tin Tc c0 T0 k c T : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hb : 0 ≤ b) (hcin : 0 ≤ cin) (hk : 0 ≤ k) (hkA : k ≤ A)
    (hc : c ∈ Set.Icc 0 (concentrationCeiling c0 cin)) :
    (c = 0 → 0 ≤ concentrationRhs a cin k c) ∧
      (c = concentrationCeiling c0 cin → concentrationRhs a cin k c ≤ 0) ∧
      (T = temperatureFloor a h Tin Tc T0 → 0 ≤ temperatureRhs a b h Tin Tc k c T) ∧
      (T = temperatureCeiling a b h A Tin Tc T0 (concentrationCeiling c0 cin) →
        temperatureRhs a b h Tin Tc k c T ≤ 0) := by
  obtain ⟨hc0, hcm⟩ := hc
  have hah : 0 < a + h := add_pos_of_pos_of_nonneg ha hh
  have hcmax : 0 ≤ concentrationCeiling c0 cin := le_trans hcin (le_max_right _ _)
  have hcin_le : cin ≤ concentrationCeiling c0 cin := le_max_right _ _
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
  · subst h0
    simp only [concentrationRhs, sub_zero, mul_zero]
    exact mul_nonneg ha.le hcin
  · rw [h0]
    unfold concentrationRhs
    nlinarith
  · have hfl : (a + h) * temperatureFloor a h Tin Tc T0 ≤ a * Tin + h * Tc := by
      have := min_le_right T0 ((a * Tin + h * Tc) / (a + h))
      rw [le_div_iff₀ hah] at this
      unfold temperatureFloor
      linarith
    rw [h0]
    unfold temperatureRhs
    nlinarith [mul_nonneg (mul_nonneg hb hk) hc0]
  · have hce : a * Tin + h * Tc + b * A * concentrationCeiling c0 cin ≤
        (a + h) * temperatureCeiling a b h A Tin Tc T0 (concentrationCeiling c0 cin) := by
      have := le_max_right T0
        ((a * Tin + h * Tc + b * A * concentrationCeiling c0 cin) / (a + h))
      rw [div_le_iff₀ hah] at this
      unfold temperatureCeiling
      linarith
    have hkc : k * c ≤ A * concentrationCeiling c0 cin :=
      mul_le_mul hkA hcm hc0 (le_trans hk hkA)
    rw [h0]
    unfold temperatureRhs
    nlinarith [mul_le_mul_of_nonneg_left hkc hb]

/-! ## D. Invariance of the box -/

/-- One-sided barrier on `[0, τ]`: a function with `g 0 ≤ 0` whose derivative within
`[0, τ]` is `≤ 0` wherever `g > 0` stays `≤ 0`. -/
private lemma barrier_nonpos {g g' : ℝ → ℝ} {τ : ℝ}
    (hg : ∀ s ∈ Set.Icc 0 τ, HasDerivWithinAt g (g' s) (Set.Icc 0 τ) s)
    (h0 : g 0 ≤ 0) (hout : ∀ s ∈ Set.Icc 0 τ, 0 < g s → g' s ≤ 0) :
    ∀ s ∈ Set.Icc 0 τ, g s ≤ 0 := by
  intro s1 hs1
  by_contra hpos
  have hpos' : 0 < g s1 := lt_of_not_ge hpos
  have hcont : ContinuousOn g (Set.Icc 0 τ) := fun s hs => (hg s hs).continuousWithinAt
  set S : Set ℝ := Set.Icc 0 s1 ∩ {s | g s ≤ 0} with hSdef
  have hsub1 : Set.Icc 0 s1 ⊆ Set.Icc 0 τ := Set.Icc_subset_Icc le_rfl hs1.2
  have hS_closed : IsClosed S :=
    (hcont.mono hsub1).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hS_ne : S.Nonempty := ⟨0, ⟨le_rfl, hs1.1⟩, h0⟩
  have hS_bdd : BddAbove S := ⟨s1, fun s hs => hs.1.2⟩
  have hs0S : sSup S ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
  have hs0lt : sSup S < s1 := by
    refine lt_of_le_of_ne hs0S.1.2 fun h => ?_
    have := hs0S.2
    rw [h] at this
    exact absurd this (not_le.mpr hpos')
  have hposon : ∀ s ∈ Set.Ioc (sSup S) s1, 0 < g s := by
    intro s hs
    by_contra hle
    have hsS : s ∈ S := ⟨⟨le_trans hs0S.1.1 hs.1.le, hs.2⟩, not_lt.mp hle⟩
    exact absurd (le_csSup hS_bdd hsS) (not_le.mpr hs.1)
  have hsub : Set.Icc (sSup S) s1 ⊆ Set.Icc 0 τ := Set.Icc_subset_Icc hs0S.1.1 hs1.2
  have hanti : AntitoneOn g (Set.Icc (sSup S) s1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := g') (convex_Icc _ _) (hcont.mono hsub)
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Icc] at hs ⊢
      exact (hg s (hsub (Set.Ioo_subset_Icc_self hs))).mono
        (Set.Ioo_subset_Icc_self.trans hsub)
    · rw [interior_Icc] at hs
      exact hout s (hsub (Set.Ioo_subset_Icc_self hs)) (hposon s ⟨hs.1, hs.2.le⟩)
  have hle := hanti ⟨le_rfl, hs0lt.le⟩ ⟨hs0lt.le, le_rfl⟩ hs0lt.le
  have := hs0S.2
  simp only [Set.mem_ofPred_eq] at this
  linarith
/-- Comparison on a time interval `[0, τ]`, for `0 < a`, nonnegative `b`, `h`, `cin` and `c0`,
`0 < T0`, and any rate law `κ` with `0 ≤ κ T` for every `T` and `κ T ≤ A` for `T > 0`: a solution
starting at `(c0, T0)` is in the box at time `τ`. The concentration bounds and the two temperature
bounds are the two orthant arguments (lower and upper corner). -/
lemma box_invariant_of_rate_bounds {a b h A cin Tin Tc c0 T0 τ : ℝ} {κ : ℝ → ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) (hb : 0 ≤ b) (hcin : 0 ≤ cin) (hc0 : 0 ≤ c0) (hT0 : 0 < T0)
    (hκ0 : ∀ T, 0 ≤ κ T) (hκA : ∀ T, 0 < T → κ T ≤ A) {c T : ℝ → ℝ} (hcI : c 0 = c0)
    (hTI : T 0 = T0)
    (hc : ∀ s ∈ Set.Icc 0 τ,
      HasDerivWithinAt c (concentrationRhs a cin (κ (T s)) (c s)) (Set.Icc 0 τ) s)
    (hT : ∀ s ∈ Set.Icc 0 τ,
      HasDerivWithinAt T (temperatureRhs a b h Tin Tc (κ (T s)) (c s) (T s)) (Set.Icc 0 τ) s)
    (hτ : 0 ≤ τ) :
    c τ ∈ Set.Icc 0 (concentrationCeiling c0 cin) ∧
      T τ ∈ Set.Icc (temperatureFloor a h Tin Tc T0)
        (temperatureCeiling a b h A Tin Tc T0 (concentrationCeiling c0 cin)) := by
  have hah : 0 < a + h := add_pos_of_pos_of_nonneg ha hh
  have hcmax0 : 0 ≤ concentrationCeiling c0 cin := le_trans hcin (le_max_right _ _)
  -- lower concentration face
  have hcl : ∀ s ∈ Set.Icc 0 τ, -c s ≤ 0 := by
    refine barrier_nonpos (g := fun s => -c s) (fun s hs => (hc s hs).neg) (by simp [hcI, hc0])
      (fun s hs hneg => ?_)
    have hcs : c s < 0 := by simpa using hneg
    have := hκ0 (T s)
    simp only [concentrationRhs]
    nlinarith [mul_nonneg ha.le hcin]
  -- upper concentration face
  have hcu : ∀ s ∈ Set.Icc 0 τ, c s - concentrationCeiling c0 cin ≤ 0 := by
    refine barrier_nonpos (g := fun s => c s - concentrationCeiling c0 cin)
      (fun s hs => (hc s hs).sub_const _) (by simp [hcI, concentrationCeiling])
      (fun s hs hpos => ?_)
    have hcs : concentrationCeiling c0 cin < c s := by simpa using hpos
    have hcin_le : cin ≤ concentrationCeiling c0 cin := le_max_right _ _
    have := hκ0 (T s)
    simp only [concentrationRhs]
    nlinarith [mul_nonneg this (hcmax0.trans hcs.le)]
  -- lower temperature face
  have hTl : ∀ s ∈ Set.Icc 0 τ, temperatureFloor a h Tin Tc T0 - T s ≤ 0 := by
    refine barrier_nonpos (g := fun s => temperatureFloor a h Tin Tc T0 - T s)
      (fun s hs => (hT s hs).const_sub _) (by simp [hTI, temperatureFloor])
      (fun s hs hpos => ?_)
    have hTs : T s < temperatureFloor a h Tin Tc T0 := by linarith
    have hfl : (a + h) * temperatureFloor a h Tin Tc T0 ≤ a * Tin + h * Tc := by
      have := min_le_right T0 ((a * Tin + h * Tc) / (a + h))
      rw [le_div_iff₀ hah] at this
      unfold temperatureFloor
      linarith
    have hcs : 0 ≤ c s := by linarith [hcl s hs]
    have hk := hκ0 (T s)
    simp only [temperatureRhs]
    nlinarith [mul_nonneg (mul_nonneg hb hk) hcs, mul_lt_mul_of_pos_left hTs hah]
  -- upper temperature face
  have hTu : ∀ s ∈ Set.Icc 0 τ,
      T s - temperatureCeiling a b h A Tin Tc T0 (concentrationCeiling c0 cin) ≤ 0 := by
    refine barrier_nonpos (g := fun s => T s - temperatureCeiling a b h A Tin Tc T0
        (concentrationCeiling c0 cin))
      (fun s hs => (hT s hs).sub_const _) (by simp [hTI, temperatureCeiling])
      (fun s hs hpos => ?_)
    have hTs : temperatureCeiling a b h A Tin Tc T0 (concentrationCeiling c0 cin) < T s := by
      linarith
    have hce : a * Tin + h * Tc + b * A * concentrationCeiling c0 cin ≤
        (a + h) * temperatureCeiling a b h A Tin Tc T0 (concentrationCeiling c0 cin) := by
      have := le_max_right T0
        ((a * Tin + h * Tc + b * A * concentrationCeiling c0 cin) / (a + h))
      rw [div_le_iff₀ hah] at this
      unfold temperatureCeiling
      linarith
    have hTpos : 0 < T s := lt_of_lt_of_le hT0 ((le_max_left _ _).trans hTs.le)
    have hk0 := hκ0 (T s)
    have hkA := hκA (T s) hTpos
    have hcs0 : 0 ≤ c s := by linarith [hcl s hs]
    have hcs1 : c s ≤ concentrationCeiling c0 cin := by linarith [hcu s hs]
    have hkc : κ (T s) * c s ≤ A * concentrationCeiling c0 cin :=
      mul_le_mul hkA hcs1 hcs0 (le_trans hk0 hkA)
    simp only [temperatureRhs]
    nlinarith [mul_le_mul_of_nonneg_left hkc hb, mul_lt_mul_of_pos_left hTs hah]
  have hτm : τ ∈ Set.Icc 0 τ := ⟨hτ, le_rfl⟩
  exact ⟨⟨by linarith [hcl τ hτm], by linarith [hcu τ hτm]⟩,
    ⟨by linarith [hTl τ hτm], by linarith [hTu τ hτm]⟩⟩

/-- Invariance for the physical CSTR, for `0 < a`, `0 < B`, `0 < T0` and nonnegative `A`, `b`, `h`,
`cin` and `c0`: every forward solution with the Arrhenius rate, from `(c0, T0)`, stays in the
concentration and temperature box for all `t ≥ 0`. -/
lemma arrhenius_box_invariant {a b h A B cin Tin Tc c0 T0 : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hT0 : 0 < T0) (hA : 0 ≤ A) (hb : 0 ≤ b) (hh : 0 ≤ h) (hcin : 0 ≤ cin) (hc0 : 0 ≤ c0)
    {c T : ℝ → ℝ} (hcI : c 0 = c0) (hTI : T 0 = T0)
    (hc : ∀ s, 0 ≤ s →
      HasDerivWithinAt c (concentrationRhs a cin (arrheniusRateConstant A B (T s)) (c s))
        (Set.Ici 0) s)
    (hT : ∀ s, 0 ≤ s →
      HasDerivWithinAt T (temperatureRhs a b h Tin Tc (arrheniusRateConstant A B (T s)) (c s) (T s))
        (Set.Ici 0) s)
    {t : ℝ} (ht : 0 ≤ t) :
    c t ∈ Set.Icc 0 (concentrationCeiling c0 cin) ∧
      T t ∈ Set.Icc (temperatureFloor a h Tin Tc T0)
        (temperatureCeiling a b h A Tin Tc T0 (concentrationCeiling c0 cin)) := by
  exact box_invariant_of_rate_bounds ha hh hb hcin hc0 hT0 (arrheniusRateConstant_nonneg hA B)
    (fun T hT => arrheniusRateConstant_le hA hB.le hT) hcI hTI
    (fun s hs => (hc s hs.1).mono Set.Icc_subset_Ici_self)
    (fun s hs => (hT s hs.1).mono Set.Icc_subset_Ici_self) ht

/-! ## E. Local existence and compact continuation -/

/-- The first component of a differentiable curve in `ℝ × ℝ` is differentiable. -/
private lemma hasDerivAt_fst_comp {x : ℝ → ℝ × ℝ} {x' : ℝ × ℝ} {t : ℝ} (h : HasDerivAt x x' t) :
    HasDerivAt (fun s => (x s).1) x'.1 t := by
  exact hasFDerivAt_fst.comp_hasDerivAt t h

/-- The second component of a differentiable curve in `ℝ × ℝ` is differentiable. -/
private lemma hasDerivAt_snd_comp {x : ℝ → ℝ × ℝ} {x' : ℝ × ℝ} {t : ℝ} (h : HasDerivAt x x' t) :
    HasDerivAt (fun s => (x s).2) x'.2 t := by
  exact hasFDerivAt_snd.comp_hasDerivAt t h

/-- The physical CSTR path exists for all forward time and stays in the box, for `0 < a`, `0 < B`,
positive `T0`, `Tin` and `Tc`, and nonnegative `A`, `b`, `h`, `cin` and `c0`: there are `c`, `T`
with `c 0 = c0`, `T 0 = T0` that, at every `t ≥ 0`, lie in the box and solve the physical balances
with the Arrhenius rate. -/
lemma exists_arrhenius_path {a b h A B cin Tin Tc c0 T0 : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hT0 : 0 < T0) (hTin : 0 < Tin) (hTc : 0 < Tc) (hA : 0 ≤ A) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (hcin : 0 ≤ cin) (hc0 : 0 ≤ c0) :
    ∃ c T : ℝ → ℝ, c 0 = c0 ∧ T 0 = T0 ∧ ∀ t, 0 ≤ t →
      (c t ∈ Set.Icc 0 (concentrationCeiling c0 cin) ∧
        T t ∈ Set.Icc (temperatureFloor a h Tin Tc T0)
          (temperatureCeiling a b h A Tin Tc T0 (concentrationCeiling c0 cin))) ∧
      HasDerivAt c (concentrationRhs a cin (arrheniusRateConstant A B (T t)) (c t)) t ∧
      HasDerivAt T
        (temperatureRhs a b h Tin Tc (arrheniusRateConstant A B (T t)) (c t) (T t)) t := by
  have hTm0 : 0 < temperatureFloor a h Tin Tc T0 := temperatureFloor_pos ha hh hTin hTc hT0
  have hκ : ∀ T, flooredRateConstant A B (temperatureFloor a h Tin Tc T0) T ∈ Set.Icc 0 A :=
    flooredRateConstant_mem_Icc hA hB.le hTm0
  have hF := locallyLipschitz_cstrField_flooredRateConstant a b h cin Tin Tc A B hTm0
  obtain ⟨I, x, hx0, -, h0I, hIconn, hsol, hexit⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact
      (E := ℝ × ℝ) Set.univ
      (fun p => cstrField a b h cin Tin Tc
        (flooredRateConstant A B (temperatureFloor a h Tin Tc T0)) p.2)
      0 (c0, T0) isOpen_univ trivial (hF.continuous.comp continuous_snd).continuousOn
      (fun p _ => by
        obtain ⟨K, t, ht, hK⟩ := hF p.2
        refine ⟨K, Set.univ ×ˢ t, prod_mem_nhds Filter.univ_mem ht, fun s y z hy hz => ?_⟩
        exact hK.dist_le_mul y hy.1.2 z hz.1.2)
  have hbox : ∀ t ∈ I, 0 ≤ t →
      (x t).1 ∈ Set.Icc 0 (concentrationCeiling c0 cin) ∧
        (x t).2 ∈ Set.Icc (temperatureFloor a h Tin Tc T0)
          (temperatureCeiling a b h A Tin Tc T0 (concentrationCeiling c0 cin)) := by
    intro t ht ht0
    have hsub : Set.Icc 0 t ⊆ I := hIconn 0 h0I t ht
    exact box_invariant_of_rate_bounds
      (κ := flooredRateConstant A B (temperatureFloor a h Tin Tc T0))
      ha hh hb hcin hc0 hT0 (fun T => (hκ T).1) (fun T _ => (hκ T).2)
      (c := fun s => (x s).1) (T := fun s => (x s).2) (by simp [hx0]) (by simp [hx0])
      (fun s hs => (hasDerivAt_fst_comp (hsol s (hsub hs)).2).hasDerivWithinAt)
      (fun s hs => (hasDerivAt_snd_comp (hsol s (hsub hs)).2).hasDerivWithinAt) ht0
  have hall : ∀ t, 0 ≤ t → t ∈ I := by
    intro t1 ht1
    by_contra hnot
    have hK : IsCompact (Set.Icc (0 : ℝ) t1 ×ˢ (Set.Icc 0 (concentrationCeiling c0 cin) ×ˢ
        Set.Icc (temperatureFloor a h Tin Tc T0)
          (temperatureCeiling a b h A Tin Tc T0 (concentrationCeiling c0 cin)))) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    obtain ⟨⟨c1, hc1I, hc1⟩, -⟩ := hexit _ hK (Set.subset_univ _)
    have ht2I : max c1 0 ∈ I := by
      rcases le_total c1 0 with hc | hc
      · rw [max_eq_right hc]
        exact h0I
      · rw [max_eq_left hc]
        exact hc1I
    have ht2lt : max c1 0 < t1 := by
      by_contra hge
      exact hnot (hIconn 0 h0I (max c1 0) ht2I ⟨ht1, not_lt.mp hge⟩)
    exact hc1 (max c1 0) ht2I (le_max_left _ _)
      ⟨⟨le_max_right _ _, ht2lt.le⟩, hbox (max c1 0) ht2I (le_max_right _ _)⟩
  refine ⟨fun t => (x t).1, fun t => (x t).2, by simp [hx0], by simp [hx0], fun t ht => ?_⟩
  have htI := hall t ht
  obtain ⟨hcb, hTb⟩ := hbox t htI ht
  have hd := (hsol t htI).2
  have heq : flooredRateConstant A B (temperatureFloor a h Tin Tc T0) (x t).2 =
      arrheniusRateConstant A B (x t).2 :=
    flooredRateConstant_eq hTm0.le hTb.1
  refine ⟨⟨hcb, hTb⟩, ?_, ?_⟩
  · have h1 := hasDerivAt_fst_comp hd
    simp only [cstrField] at h1
    rwa [heq] at h1
  · have h2 := hasDerivAt_snd_comp hd
    simp only [cstrField] at h2
    rwa [heq] at h2

end Chemistry.ReactingTransportPorts

end
