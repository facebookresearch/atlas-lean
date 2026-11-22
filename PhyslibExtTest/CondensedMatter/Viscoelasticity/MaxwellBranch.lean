/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.Viscoelasticity.MaxwellBranch
public import MathlibExt.Analysis.ODE.ConstantInputRelaxation
public import PhyslibExt.ContinuumMechanics.EngineeringScaling

/-!
# Tests for `PhyslibExt.CondensedMatter.Viscoelasticity.MaxwellBranch`

The branch `E = 2`, `η = 4` has relaxation time `2`. A held strain of `5`
relaxes a stress starting at `3`; a held stress of `3` creeps from strain `1`
at rate `3 / 4`; an exponential loading history has positive input power and
dissipation. Controls drop each hold, use negative times, flip the relation
and dissipation signs, and evaluate the totalized parameter edges. A
temperature calibration and a pavement-layer calibration exercise calibrated
branches, and the viscosity-over-stress dimension is a time.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.Viscoelasticity.MaxwellBranch

open _root_.Viscoelasticity
open _root_.Viscoelasticity.MaxwellBranch
open Filter Topology

#print axioms Viscoelasticity.MaxwellBranch.isHistory_iff_relaxation
#print axioms Viscoelasticity.MaxwellBranch.IsHistory.hasDerivAt_storedEnergy
#print axioms Viscoelasticity.MaxwellBranch.IsHistory.stress_eq_of_strain_held
#print axioms Viscoelasticity.MaxwellBranch.IsHistory.strain_eq_of_stress_held
#print axioms Viscoelasticity.MaxwellBranch.dissipationRate_pos_iff

/-- Branch `E = 2`, `η = 4`, `τ = 2`. -/
private noncomputable def branch24 : MaxwellBranch := ⟨2, 4, by norm_num, by norm_num⟩

example : branch24.relaxationTime = 2 := by
  simp only [MaxwellBranch.relaxationTime, branch24]; norm_num

/-- heldStrainHistory stress: nonzero decaying stress. -/
private noncomputable def σ1 : ℝ → ℝ := fun t => 3 * Real.exp (-(1 / 2) * t)
/-- heldStrainHistory stress rate. -/
private noncomputable def σ1' : ℝ → ℝ := fun t => -(3 / 2) * Real.exp (-(1 / 2) * t)

/-- heldStrainHistory: held nonzero strain `5`, nonzero relaxing stress, on all of `ℝ`. -/
private lemma heldStrainHistory : branch24.IsHistory Set.univ σ1 σ1' (fun _ => 5) (fun _ => 0) := by
  intro t _
  refine ⟨?_, hasDerivAt_const _ _, ?_⟩
  · unfold σ1 σ1'
    have h := (((hasDerivAt_id' t).const_mul (-(1 / 2 : ℝ))).exp).const_mul 3
    convert h using 1
    ring
  · simp only [σ1, σ1', branch24]; ring

-- T3 applied to heldStrainHistory, and the explicit closed form agrees independently
example (t : ℝ) (ht : 0 ≤ t) :
    σ1 t = σ1 0 * Real.exp (-(branch24.modulus / branch24.viscosity) * t) :=
  IsHistory.stress_eq_of_strain_held (fun t _ => heldStrainHistory t trivial) (fun _ _ => rfl) ht
example (t : ℝ) : σ1 t = σ1 0 * Real.exp (-(branch24.modulus / branch24.viscosity) * t) := by
  simp only [σ1, branch24, mul_zero, Real.exp_zero, mul_one]; norm_num

/-- heldStressHistory: held nonzero stress `3`, creeping strain. -/
private lemma heldStressHistory : branch24.IsHistory Set.univ (fun _ => 3) (fun _ => 0)
    (fun t => 1 + 3 / 4 * t) (fun _ => 3 / 4) := by
  intro t _
  refine ⟨hasDerivAt_const _ _, ?_, ?_⟩
  · have h := ((hasDerivAt_id' t).const_mul (3 / 4 : ℝ)).const_add 1
    convert h using 1
    ring
  · simp only [branch24]; norm_num

example (t : ℝ) (ht : 0 ≤ t) :
    (fun t : ℝ => 1 + 3 / 4 * t) t = (fun t : ℝ => 1 + 3 / 4 * t) 0
      + (fun _ : ℝ => (3 : ℝ)) 0 / branch24.viscosity * t :=
  IsHistory.strain_eq_of_stress_held (fun t _ => heldStressHistory t trivial) (fun _ _ => rfl) ht

/-- loadingHistory: a loading history, every function nonzero, input power and dissipation nonzero.
-/
private lemma loadingHistory : branch24.IsHistory Set.univ Real.exp Real.exp
    (fun t => 3 / 4 * Real.exp t) (fun t => 3 / 4 * Real.exp t) := by
  intro t _
  refine ⟨Real.hasDerivAt_exp t, (Real.hasDerivAt_exp t).const_mul (3 / 4), ?_⟩
  simp only [branch24]; ring

example (t : ℝ) : HasDerivAt (fun s => branch24.storedEnergy (Real.exp s))
    (Real.exp t * (3 / 4 * Real.exp t) - branch24.dissipationRate (Real.exp t)) t :=
  IsHistory.hasDerivAt_storedEnergy loadingHistory (Set.mem_univ t)
example (t : ℝ) :
    0 < Real.exp t * (3 / 4 * Real.exp t) ∧ 0 < branch24.dissipationRate (Real.exp t) :=
  ⟨by positivity, (dissipationRate_pos_iff branch24 _).2 (Real.exp_pos t).ne'⟩

-- Control: `hε` is needed in T3 (heldStressHistory obeys `h`, violates the hold, and the T3 formula
-- fails at 2)
example : ¬ ((fun _ : ℝ => (3 : ℝ)) 2 =
    (fun _ : ℝ => (3 : ℝ)) 0 * Real.exp (-(branch24.modulus / branch24.viscosity) * 2)) := by
  intro h
  have h1 : Real.exp (-(branch24.modulus / branch24.viscosity) * 2) = 1 := by
    have : (3 : ℝ) * 1 = 3 * Real.exp (-(branch24.modulus / branch24.viscosity) * 2)
      := by simpa using h
    linarith
  rw [Real.exp_eq_one_iff] at h1
  simp only [branch24] at h1; norm_num at h1

-- Control: `hσ` is needed in T4 (heldStrainHistory obeys `h`, violates the stress hold, T4 formula
-- fails at 1)
example : ¬ ((fun _ : ℝ => (5 : ℝ)) 1 = (fun _ : ℝ => (5 : ℝ)) 0 + σ1 0 / branch24.viscosity * 1)
  := by
  simp only [σ1, branch24, mul_zero, Real.exp_zero, mul_one]; norm_num

-- Control: `E ≠ 0` is needed in T1: raw E = 0, η = 1 satisfies the series form, not the relaxation
-- form
example : ((1 : ℝ) = 5 / 0 + 1 / 1) ∧ ¬ ((5 : ℝ) + 1 / (1 / 0) = 0 * 1) := by norm_num

-- Control: `0 < η` is needed in T5: raw η = -1 or η = 0 breaks `s ≠ 0 → 0 < s^2/η`
example : ¬ (0 < (1 : ℝ) ^ 2 / (-1)) ∧ ¬ (0 < (1 : ℝ) ^ 2 / 0) := by norm_num

/-- Left-modified relaxation history: obeys the relation and the hold on `Ici 0`, arbitrary for `t ≤
-1`. -/
private noncomputable def σL : ℝ → ℝ := fun t => if -1 < t then 3 * Real.exp (-(1 / 2) * t) else 0

private lemma leftHistoryRelax : branch24.IsHistory (Set.Ici 0) σL σ1' (fun _ => 5) (fun _ => 0)
  := by
  intro t ht
  have ht' : (-1 : ℝ) < t := by have := Set.mem_Ici.mp ht; linarith
  have hev : σL =ᶠ[nhds t] σ1 := by
    filter_upwards [lt_mem_nhds ht'] with u hu
    simp [σL, σ1, hu]
  have hσt : σL t = σ1 t := by simp [σL, σ1, ht']
  refine ⟨((heldStrainHistory t trivial).1).congr_of_eventuallyEq hev, hasDerivAt_const _ _, ?_⟩
  rw [hσt]; exact (heldStrainHistory t trivial).2.2

example : ¬ (σL (-2) = σL 0 * Real.exp (-(branch24.modulus / branch24.viscosity) * (-2))) := by
  simp only [σL, branch24]; norm_num

/-- Left-modified creep history: held stress `3`, creep on `Ici 0`, arbitrary for `t ≤ -1`. -/
private noncomputable def εL : ℝ → ℝ := fun t => if -1 < t then 1 + 3 / 4 * t else 0

private lemma leftHistoryCreep : branch24.IsHistory (Set.Ici 0) (fun _ => 3) (fun _ => 0) εL
    (fun _ => 3 / 4)
  := by
  intro t ht
  have ht' : (-1 : ℝ) < t := by have := Set.mem_Ici.mp ht; linarith
  have hev : εL =ᶠ[nhds t] (fun t => 1 + 3 / 4 * t) := by
    filter_upwards [lt_mem_nhds ht'] with u hu
    simp [εL, hu]
  refine ⟨hasDerivAt_const _ _, ((heldStressHistory t trivial).2.1).congr_of_eventuallyEq hev, ?_⟩
  exact (heldStressHistory t trivial).2.2

example : ¬ (εL (-2) = εL 0 + (fun _ : ℝ => (3 : ℝ)) 0 / branch24.viscosity * (-2)) := by
  simp only [εL, branch24]; norm_num

-- Control: sign control. The pin's relation rejects the growing held-strain history, which the
-- wrong-sign relation `ε' = σ'/E - σ/η` accepts (so T3 is sign-sensitive).
example : ¬ branch24.IsHistory Set.univ (fun t => 3 * Real.exp ((1 / 2) * t))
    (fun t => (3 / 2) * Real.exp ((1 / 2) * t)) (fun _ => 5) (fun _ => 0) := by
  intro h
  have h0 := (h 0 trivial).2.2
  simp only [branch24, mul_zero, Real.exp_zero, mul_one] at h0
  norm_num at h0
example (t : ℝ) :
    (0 : ℝ) = (3 / 2) * Real.exp ((1 / 2) * t) / 2 - 3 * Real.exp ((1 / 2) * t) / 4 := by
  ring

-- Control: dissipation sign control: the sign-flipped balance is false on heldStrainHistory at t =
-- 0
example : ¬ HasDerivAt (fun s => branch24.storedEnergy (σ1 s))
    (σ1 0 * 0 + branch24.dissipationRate (σ1 0)) 0 := by
  intro hbad
  have hgood := IsHistory.hasDerivAt_storedEnergy heldStrainHistory (Set.mem_univ 0)
  have := hbad.unique hgood
  simp only [σ1, branch24, MaxwellBranch.dissipationRate, mul_zero, Real.exp_zero,
    mul_one] at this
  norm_num at this

-- Control: totalized edges read the opposite physical limit (excluded by the record's fields):
-- η = 0 gives `σ/0 = 0` (a rigid dashpot: held strain, stress 3 never relaxes);
-- E = 0 gives `σ'/0 = 0` (a rigid spring: any stress rate with no elastic strain).
example : ((0 : ℝ) = 0 / 2 + 3 / 0) ∧ ((3 / 4 : ℝ) = 7 / 0 + 3 / 4) := by norm_num

-- Control: joint-flip sign rule and evenness (module-doc claims)
example (b : MaxwellBranch) (I : Set ℝ) (σ σ' ε ε' : ℝ → ℝ) :
    b.IsHistory I σ σ' ε ε' ↔
      b.IsHistory I (fun t => -σ t) (fun t => -σ' t) (fun t => -ε t) (fun t => -ε' t) := by
  unfold IsHistory
  refine forall₂_congr fun t _ => ?_
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1.fun_neg, h2.fun_neg, ?_⟩
    beta_reduce
    rw [h3]; ring
  · rintro ⟨h1, h2, h3⟩
    beta_reduce at h1 h2 h3
    refine ⟨by simpa using h1.fun_neg, by simpa using h2.fun_neg, ?_⟩
    linear_combination -h3
example (b : MaxwellBranch) (s : ℝ) :
    b.storedEnergy (-s) = b.storedEnergy s ∧ b.dissipationRate (-s) = b.dissipationRate s := by
  simp [MaxwellBranch.storedEnergy, MaxwellBranch.dissipationRate]

-- Calibration fixture: temperature-dependent modulus and viscosity on a declared domain
/-- Fixture calibration over temperature (°C). -/
private noncomputable def temperatureCalibration : MaxwellCalibration ℝ where
  modulus := fun T => 3000 * Real.exp (-(T - 20) / 15)
  viscosity := fun T => 300 * Real.exp (-(T - 20) / 8)
  domain := Set.Icc (-10) 60
  modulus_pos := fun T _ => by positivity
  viscosity_pos := fun T _ => by positivity

private lemma temp25Mem : (25 : ℝ) ∈ temperatureCalibration.domain
  := by simp only [temperatureCalibration]; constructor <;> norm_num

example : (temperatureCalibration.branch temp25Mem).relaxationTime
    = Real.exp (-(25 - 20) / 8) / (10 * Real.exp (-(25 - 20) / 15)) := by
  simp only [temperatureCalibration, MaxwellCalibration.branch, MaxwellBranch.relaxationTime]
  field_simp
  ring

-- Energy balance at a calibrated branch, in unfolded calibrated form
example {Θ : Type*} (c : MaxwellCalibration Θ) {θ : Θ} (hθ : θ ∈ c.domain) {I : Set ℝ}
    {σ σ' ε ε' : ℝ → ℝ} (h : (c.branch hθ).IsHistory I σ σ' ε ε') {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => σ s ^ 2 / (2 * c.modulus θ))
      (σ t * ε' t - σ t ^ 2 / c.viscosity θ) t :=
  IsHistory.hasDerivAt_storedEnergy h ht

-- The energy algebra also holds for arbitrary real parameters: raw identity
example (E η σ σ' : ℝ) : σ * (σ' / E + σ / η) - σ ^ 2 / η = 2 * σ * σ' / (2 * E) := by ring

/-! ### Calibrated forms, limits, and dimensions -/

-- Held-strain relaxation at a calibrated branch, in unfolded calibrated form.
example {Θ : Type*} (c : MaxwellCalibration Θ) {θ : Θ} (hθ : θ ∈ c.domain)
    {σ σ' ε ε' : ℝ → ℝ} (h : (c.branch hθ).IsHistory (Set.Ici 0) σ σ' ε ε')
    (hε : ∀ t ∈ Set.Ici (0 : ℝ), ε t = ε 0) {t : ℝ} (ht : 0 ≤ t) :
    σ t = σ 0 * Real.exp (-(c.modulus θ / c.viscosity θ) * t) :=
  IsHistory.stress_eq_of_strain_held h hε ht

/-- Pavement-layer calibration fixture: `E = 3000` MPa and `η = 300` MPa s. -/
private noncomputable def pavementCalibration : MaxwellCalibration Unit where
  modulus := fun _ => 3000
  viscosity := fun _ => 300
  domain := Set.univ
  modulus_pos := fun _ _ => by norm_num
  viscosity_pos := fun _ _ => by norm_num

private lemma pavementUnitMem : (Unit.unit : Unit) ∈ pavementCalibration.domain :=
  Set.mem_univ _

example : (pavementCalibration.branch pavementUnitMem).relaxationTime = 1 / 10 := by
  simp only [pavementCalibration, MaxwellCalibration.branch, MaxwellBranch.relaxationTime]
  norm_num

private lemma pavementRelaxationHistory :
    (pavementCalibration.branch pavementUnitMem).IsHistory Set.univ
      (fun t => 3 * Real.exp (-10 * t)) (fun t => -30 * Real.exp (-10 * t))
      (fun _ => 5) (fun _ => 0) := by
  intro t _
  refine ⟨?_, hasDerivAt_const _ _, ?_⟩
  · have h := (((hasDerivAt_id' t).const_mul (-10 : ℝ)).exp).const_mul 3
    convert h using 1
    ring
  · simp only [pavementCalibration, MaxwellCalibration.branch]
    ring

example (t : ℝ) : HasDerivAt
    (fun s => (pavementCalibration.branch pavementUnitMem).storedEnergy
      ((fun u => 3 * Real.exp (-10 * u)) s))
    ((fun u => 3 * Real.exp (-10 * u)) t * 0 -
      (pavementCalibration.branch pavementUnitMem).dissipationRate
        ((fun u => 3 * Real.exp (-10 * u)) t)) t :=
  IsHistory.hasDerivAt_storedEnergy pavementRelaxationHistory (Set.mem_univ t)

example (t : ℝ) (ht : 0 ≤ t) :
    (fun u => 3 * Real.exp (-10 * u)) t =
      (fun u => 3 * Real.exp (-10 * u)) 0 *
        Real.exp (-((pavementCalibration.branch pavementUnitMem).modulus /
          (pavementCalibration.branch pavementUnitMem).viscosity) * t) :=
  IsHistory.stress_eq_of_strain_held
    (fun u _ => pavementRelaxationHistory u trivial) (fun _ _ => rfl) ht

-- Held-strain stress decays to zero, through the constant-input solution limit.
example {b : MaxwellBranch} {σ σ' ε ε' : ℝ → ℝ}
    (h : b.IsHistory (Set.Ici 0) σ σ' ε ε')
    (hε : ∀ t ∈ Set.Ici (0 : ℝ), ε t = ε 0) :
    Tendsto σ atTop (𝓝 0) := by
  have hk : 0 < b.modulus / b.viscosity := div_pos b.modulus_pos b.viscosity_pos
  have hEq : σ =ᶠ[atTop]
      MathlibExt.Biology.Biophysics.CompartmentKinetics.amount
        (b.modulus / b.viscosity) 0 (σ 0) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [IsHistory.stress_eq_of_strain_held h hε ht,
      MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_bolus]
  have hlim := MathlibExt.Biology.Biophysics.CompartmentKinetics.tendsto_amount
    hk (0 : ℝ) (σ 0)
  rw [MathlibExt.Biology.Biophysics.CompartmentKinetics.steadyAmount] at hlim
  simp only [zero_div] at hlim
  exact Tendsto.congr' hEq.symm hlim

-- At a positive held stress, creep is unbounded.
example {b : MaxwellBranch} {σ σ' ε ε' : ℝ → ℝ}
    (h : b.IsHistory (Set.Ici 0) σ σ' ε ε')
    (hσ : ∀ t ∈ Set.Ici (0 : ℝ), σ t = σ 0) (hσ0 : 0 < σ 0) :
    Tendsto ε atTop atTop := by
  have hrate : 0 < σ 0 / b.viscosity := div_pos hσ0 b.viscosity_pos
  have hEq : ε =ᶠ[atTop] fun t => ε 0 + σ 0 / b.viscosity * t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact IsHistory.strain_eq_of_stress_held h hσ ht
  have hlim : Tendsto (fun t => ε 0 + σ 0 / b.viscosity * t) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (ε 0)
      (tendsto_id.const_mul_atTop hrate)
    exact h.congr (fun t => by simp only [id_eq]; ring)
  exact Tendsto.congr' hEq.symm hlim

-- The relaxation formula in relaxation-time form.
example {b : MaxwellBranch} {σ σ' ε ε' : ℝ → ℝ}
    (h : b.IsHistory (Set.Ici 0) σ σ' ε ε')
    (hε : ∀ t ∈ Set.Ici (0 : ℝ), ε t = ε 0) {t : ℝ} (ht : 0 ≤ t) :
    σ t = σ 0 * Real.exp (-t / b.relaxationTime) := by
  rw [IsHistory.stress_eq_of_strain_held h hε ht]
  congr 2
  simp only [MaxwellBranch.relaxationTime]
  field_simp

example (b : MaxwellBranch) (s : ℝ) :
    s / b.relaxationTime = b.modulus / b.viscosity * s := by
  simp only [MaxwellBranch.relaxationTime, div_div_eq_mul_div]
  ring

-- Positive dissipation at stress `1`, with its value on the `E = 2`, `η = 4` branch.
example : 0 < branch24.dissipationRate 1 :=
  (dissipationRate_pos_iff branch24 1).2 one_ne_zero

example : branch24.dissipationRate 1 = 1 / 4 := by
  simp only [branch24, MaxwellBranch.dissipationRate]
  norm_num

-- A dynamic viscosity divided by a stress has the dimension of a time.
example : EngineeringScaling.dynamicViscosityDim / Units.QuantityDimensions.stressDim =
    Dimension.single ISQDimensionBase.time := by
  decide

end PhyslibExtTest.CondensedMatter.Viscoelasticity.MaxwellBranch
