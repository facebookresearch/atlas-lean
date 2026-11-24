/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import MathlibExt.Analysis.ODE.ConstantInputRelaxation

/-!
# Maxwell branch: energy balance and held-strain relaxation

A linear spring and dashpot in series, with stored energy, dissipation,
held-strain relaxation, constant-stress creep, and calibrated branches.

## i. Overview

A Maxwell branch is a linear (Hookean) spring of modulus `E` in series with a
linear (Newtonian) dashpot of viscosity `η`; `0 < E` and `0 < η` are fields of
the record. Its relaxation time is `τ = η / E`. In Maxwell's notation `τ` is
the time of relaxation `T`, and `η = E * T` is the coefficient of viscosity.

The stress history `σ` is tension positive and the strain history `ε` is
extension positive. The supplied rates `σ'` and `ε'` are tied to the histories
by two-sided `HasDerivAt` at every time of the declared time set. In the series
connection, the spring and dashpot carry the same stress and their strains add,
giving `ε' = σ' / E + σ / η`, equivalently `σ' + σ / τ = E * ε'`. The stored
energy per unit volume is `σ ^ 2 / (2 * E)`, the dissipation rate per unit
volume is `σ ^ 2 / η`, and the input power per unit volume is `σ * ε'`.

A strain or stress step at the start of a test is represented by starting the
hold after the step, so histories are differentiable at the hold start, as in
the constant-input relaxation solution API. Then `σ 0` (respectively `ε 0`) is
the post-step value, and Maxwell's `F = ES e^{-t/T}` is the special case
`σ 0 = E * ε 0`. The held-strain and constant-stress closed forms consume
`MathlibExt.Biology.Biophysics.CompartmentKinetics.IsSolution.eq_amount`
with `amount_bolus` and `amount_rate_zero`.

Units are cross-referenced, while statements stay on `ℝ`: `E` and `σ` have
`Units.QuantityDimensions.stressDim`; `η` has
`EngineeringScaling.dynamicViscosityDim`; `τ` has `Dimension.single .time`;
stored energy per unit volume again has the stress dimension; dissipation and
input power per unit volume use `Units.EngineeringQuantities.powerDim` per
unit volume. Every division by `E`, `η`, or `τ` in a physical reading is by a
positive number from the record.

A calibration gives modulus and viscosity as functions of a state `θ` on a
declared domain. Values off that domain are unconstrained and never read.
One branch is in scope; generalized Maxwell series, other rheology models,
temperature-varying laws, damage, and layered structures are excluded.

## ii. Key results

- `Viscoelasticity.MaxwellBranch.relaxationTime`: the relaxation time `η / E`.
- `Viscoelasticity.MaxwellBranch.storedEnergy` and
  `Viscoelasticity.MaxwellBranch.dissipationRate`: spring energy and dashpot
  dissipation per unit volume.
- `Viscoelasticity.MaxwellBranch.IsHistory`: the series constitutive relation.
- `Viscoelasticity.MaxwellBranch.isHistory_iff_relaxation`: equivalence with
  the relaxation form.
- `Viscoelasticity.MaxwellBranch.IsHistory.hasDerivAt_storedEnergy`: input
  power minus dissipation is the stored-energy rate.
- `Viscoelasticity.MaxwellBranch.IsHistory.stress_eq_of_strain_held`:
  exponential stress relaxation at held strain.
- `Viscoelasticity.MaxwellBranch.IsHistory.strain_eq_of_stress_held`:
  linear creep at held stress.
- `Viscoelasticity.MaxwellBranch.dissipationRate_pos_iff`: positive
  dissipation exactly at nonzero stress.
- `Viscoelasticity.MaxwellCalibration.branch`: the branch declared at a
  calibration state in its domain.

## iii. Table of contents

- A. Record and relation
- B. Energy balance and tests of the branch
- C. Calibrated branches

## iv. References

- J. C. Maxwell, "On the dynamical theory of gases", Phil. Trans. R. Soc.
  Lond. 157 (1867) 49-88, DOI `10.1098/rstl.1867.0004`; reprinted in
  *The Scientific Papers of James Clerk Maxwell*, Vol. II (1890), pp. 30-31.
- D. Roylance, *Engineering Viscoelasticity*, Massachusetts Institute of
  Technology (October 24, 2001), section 4.1, pp. 8-10 (Eqn. (22), p. 9;
  Example 2, p. 10), and section 4.2, p. 11.
-/

@[expose] public section

namespace Viscoelasticity

/-! ## A. Record and relation -/

/-- A Maxwell branch: a linear spring of modulus `E` (stress per unit strain) in series with a
linear dashpot of viscosity `η` (stress times time per unit strain), both strictly positive. -/
structure MaxwellBranch where
  /-- Spring modulus `E`. -/
  modulus : ℝ
  /-- Dashpot viscosity `η`. -/
  viscosity : ℝ
  /-- The spring modulus is positive. -/
  modulus_pos : 0 < modulus
  /-- The dashpot viscosity is positive. -/
  viscosity_pos : 0 < viscosity

namespace MaxwellBranch

/-- Relaxation time `τ = η / E` of the branch (Maxwell's time of relaxation). -/
noncomputable def relaxationTime (b : MaxwellBranch) : ℝ :=
  b.viscosity / b.modulus

/-- Energy per unit volume stored in the spring at stress `s`: `s ^ 2 / (2 * E)`, which is
`E * (s / E) ^ 2 / 2` at the spring strain `s / E`. -/
noncomputable def storedEnergy (b : MaxwellBranch) (s : ℝ) : ℝ :=
  s ^ 2 / (2 * b.modulus)

/-- Power per unit volume dissipated in the dashpot at stress `s`: `s ^ 2 / η`, the stress
times the dashpot strain rate `s / η`. -/
noncomputable def dissipationRate (b : MaxwellBranch) (s : ℝ) : ℝ :=
  s ^ 2 / b.viscosity

/-- Canonical constitutive relation of the branch on the time set `I`: at every `t ∈ I` the
stress history `σ` has rate `σ' t`, the strain history `ε` has rate `ε' t`, and the strain
rate is the spring strain rate `σ' t / E` plus the dashpot strain rate `σ t / η`. -/
def IsHistory (b : MaxwellBranch) (I : Set ℝ) (σ σ' ε ε' : ℝ → ℝ) : Prop :=
  ∀ t ∈ I, HasDerivAt σ (σ' t) t ∧ HasDerivAt ε (ε' t) t ∧
    ε' t = σ' t / b.modulus + σ t / b.viscosity

/-- Relaxation form of the canonical relation. For every time set and every history, the
series form `ε' = σ' / E + σ / η` holds exactly when `σ' + σ / τ = E * ε'` with `τ = η / E`:
Maxwell's `dF/dt = E dS/dt - F/T`, with time of relaxation `T = τ` and coefficient of
viscosity `E * T = η` (Roylance, section 4.1, Eqn. (22)). The equivalence uses `E ≠ 0`, from
the record's `0 < E`. -/
theorem isHistory_iff_relaxation (b : MaxwellBranch) (I : Set ℝ) (σ σ' ε ε' : ℝ → ℝ) :
    b.IsHistory I σ σ' ε ε' ↔
      ∀ t ∈ I, HasDerivAt σ (σ' t) t ∧ HasDerivAt ε (ε' t) t ∧
        σ' t + σ t / b.relaxationTime = b.modulus * ε' t := by
  have hE : b.modulus ≠ 0 := ne_of_gt b.modulus_pos
  have hη : b.viscosity ≠ 0 := ne_of_gt b.viscosity_pos
  have halg : ∀ a c s : ℝ, (c = a / b.modulus + s / b.viscosity ↔
      a + s * b.modulus / b.viscosity = b.modulus * c) := by
    intro a c s
    constructor
    · intro hheq
      rw [hheq]
      field_simp
    · intro hheq
      have hmul : b.modulus * c = b.modulus * (a / b.modulus + s / b.viscosity) := by
        rw [← hheq]
        field_simp
      exact mul_left_cancel₀ hE hmul
  constructor
  · intro h t ht
    obtain ⟨hσ, hε, heq⟩ := h t ht
    refine ⟨hσ, hε, ?_⟩
    simp only [MaxwellBranch.relaxationTime, div_div_eq_mul_div]
    exact (halg _ _ _).mp heq
  · intro h t ht
    obtain ⟨hσ, hε, heq⟩ := h t ht
    refine ⟨hσ, hε, ?_⟩
    simp only [MaxwellBranch.relaxationTime, div_div_eq_mul_div] at heq
    exact (halg _ _ _).mpr heq

/-! ## B. Energy balance and tests of the branch -/

/-- Energy balance. Along a history that obeys the canonical relation on `I`, at every time of
`I` the stored energy changes at the input power `σ * ε'` minus the dashpot dissipation:
`(σ ^ 2 / (2 * E))' = σ * ε' - σ ^ 2 / η`. The physical reading is `0 < E` and `0 < η`, the
fields of the record. -/
lemma IsHistory.hasDerivAt_storedEnergy {b : MaxwellBranch} {I : Set ℝ}
    {σ σ' ε ε' : ℝ → ℝ} (h : b.IsHistory I σ σ' ε ε') {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => b.storedEnergy (σ s)) (σ t * ε' t - b.dissipationRate (σ t)) t := by
  obtain ⟨hσ, hε, heq⟩ := h t ht
  have hE : b.modulus ≠ 0 := ne_of_gt b.modulus_pos
  have hη : b.viscosity ≠ 0 := ne_of_gt b.viscosity_pos
  simp only [MaxwellBranch.storedEnergy, MaxwellBranch.dissipationRate]
  have hpow := hσ.pow 2
  have hdiv := hpow.div_const (2 * b.modulus)
  have h21 : ((2 : ℕ) - 1) = 1 := by decide
  have hval : (↑(2 : ℕ) : ℝ) * σ t ^ ((2 : ℕ) - 1) * σ' t / (2 * b.modulus)
      = σ t * ε' t - (σ t) ^ 2 / b.viscosity := by
    rw [h21, pow_one, heq]
    field_simp
    ring
  rw [show σ t * ε' t - (σ t) ^ 2 / b.viscosity
      = (↑(2 : ℕ) : ℝ) * σ t ^ ((2 : ℕ) - 1) * σ' t / (2 * b.modulus) from hval.symm]
  exact hdiv

private lemma deriv_zero_of_const_on_Ici {f f' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt f (f' t) t)
    (hconst : ∀ t ∈ Set.Ici (0 : ℝ), f t = f 0)
    {t : ℝ} (ht : t ∈ Set.Ici (0 : ℝ)) : f' t = 0 := by
  have hxu : UniqueDiffWithinAt ℝ (Set.Ici 0) t := (uniqueDiffOn_Ici 0) t ht
  have hw : HasDerivWithinAt f (f' t) (Set.Ici 0) t := (hderiv t ht).hasDerivWithinAt
  have heq : (fun _ : ℝ => f 0) =ᶠ[nhdsWithin t (Set.Ici 0)] f :=
    Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun x hx => (hconst x hx).symm)
  have hwconst : HasDerivWithinAt (fun _ : ℝ => f 0) (f' t) (Set.Ici 0) t :=
    hw.congr_of_eventuallyEq_of_mem heq ht
  have hw0 : HasDerivWithinAt (fun _ : ℝ => f 0) 0 (Set.Ici 0) t :=
    hasDerivWithinAt_const (c := f 0) (s := Set.Ici 0) (x := t)
  exact UniqueDiffWithinAt.eq_deriv _ hxu hwconst hw0


/-- Held-strain relaxation (the stress relaxation test). If a history obeys the canonical
relation for `t ≥ 0` and the strain is held at its initial value `ε 0` there, then for every
`t ≥ 0` the stress is the existing zero-input exponential decay with removal rate
`E / η = 1 / τ`: `σ t = σ 0 * exp (-(E / η) * t)`, a decay to zero since `0 < E / η`. This is
the `amount_bolus` closed form at removal rate `E / η` (Roylance, Example 2). Here `σ 0` is
the stress at the start of the hold; nothing is claimed for `t < 0`. -/
theorem IsHistory.stress_eq_of_strain_held {b : MaxwellBranch} {σ σ' ε ε' : ℝ → ℝ}
    (h : b.IsHistory (Set.Ici 0) σ σ' ε ε') (hε : ∀ t ∈ Set.Ici (0 : ℝ), ε t = ε 0)
    {t : ℝ} (ht : 0 ≤ t) :
    σ t = σ 0 * Real.exp (-(b.modulus / b.viscosity) * t) := by
  have hE : b.modulus ≠ 0 := ne_of_gt b.modulus_pos
  have hη : b.viscosity ≠ 0 := ne_of_gt b.viscosity_pos
  have hε0 : ∀ s ∈ Set.Ici (0 : ℝ), ε' s = 0 := fun s hs =>
    deriv_zero_of_const_on_Ici (fun u hu => (h u hu).2.1) hε hs
  have hsol : MathlibExt.Biology.Biophysics.CompartmentKinetics.IsSolution
      (b.modulus / b.viscosity) 0 σ := by
    intro s hs
    obtain ⟨hσ, _hε, heq⟩ := h s hs
    rw [hε0 s hs] at heq
    have hσ'eq : σ' s = -(b.modulus / b.viscosity) * σ s := by
      field_simp at heq ⊢
      linear_combination -heq
    have hder : (0 : ℝ) - (b.modulus / b.viscosity) * σ s = σ' s := by
      rw [hσ'eq]
      ring
    rw [hder]
    exact hσ
  have hamount := hsol.eq_amount ht
  rw [MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_bolus] at hamount
  exact hamount

/-- Constant-stress creep (the creep test). If a history obeys the canonical relation for
`t ≥ 0` and the stress is held at its initial value `σ 0` there, then for every `t ≥ 0` the
strain changes linearly at the dashpot strain rate: `ε t = ε 0 + σ 0 / η * t`. For `σ 0 ≠ 0`
this is creep without bound (unrestricted flow) of the single branch; it is not a prediction
of the deformation of a pavement or of any layered structure. This is the
`amount_rate_zero` closed form at input rate `σ 0 / η`. Nothing is claimed for
`t < 0`. -/
lemma IsHistory.strain_eq_of_stress_held {b : MaxwellBranch} {σ σ' ε ε' : ℝ → ℝ}
    (h : b.IsHistory (Set.Ici 0) σ σ' ε ε') (hσ : ∀ t ∈ Set.Ici (0 : ℝ), σ t = σ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ε t = ε 0 + σ 0 / b.viscosity * t := by
  have hσ'0 : ∀ s ∈ Set.Ici (0 : ℝ), σ' s = 0 := fun s hs =>
    deriv_zero_of_const_on_Ici (fun u hu => (h u hu).1) hσ hs
  have hsol : MathlibExt.Biology.Biophysics.CompartmentKinetics.IsSolution
      0 (σ 0 / b.viscosity) ε := by
    intro s hs
    obtain ⟨_hσ, hε, heq⟩ := h s hs
    rw [hσ'0 s hs, hσ s hs] at heq
    have hε'eq : ε' s = σ 0 / b.viscosity := by
      simpa using heq
    have hder : σ 0 / b.viscosity - 0 * ε s = ε' s := by
      rw [hε'eq]
      ring
    rw [hder]
    exact hε
  have hamount := hsol.eq_amount ht
  rw [MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_rate_zero] at hamount
  exact hamount

/-- Positive viscosity: the dashpot dissipates power at every nonzero stress. The dissipation
rate `s ^ 2 / η` is positive exactly when `s ≠ 0`; this uses the record's `0 < η`. -/
lemma dissipationRate_pos_iff (b : MaxwellBranch) (s : ℝ) :
    0 < b.dissipationRate s ↔ s ≠ 0 := by
  simp only [MaxwellBranch.dissipationRate,
    div_pos_iff_of_pos_right b.viscosity_pos, sq_pos_iff]

end MaxwellBranch

/-! ## C. Calibrated branches -/

/-- A temperature/rate calibration of a Maxwell branch: the calibrated spring modulus and
dashpot viscosity as functions of a calibration state `θ` (for example temperature, loading
rate or frequency, and the material), with the declared domain of states on which the
calibration is valid. Both calibrated values are positive on the domain; values off the
domain are unconstrained and never read. -/
structure MaxwellCalibration (Θ : Type*) where
  /-- Calibrated spring modulus at each state. -/
  modulus : Θ → ℝ
  /-- Calibrated dashpot viscosity at each state. -/
  viscosity : Θ → ℝ
  /-- Declared calibration domain. -/
  domain : Set Θ
  /-- The calibrated modulus is positive on the domain. -/
  modulus_pos : ∀ θ ∈ domain, 0 < modulus θ
  /-- The calibrated viscosity is positive on the domain. -/
  viscosity_pos : ∀ θ ∈ domain, 0 < viscosity θ

/-- The Maxwell branch declared by a calibration at a state `θ` of its domain: modulus
`c.modulus θ` and viscosity `c.viscosity θ`. A load history analyzed with this branch holds
the state `θ` fixed. -/
def MaxwellCalibration.branch {Θ : Type*} (c : MaxwellCalibration Θ) {θ : Θ}
    (hθ : θ ∈ c.domain) : MaxwellBranch where
  modulus := c.modulus θ
  viscosity := c.viscosity θ
  modulus_pos := c.modulus_pos θ hθ
  viscosity_pos := c.viscosity_pos θ hθ

end Viscoelasticity
