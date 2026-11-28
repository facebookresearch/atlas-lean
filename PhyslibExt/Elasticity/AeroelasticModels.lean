/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Typical-section static divergence and a circulatory flutter pilot

## i. Overview

A rigid airfoil section on a torsional spring of stiffness `K` about its elastic axis,
in a quasi-steady linear aerodynamic moment model. The twist `θ` (rad) and the rigid
angle of attack `α₀` (rad) are nose-up positive. The lift is `q * S * CLα * (α₀ + θ)`
with dynamic pressure `q`, reference area `S` and lift-curve slope `CLα` (per rad).
The offset `e` is the distance from the elastic axis forward to the aerodynamic centre,
positive when the aerodynamic centre lies ahead of the elastic axis, so the aerodynamic
moment about the elastic axis, nose-up positive, is `q * S * e * CLα * (α₀ + θ)`.

The static moment balance about the elastic axis is `restoringMoment = 0`, where the net
restoring moment is the elastic moment `K * θ` minus the aerodynamic moment. It is affine
in `θ` with slope `K - q * (S * e * CLα)`, the effective stiffness. For `0 < K` and a
positive aerodynamic factor `0 < S * e * CLα`:

* the effective stiffness vanishes exactly at the divergence dynamic pressure
  `qD = K / (S * e * CLα)`, which is positive;
* it is positive exactly below `qD`, and below `qD` the only twist balancing the moment
  with zero rigid angle is `θ = 0`;
* at `qD` every twist, in particular a nonzero one, balances the moment with zero rigid
  angle: a neutral displacement.

The sign of `e * CLα` matters. For a nonpositive factor `S * e * CLα ≤ 0` the effective
stiffness stays positive at every nonnegative dynamic pressure and the division formula
gives no positive pressure. For a zero factor the formula `K / 0` evaluates to `0`, which
is not a pressure at which the stiffness vanishes.

Sections E-J study a declared, dimensionless pilot model of two structural coordinates under a
circulatory (nonconservative) aerodynamic load: damping removes energy, the circulatory load
feeds energy in through the velocity port, and the balance flips from decay to neutral
oscillation to growth as the load parameter `q` rises. The coordinates `z = (z₀, z₁)` are two
modal displacements with unit modal masses, unit modal stiffnesses and modal damping `2`
(critical damping of each mode), in nondimensional time `t`. The aerodynamic load is the
circulatory generalized force `q J z` with `J = [[0, -1], [1, 0]]`, so the model is
`z'' + 2 z' + z - q J z = 0`.

* Structural ports. The model is the force balance `M z'' + D z' + K z = q J z` of the two unit
  modes, `M = 1`, `D = 2`, `K = diagonal (1, 1)`; the identity is already a mass-orthonormal modal
  basis with the repeated modal stiffness `1`. The load enters as a generalized force on the two
  modal coordinates, and its power through the velocity port is `q (J z) ⬝ᵥ z'`; the energy
  `E = (z' ⬝ᵥ z' + z ⬝ᵥ z) / 2` obeys `E' = -2 z' ⬝ᵥ z' + q (J z) ⬝ᵥ z'` on solutions.
* Nonsymmetric load. `Jᵀ = -J`, so `(J v) ⬝ᵥ v = 0`: the load does no work along the displacement
  itself, and the loaded stiffness `1 - q J` has the positive quadratic form `v ⬝ᵥ v` for every
  `q`, hence no static divergence. For `q ≠ 0` it is not symmetric, so the symmetric congruence
  diagonalization behind the modal basis does not apply to it.
* Witnesses. At `q = 0` every solution decays like `(z₀ + t (v₀ + z₀)) e^(-t)`. At `q = 2`,
  `z = (cos t, sin t)` is a solution of constant Euclidean norm `1`, the load power balancing the
  damping. At `q = 8`, `z = e^t (cos 2t, sin 2t)` is a solution of Euclidean norm `e^t`, strictly
  increasing and unbounded, with net power input `6 e^(2t)`.

Norms in the pilot are Euclidean, `√(z ⬝ᵥ z)`: the default sup norm on `Fin 2 → ℝ` is not
monotone along the growing trajectory.

Model inputs: the quasi-steady linear moment law and the linear spring of sections A-D, and the
declared normalized coefficients and circulatory load law of sections E-J. Non-goals: unsteady
aerodynamics, typical-section flutter, the general flutter threshold in `q` of the pilot, a
three-dimensional wing or an aircraft flutter boundary, empirical adequacy and any vehicle or
system safety claim.

## ii. Key results

- `Elasticity.AeroelasticModels.restoringMoment_eq`,
  `Elasticity.AeroelasticModels.hasDerivAt_restoringMoment`: the net restoring moment is
  affine in the twist, with slope the effective stiffness.
- `Elasticity.AeroelasticModels.divergencePressure_pos`,
  `Elasticity.AeroelasticModels.effectiveStiffness_eq_zero_iff`,
  `Elasticity.AeroelasticModels.effectiveStiffness_pos_iff`: the divergence pressure is
  positive, the stiffness vanishes exactly there and is positive exactly below it.
- `Elasticity.AeroelasticModels.eq_zero_of_restoringMoment_eq_zero`,
  `Elasticity.AeroelasticModels.restoringMoment_divergencePressure`,
  `Elasticity.AeroelasticModels.exists_neutral_displacement`: no neutral twist below the
  divergence pressure, every twist neutral at it.
- `Elasticity.AeroelasticModels.coupling_nonpos`,
  `Elasticity.AeroelasticModels.coupling_zero`: the nonpositive and zero aerodynamic factor.
- `Elasticity.AeroelasticModels.circulatoryResidual_eq_ports`,
  `Elasticity.AeroelasticModels.hasDerivAt_energy`: the pilot model as the force balance of the
  two unit modes, and its power port and energy balance.
- `Elasticity.AeroelasticModels.circulatoryJ_transpose`,
  `Elasticity.AeroelasticModels.circulatoryJ_mulVec_dotProduct_self`,
  `Elasticity.AeroelasticModels.loadedStiffness_dotProduct_self`,
  `Elasticity.AeroelasticModels.loadedStiffness_not_isSymm`,
  `Elasticity.AeroelasticModels.loadedStiffness_mulVec_eq_zero_iff`: the nonsymmetric
  circulatory load, without static divergence.
- `Elasticity.AeroelasticModels.neutralMode_solves`,
  `Elasticity.AeroelasticModels.neutralMode_dotProduct_self`,
  `Elasticity.AeroelasticModels.neutralMode_power_balance`: the neutral witness at `q = 2`.
- `Elasticity.AeroelasticModels.growingMode_solves`,
  `Elasticity.AeroelasticModels.growingMode_norm`,
  `Elasticity.AeroelasticModels.growingMode_norm_growing`,
  `Elasticity.AeroelasticModels.growingMode_net_power`: the growing witness at `q = 8`.
- `Elasticity.AeroelasticModels.unloaded_response_eq`,
  `Elasticity.AeroelasticModels.unloaded_tendsto_zero`: every `C²` solution at `q = 0`, by
  linear ODE uniqueness, and its decay.
- `Elasticity.AeroelasticModels.circulatory_witnesses`: the stable, neutral and unstable
  witnesses together.

## iii. Table of contents

- A. Moment model
- B. Effective stiffness
- C. Divergence pressure
- D. Nonpositive and zero aerodynamic factor
- E. The circulatory pilot model and its structural ports
- F. The nonsymmetric circulatory load
- G. The neutral witness at `q = 2`
- H. The growing witness at `q = 8`
- I. Decay at `q = 0`
- J. The three witnesses

## iv. References

- R. L. Bisplinghoff, H. Ashley and R. L. Halfman, *Aeroelasticity*, 1955 (typical section;
  flutter as a dynamic instability of a coupled structural-aerodynamic system).
- D. H. Hodges and G. A. Pierce, *Introduction to Structural Dynamics and Aeroelasticity*,
  2nd edition, 2011 (static divergence of the typical section; divergence versus flutter).
- V. V. Bolotin, *Nonconservative Problems of the Theory of Elastic Stability*, 1963
  (circulatory follower forces and flutter of nonconservative systems).
-/

@[expose] public section

namespace Elasticity.AeroelasticModels

/-! ## A. Moment model -/

/-- Aerodynamic moment about the elastic axis, nose-up positive:
`q * S * e * CLα * (α₀ + θ)`. -/
def aeroMoment (q S e CLα α₀ θ : ℝ) : ℝ :=
  q * S * e * CLα * (α₀ + θ)

/-- Net restoring moment about the elastic axis: the elastic moment `K * θ` minus the
aerodynamic moment. Static equilibrium is `restoringMoment K q S e CLα α₀ θ = 0`. -/
def restoringMoment (K q S e CLα α₀ θ : ℝ) : ℝ :=
  K * θ - aeroMoment q S e CLα α₀ θ

/-- Effective torsional stiffness `K - q * (S * e * CLα)`. -/
def effectiveStiffness (K q S e CLα : ℝ) : ℝ :=
  K - q * (S * e * CLα)

/-- Divergence dynamic pressure `K / (S * e * CLα)`. For a zero aerodynamic factor this
division evaluates to `0`; it is meaningful only for a nonzero factor. -/
noncomputable def divergencePressure (K S e CLα : ℝ) : ℝ :=
  K / (S * e * CLα)

/-! ## B. Effective stiffness -/

/-- The net restoring moment is affine in the twist, with slope the effective
stiffness. -/
lemma restoringMoment_eq (K q S e CLα α₀ θ : ℝ) :
    restoringMoment K q S e CLα α₀ θ =
      effectiveStiffness K q S e CLα * θ - q * (S * e * CLα) * α₀ := by
  unfold restoringMoment aeroMoment effectiveStiffness
  ring

/-- The effective stiffness is the derivative of the net restoring moment with respect
to the twist. -/
lemma hasDerivAt_restoringMoment (K q S e CLα α₀ θ : ℝ) :
    HasDerivAt (restoringMoment K q S e CLα α₀) (effectiveStiffness K q S e CLα) θ := by
  rw [hasDerivAt_iff_isLittleO]
  have h : (fun x' : ℝ => restoringMoment K q S e CLα α₀ x' -
      restoringMoment K q S e CLα α₀ θ - (x' - θ) • effectiveStiffness K q S e CLα) =
      fun _ => 0 := by
    funext x'
    unfold restoringMoment aeroMoment effectiveStiffness
    simp only [smul_eq_mul]
    ring
  rw [h]
  exact Asymptotics.isLittleO_zero _ _

/-! ## C. Divergence pressure -/

/-- For positive stiffness and positive aerodynamic factor the divergence pressure is
positive. -/
lemma divergencePressure_pos {K S e CLα : ℝ} (hK : 0 < K) (hc : 0 < S * e * CLα) :
    0 < divergencePressure K S e CLα := by
  unfold divergencePressure
  exact div_pos hK hc

/-- For a positive aerodynamic factor the effective stiffness vanishes exactly at the
divergence pressure. -/
lemma effectiveStiffness_eq_zero_iff {K q S e CLα : ℝ} (hc : 0 < S * e * CLα) :
    effectiveStiffness K q S e CLα = 0 ↔ q = divergencePressure K S e CLα := by
  have hc' : S * e * CLα ≠ 0 := ne_of_gt hc
  unfold effectiveStiffness divergencePressure
  rw [sub_eq_zero]
  constructor
  · intro h
    rw [eq_div_iff hc']
    linarith
  · intro h
    rw [eq_div_iff hc'] at h
    linarith

/-- For a positive aerodynamic factor the effective stiffness is positive exactly below
the divergence pressure. -/
lemma effectiveStiffness_pos_iff {K q S e CLα : ℝ} (hc : 0 < S * e * CLα) :
    0 < effectiveStiffness K q S e CLα ↔ q < divergencePressure K S e CLα := by
  unfold effectiveStiffness divergencePressure
  rw [sub_pos, lt_div_iff₀ hc]

/-- For `0 < S e CLα`, below the divergence pressure the only twist balancing the moment with
zero rigid angle is `θ = 0`. -/
lemma eq_zero_of_restoringMoment_eq_zero {K q S e CLα θ : ℝ} (hc : 0 < S * e * CLα)
    (hq : q < divergencePressure K S e CLα) (hθ : restoringMoment K q S e CLα 0 θ = 0) :
    θ = 0 := by
  have hpos : 0 < effectiveStiffness K q S e CLα :=
    (effectiveStiffness_pos_iff hc).mpr hq
  have hne : effectiveStiffness K q S e CLα ≠ 0 := ne_of_gt hpos
  have heq := restoringMoment_eq K q S e CLα 0 θ
  rw [hθ] at heq
  simp only [mul_zero, sub_zero] at heq
  have heq' : effectiveStiffness K q S e CLα * θ = 0 := heq.symm
  exact (mul_eq_zero.mp heq').resolve_left hne

/-- For `S e CLα ≠ 0`, at the divergence pressure every twist balances the moment with zero
rigid angle. -/
lemma restoringMoment_divergencePressure {K S e CLα : ℝ} (hc : S * e * CLα ≠ 0)
    (θ : ℝ) : restoringMoment K (divergencePressure K S e CLα) S e CLα 0 θ = 0 := by
  have heq := restoringMoment_eq K (divergencePressure K S e CLα) S e CLα 0 θ
  have hK : effectiveStiffness K (divergencePressure K S e CLα) S e CLα = 0 := by
    unfold effectiveStiffness divergencePressure
    rw [div_mul_cancel₀ _ hc, sub_self]
  rw [heq, hK]
  simp

/-- Neutral displacement: the divergence pressure is positive and a nonzero twist
balances the moment there with zero rigid angle. -/
lemma exists_neutral_displacement {K S e CLα : ℝ} (hK : 0 < K) (hc : 0 < S * e * CLα) :
    0 < divergencePressure K S e CLα ∧
      ∃ θ : ℝ, θ ≠ 0 ∧ restoringMoment K (divergencePressure K S e CLα) S e CLα 0 θ = 0 := by
  exact ⟨divergencePressure_pos hK hc, 1, one_ne_zero,
    restoringMoment_divergencePressure (ne_of_gt hc) 1⟩

/-! ## D. Nonpositive and zero aerodynamic factor -/

/-- Nonpositive factor branch: for `0 < K` and `S e CLα ≤ 0`, the division formula gives no
positive pressure, and the effective stiffness stays positive at every nonnegative dynamic
pressure. -/
lemma coupling_nonpos {K S e CLα : ℝ} (hK : 0 < K) (hc : S * e * CLα ≤ 0) :
    divergencePressure K S e CLα ≤ 0 ∧
      ∀ q : ℝ, 0 ≤ q → 0 < effectiveStiffness K q S e CLα := by
  constructor
  · unfold divergencePressure
    exact div_nonpos_of_nonneg_of_nonpos (le_of_lt hK) hc
  · intro q hq
    unfold effectiveStiffness
    have hqc : q * (S * e * CLα) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq hc
    linarith

/-- Zero factor: for `0 < K` and `S e CLα = 0`, the division formula evaluates to `0` and no
dynamic pressure makes the effective stiffness vanish. -/
lemma coupling_zero {K S e CLα : ℝ} (hK : 0 < K) (hc : S * e * CLα = 0) :
    divergencePressure K S e CLα = 0 ∧ ¬ ∃ q : ℝ, effectiveStiffness K q S e CLα = 0 := by
  constructor
  · unfold divergencePressure
    rw [hc, div_zero]
  · rintro ⟨q, hq⟩
    unfold effectiveStiffness at hq
    rw [hc, mul_zero, sub_zero] at hq
    exact ne_of_gt hK hq

open Filter Matrix Topology

/-! ## E. The circulatory pilot model and its structural ports -/

/-- The circulatory load operator `J = [[0, -1], [1, 0]]`, the quarter turn of the two
structural coordinates. -/
def circulatoryJ : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; 1, 0]

/-- The circulatory aerodynamic generalized force `q J z` on the two structural coordinates. -/
def circulatoryForce (q : ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  q • (circulatoryJ *ᵥ z)

/-- The residual `z'' + 2 z' + z - q J z` of the normalized circulatory model at time `t`; a
solution makes it vanish at every `t`. -/
noncomputable def circulatoryResidual (q : ℝ) (z : ℝ → Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  deriv (deriv z) t + (2 : ℝ) • deriv z t + z t - q • (circulatoryJ *ᵥ z t)

/-- Force port: the model is the force balance `M z'' + D z' + K z - q J z` of the two unit
modes, with mass `M = 1`, damping `D = 2` and modal stiffness `K = diagonal (1, 1)`, driven by
the circulatory generalized force. -/
lemma circulatoryResidual_eq_ports (q : ℝ) (z : ℝ → Fin 2 → ℝ) (t : ℝ) :
    circulatoryResidual q z t =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ deriv (deriv z) t +
        (2 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ deriv z t +
        Matrix.diagonal (fun _ => (1 : ℝ)) *ᵥ z t - circulatoryForce q (z t) := by
  ext i
  simp [circulatoryResidual, circulatoryForce]

/-- Product rule for the dot product of two vector-valued functions on `Fin 2`. -/
private lemma hasDerivAt_dotProduct {f g : ℝ → Fin 2 → ℝ} {f' g' : Fin 2 → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⬝ᵥ g s) (f' ⬝ᵥ g t + f t ⬝ᵥ g') t := by
  have hfi := hasDerivAt_pi.mp hf
  have hgi := hasDerivAt_pi.mp hg
  have h := ((hfi 0).mul (hgi 0)).add ((hfi 1).mul (hgi 1))
  simp only [dotProduct, Fin.sum_univ_two]
  convert h using 1
  ring

/-- Second-order regularity: a `C²` function and its derivative are differentiable. -/
private lemma differentiable_of_contDiff_two {z : ℝ → Fin 2 → ℝ} (hz : ContDiff ℝ 2 z) :
    Differentiable ℝ z ∧ Differentiable ℝ (deriv z) :=
  ⟨hz.differentiable (by norm_num),
    ((contDiff_succ_iff_deriv (n := 1)).mp hz).2.2.differentiable (by norm_num)⟩

/-- Power port and energy balance: for every `C²` trajectory the energy
`E = (z' ⬝ᵥ z' + z ⬝ᵥ z) / 2` has derivative `R ⬝ᵥ z' - 2 z' ⬝ᵥ z' + (q J z) ⬝ᵥ z'`, where `R` is
the model residual. On solutions the damping removes `2 z' ⬝ᵥ z'` and the circulatory load
supplies the port power `(q J z) ⬝ᵥ z'`. -/
lemma hasDerivAt_energy (q : ℝ) {z : ℝ → Fin 2 → ℝ} (hz : ContDiff ℝ 2 z) (t : ℝ) :
    HasDerivAt (fun s => (deriv z s ⬝ᵥ deriv z s + z s ⬝ᵥ z s) / 2)
      (circulatoryResidual q z t ⬝ᵥ deriv z t - 2 * (deriv z t ⬝ᵥ deriv z t) +
        circulatoryForce q (z t) ⬝ᵥ deriv z t) t := by
  obtain ⟨hd1, hd2⟩ := differentiable_of_contDiff_two hz
  have h1 := hasDerivAt_dotProduct (hd2 t).hasDerivAt (hd2 t).hasDerivAt
  have h2 := hasDerivAt_dotProduct (hd1 t).hasDerivAt (hd1 t).hasDerivAt
  have h := (h1.add h2).div_const 2
  convert h using 1
  simp only [circulatoryResidual, circulatoryForce, add_dotProduct, sub_dotProduct,
    smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm (z t) (deriv z t), dotProduct_comm (deriv (deriv z) t) (deriv z t)]
  ring

/-! ## F. The nonsymmetric circulatory load -/

/-- The circulatory operator is skew: `Jᵀ = -J`. -/
lemma circulatoryJ_transpose : circulatoryJᵀ = -circulatoryJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [circulatoryJ]

/-- The circulatory load does no work along the displacement itself: `(J v) ⬝ᵥ v = 0`. -/
lemma circulatoryJ_mulVec_dotProduct_self (v : Fin 2 → ℝ) : (circulatoryJ *ᵥ v) ⬝ᵥ v = 0 := by
  simp [circulatoryJ, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The loaded stiffness `1 - q J` has the positive quadratic form `v ⬝ᵥ v` for every `q`. -/
lemma loadedStiffness_dotProduct_self (q : ℝ) (v : Fin 2 → ℝ) :
    v ⬝ᵥ ((1 - q • circulatoryJ) *ᵥ v) = v ⬝ᵥ v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, dotProduct_comm v (circulatoryJ *ᵥ v), circulatoryJ_mulVec_dotProduct_self,
    smul_zero, sub_zero]

/-- For `q ≠ 0` the loaded stiffness `1 - q J` is not symmetric, hence not positive
semidefinite in Mathlib's sense: the symmetric congruence diagonalization behind a
mass-orthonormal modal basis does not apply to it. -/
lemma loadedStiffness_not_isSymm {q : ℝ} (hq : q ≠ 0) :
    ¬ (1 - q • circulatoryJ).IsSymm ∧ ¬ (1 - q • circulatoryJ).PosSemidef := by
  have hentry : (1 - q • circulatoryJ) 0 1 = q ∧ (1 - q • circulatoryJ) 1 0 = -q := by
    simp [circulatoryJ]
  have hsymm : ¬ (1 - q • circulatoryJ).IsSymm := by
    intro h
    have := h.apply 0 1
    rw [hentry.1, hentry.2] at this
    exact hq (by linarith)
  refine ⟨hsymm, fun h => hsymm ?_⟩
  have hh := h.isHermitian
  ext i j
  have := hh.apply i j
  simpa using this

/-- No static divergence at any `q`: the loaded stiffness has trivial kernel, so the static
balance `(1 - q J) z = 0` has only `z = 0`. -/
lemma loadedStiffness_mulVec_eq_zero_iff (q : ℝ) (v : Fin 2 → ℝ) :
    (1 - q • circulatoryJ) *ᵥ v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have := loadedStiffness_dotProduct_self q v
    rw [h, dotProduct_zero] at this
    exact dotProduct_self_eq_zero.mp this.symm
  · rintro rfl
    exact Matrix.mulVec_zero _

/-! ## G. The neutral witness at `q = 2` -/

/-- The neutral trajectory `z(t) = (cos t, sin t)`. -/
noncomputable def neutralMode (t : ℝ) : Fin 2 → ℝ :=
  ![Real.cos t, Real.sin t]

/-- Derivative of a pair of real functions as a vector in `Fin 2 → ℝ`. -/
private lemma hasDerivAt_vec2 {f g : ℝ → ℝ} {f' g' t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) : HasDerivAt (fun s => ![f s, g s]) ![f', g'] t := by
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  · simpa using hf
  · simpa using hg

/-- The derivative of `t ↦ (cos t, sin t)`, as a function. -/
private lemma deriv_cos_sin :
    deriv (fun t => ![Real.cos t, Real.sin t]) = fun t => ![-Real.sin t, Real.cos t] := by
  funext t
  exact (hasDerivAt_vec2 (Real.hasDerivAt_cos t) (Real.hasDerivAt_sin t)).deriv

/-- First derivative of the neutral trajectory: `z' = (-sin t, cos t)`. -/
lemma hasDerivAt_neutralMode (t : ℝ) :
    HasDerivAt neutralMode ![-Real.sin t, Real.cos t] t := by
  exact hasDerivAt_vec2 (Real.hasDerivAt_cos t) (Real.hasDerivAt_sin t)

/-- Second derivative of the neutral trajectory: `z'' = (-cos t, -sin t)`. -/
lemma hasDerivAt_deriv_neutralMode (t : ℝ) :
    HasDerivAt (deriv neutralMode) ![-Real.cos t, -Real.sin t] t := by
  rw [show neutralMode = fun t => ![Real.cos t, Real.sin t] from rfl, deriv_cos_sin]
  exact hasDerivAt_vec2 (Real.hasDerivAt_sin t).neg (Real.hasDerivAt_cos t)

/-- At `q = 2` the neutral trajectory solves the model. -/
lemma neutralMode_solves (t : ℝ) : circulatoryResidual 2 neutralMode t = 0 := by
  rw [circulatoryResidual, (hasDerivAt_deriv_neutralMode t).deriv,
    show neutralMode = fun t => ![Real.cos t, Real.sin t] from rfl, deriv_cos_sin]
  ext i
  fin_cases i <;> simp [circulatoryJ]

/-- The neutral trajectory has constant Euclidean norm `1`: nonzero and not decaying. -/
lemma neutralMode_dotProduct_self (t : ℝ) : neutralMode t ⬝ᵥ neutralMode t = 1 := by
  simp only [neutralMode, dotProduct, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination Real.cos_sq_add_sin_sq t

/-- Neutral power balance: on the neutral trajectory the circulatory port power equals the
damping loss, `(2 J z) ⬝ᵥ z' = 2 z' ⬝ᵥ z' = 2`. -/
lemma neutralMode_power_balance (t : ℝ) :
    circulatoryForce 2 (neutralMode t) ⬝ᵥ deriv neutralMode t =
        2 * (deriv neutralMode t ⬝ᵥ deriv neutralMode t) ∧
      2 * (deriv neutralMode t ⬝ᵥ deriv neutralMode t) = 2 := by
  rw [show neutralMode = fun t => ![Real.cos t, Real.sin t] from rfl, deriv_cos_sin]
  simp [circulatoryForce, circulatoryJ, dotProduct, Fin.sum_univ_two]
  constructor
  · ring
  · nlinarith [Real.sin_sq_add_cos_sq t]

/-! ## H. The growing witness at `q = 8` -/

/-- The growing trajectory `z(t) = e^t (cos 2t, sin 2t)`. -/
noncomputable def growingMode (t : ℝ) : Fin 2 → ℝ :=
  Real.exp t • ![Real.cos (2 * t), Real.sin (2 * t)]

/-- Derivative of `e^t (A cos 2t + B sin 2t)`. -/
private lemma hasDerivAt_exp_trig (A B t : ℝ) :
    HasDerivAt (fun s => Real.exp s * (A * Real.cos (2 * s) + B * Real.sin (2 * s)))
      (Real.exp t * ((A + 2 * B) * Real.cos (2 * t) + (B - 2 * A) * Real.sin (2 * t))) t := by
  have h2 : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
  have h := (Real.hasDerivAt_exp t).mul ((h2.cos.const_mul A).add (h2.sin.const_mul B))
  convert h using 1
  simp only [Pi.add_apply]
  ring

/-- Derivative of `e^t (A₀ cos 2t + B₀ sin 2t, A₁ cos 2t + B₁ sin 2t)`. -/
private lemma hasDerivAt_growingVec (A₀ B₀ A₁ B₁ t : ℝ) :
    HasDerivAt (fun s => Real.exp s • ![A₀ * Real.cos (2 * s) + B₀ * Real.sin (2 * s),
      A₁ * Real.cos (2 * s) + B₁ * Real.sin (2 * s)])
      (Real.exp t • ![(A₀ + 2 * B₀) * Real.cos (2 * t) + (B₀ - 2 * A₀) * Real.sin (2 * t),
        (A₁ + 2 * B₁) * Real.cos (2 * t) + (B₁ - 2 * A₁) * Real.sin (2 * t)]) t := by
  have e : (fun s => Real.exp s • ![A₀ * Real.cos (2 * s) + B₀ * Real.sin (2 * s),
      A₁ * Real.cos (2 * s) + B₁ * Real.sin (2 * s)]) =
      fun s => ![Real.exp s * (A₀ * Real.cos (2 * s) + B₀ * Real.sin (2 * s)),
        Real.exp s * (A₁ * Real.cos (2 * s) + B₁ * Real.sin (2 * s))] := by
    funext s
    ext i
    fin_cases i <;> simp
  rw [e]
  convert hasDerivAt_vec2 (hasDerivAt_exp_trig A₀ B₀ t) (hasDerivAt_exp_trig A₁ B₁ t) using 1
  ext i
  fin_cases i <;> simp

/-- The growing trajectory in the `A cos 2t + B sin 2t` coordinates. -/
private lemma exp_smul_cos_sin_eq :
    (fun s => Real.exp s • ![Real.cos (2 * s), Real.sin (2 * s)]) =
      fun s => Real.exp s • ![1 * Real.cos (2 * s) + 0 * Real.sin (2 * s),
        0 * Real.cos (2 * s) + 1 * Real.sin (2 * s)] := by
  funext s
  simp

/-- The derivative of the growing trajectory, as a function. -/
private lemma deriv_exp_smul_cos_sin :
    deriv (fun s => Real.exp s • ![Real.cos (2 * s), Real.sin (2 * s)]) = fun t => Real.exp t •
      ![1 * Real.cos (2 * t) + (-2) * Real.sin (2 * t),
        2 * Real.cos (2 * t) + 1 * Real.sin (2 * t)] := by
  funext t
  rw [exp_smul_cos_sin_eq, (hasDerivAt_growingVec 1 0 0 1 t).deriv]
  congr 1
  ext i
  fin_cases i <;> simp

/-- First derivative of the growing trajectory:
`z' = e^t (cos 2t - 2 sin 2t, sin 2t + 2 cos 2t)`. -/
lemma hasDerivAt_growingMode (t : ℝ) :
    HasDerivAt growingMode
      (Real.exp t • ![Real.cos (2 * t) - 2 * Real.sin (2 * t),
        Real.sin (2 * t) + 2 * Real.cos (2 * t)]) t := by
  rw [show growingMode = fun s => Real.exp s • ![Real.cos (2 * s), Real.sin (2 * s)] from rfl,
    exp_smul_cos_sin_eq]
  convert hasDerivAt_growingVec 1 0 0 1 t using 1
  congr 1
  ext i
  fin_cases i <;> simp <;> ring

/-- Second derivative of the growing trajectory:
`z'' = e^t (-3 cos 2t - 4 sin 2t, -3 sin 2t + 4 cos 2t)`. -/
lemma hasDerivAt_deriv_growingMode (t : ℝ) :
    HasDerivAt (deriv growingMode)
      (Real.exp t • ![-3 * Real.cos (2 * t) - 4 * Real.sin (2 * t),
        -3 * Real.sin (2 * t) + 4 * Real.cos (2 * t)]) t := by
  rw [show growingMode = fun s => Real.exp s • ![Real.cos (2 * s), Real.sin (2 * s)] from rfl,
    deriv_exp_smul_cos_sin]
  convert hasDerivAt_growingVec 1 (-2) 2 1 t using 1
  congr 1
  ext i
  fin_cases i <;> simp <;> ring

/-- At `q = 8` the growing trajectory solves the model. -/
lemma growingMode_solves (t : ℝ) : circulatoryResidual 8 growingMode t = 0 := by
  rw [circulatoryResidual, (hasDerivAt_deriv_growingMode t).deriv,
    show growingMode = fun s => Real.exp s • ![Real.cos (2 * s), Real.sin (2 * s)] from rfl,
    deriv_exp_smul_cos_sin]
  ext i
  fin_cases i <;> simp [circulatoryJ] <;> ring

/-- The growing trajectory has Euclidean norm `e^t`. -/
lemma growingMode_norm (t : ℝ) : √(growingMode t ⬝ᵥ growingMode t) = Real.exp t := by
  have h : growingMode t ⬝ᵥ growingMode t = Real.exp t ^ 2 := by
    simp [growingMode, dotProduct, Fin.sum_univ_two]
    linear_combination Real.exp t ^ 2 * Real.cos_sq_add_sin_sq (2 * t)
  rw [h, Real.sqrt_sq (Real.exp_pos t).le]

/-- The Euclidean norm of the growing trajectory is strictly increasing and unbounded. -/
lemma growingMode_norm_growing :
    StrictMono (fun t => √(growingMode t ⬝ᵥ growingMode t)) ∧
      Tendsto (fun t => √(growingMode t ⬝ᵥ growingMode t)) atTop atTop := by
  have h : (fun t => √(growingMode t ⬝ᵥ growingMode t)) = Real.exp :=
    funext growingMode_norm
  rw [h]
  exact ⟨Real.exp_strictMono, Real.tendsto_exp_atTop⟩

/-- Net power input on the growing trajectory: at every time `t` the circulatory port power minus
the damping loss is `6 e^(2t)`. -/
lemma growingMode_net_power (t : ℝ) :
    circulatoryForce 8 (growingMode t) ⬝ᵥ deriv growingMode t -
        2 * (deriv growingMode t ⬝ᵥ deriv growingMode t) = 6 * Real.exp (2 * t) := by
  rw [show growingMode = fun s => Real.exp s • ![Real.cos (2 * s), Real.sin (2 * s)] from rfl,
    deriv_exp_smul_cos_sin]
  have he : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [two_mul, Real.exp_add, sq]
  rw [he]
  simp [circulatoryForce, circulatoryJ, dotProduct, Fin.sum_univ_two]
  linear_combination (6 * Real.exp t ^ 2) * Real.cos_sq_add_sin_sq (2 * t)

/-! ## I. Decay at `q = 0` -/

/-- The `q = 0` model as a first-order linear system on positions and velocities. -/
private noncomputable def dampedField :
    (Fin 2 → ℝ) × (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (ContinuousLinearMap.snd ℝ _ _).prod
    ((-1 : ℝ) • ContinuousLinearMap.fst ℝ _ _ + (-2 : ℝ) • ContinuousLinearMap.snd ℝ _ _)

/-- The explicit `q = 0` response, its derivative and its second derivative. -/
private lemma hasDerivAt_decayResponse (z₀ w : Fin 2 → ℝ) (s : ℝ) :
    HasDerivAt (fun s => Real.exp (-s) • (z₀ + s • w)) (Real.exp (-s) • (w - z₀ - s • w)) s ∧
      HasDerivAt (fun s => Real.exp (-s) • (w - z₀ - s • w))
        (Real.exp (-s) • (z₀ - (2 : ℝ) • w + s • w)) s := by
  have he : HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-s)) s :=
    (hasDerivAt_neg s).exp.congr_deriv (by ring)
  have h1 : HasDerivAt (fun s : ℝ => z₀ + s • w) w s := by
    simpa using ((hasDerivAt_id s).smul_const w).const_add z₀
  have h2 : HasDerivAt (fun s : ℝ => w - z₀ - s • w) (-w) s := by
    simpa using ((hasDerivAt_id s).smul_const w).const_sub (w - z₀)
  refine ⟨?_, ?_⟩
  · convert he.smul h1 using 1
    ext i
    simp
    ring
  · convert he.smul h2 using 1
    ext i
    simp
    ring

/-- Full response at `q = 0`, by linear ODE uniqueness: every `C²` solution is
`z(t) = e^(-t) (z(0) + t (z'(0) + z(0)))`. -/
lemma unloaded_response_eq {z : ℝ → Fin 2 → ℝ} (hz : ContDiff ℝ 2 z)
    (hsol : ∀ t, circulatoryResidual 0 z t = 0) (t : ℝ) :
    z t = Real.exp (-t) • (z 0 + t • (deriv z 0 + z 0)) := by
  obtain ⟨hd1, hd2⟩ := differentiable_of_contDiff_two hz
  set w := deriv z 0 + z 0 with hw
  have hzz : ∀ s, deriv (deriv z) s = -z s - (2 : ℝ) • deriv z s := by
    intro s
    have h := hsol s
    simp only [circulatoryResidual, zero_smul, sub_zero] at h
    rw [← sub_eq_zero, ← h]
    abel
  have hf : ∀ s, HasDerivAt (fun s => (z s, deriv z s)) (dampedField (z s, deriv z s)) s ∧
      (z s, deriv z s) ∈ (Set.univ : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))) := by
    intro s
    refine ⟨?_, Set.mem_univ _⟩
    convert (hd1 s).hasDerivAt.prodMk (hd2 s).hasDerivAt using 1
    rw [hzz s]
    refine Prod.ext rfl ?_
    ext i
    simp [dampedField]
    ring
  have hg : ∀ s, HasDerivAt (fun s => (Real.exp (-s) • (z 0 + s • w),
        Real.exp (-s) • (w - z 0 - s • w)))
      (dampedField (Real.exp (-s) • (z 0 + s • w), Real.exp (-s) • (w - z 0 - s • w))) s ∧
      (Real.exp (-s) • (z 0 + s • w), Real.exp (-s) • (w - z 0 - s • w)) ∈
        (Set.univ : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ))) := by
    intro s
    refine ⟨?_, Set.mem_univ _⟩
    obtain ⟨h1, h2⟩ := hasDerivAt_decayResponse (z 0) w s
    convert h1.prodMk h2 using 1
    refine Prod.ext rfl ?_
    ext i
    simp [dampedField]
    ring
  have heq := ODE_solution_unique_univ (v := fun _ p => dampedField p)
    (s := fun _ => Set.univ) (t₀ := 0)
    (fun _ => dampedField.lipschitzWith.lipschitzOnWith) hf hg (by
      simp only [neg_zero, Real.exp_zero, one_smul, zero_smul, add_zero, sub_zero]
      ext i <;> simp [hw])
  have := congrArg Prod.fst (congrFun heq t)
  simpa using this

/-- Decay at `q = 0`: every `C²` solution tends to `0`. -/
lemma unloaded_tendsto_zero {z : ℝ → Fin 2 → ℝ} (hz : ContDiff ℝ 2 z)
    (hsol : ∀ t, circulatoryResidual 0 z t = 0) : Tendsto z atTop (𝓝 0) := by
  have h : z = fun t => Real.exp (-t) • z 0 + (t ^ 1 * Real.exp (-t)) • (deriv z 0 + z 0) := by
    funext t
    rw [unloaded_response_eq hz hsol t, smul_add, smul_smul]
    congr 1
    ring_nf
  rw [h]
  have h1 := Real.tendsto_exp_neg_atTop_nhds_zero.smul_const (z 0)
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).smul_const (deriv z 0 + z 0)
  simpa using h1.add h2

/-! ## J. The three witnesses -/

/-- Stable, neutral and unstable witnesses of the declared model: at `q = 0` every `C²`
solution decays; at `q = 2` a solution keeps Euclidean norm `1`; at `q = 8` a solution has
unbounded Euclidean norm. Three sample loads, not a threshold classification in `q`. -/
lemma circulatory_witnesses :
    (∀ z : ℝ → Fin 2 → ℝ, ContDiff ℝ 2 z → (∀ t, circulatoryResidual 0 z t = 0) →
        Tendsto z atTop (𝓝 0)) ∧
      (∀ t, circulatoryResidual 2 neutralMode t = 0 ∧
        √(neutralMode t ⬝ᵥ neutralMode t) = 1) ∧
      (∀ t, circulatoryResidual 8 growingMode t = 0) ∧
      Tendsto (fun t => √(growingMode t ⬝ᵥ growingMode t)) atTop atTop := by
  refine ⟨fun z hz hsol => unloaded_tendsto_zero hz hsol, fun t => ⟨neutralMode_solves t, ?_⟩,
    growingMode_solves, growingMode_norm_growing.2⟩
  rw [neutralMode_dotProduct_self, Real.sqrt_one]

end Elasticity.AeroelasticModels

end
