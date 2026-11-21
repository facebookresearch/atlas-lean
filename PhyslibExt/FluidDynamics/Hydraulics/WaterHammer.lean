/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Physlib.ClassicalMechanics.WaveEquation.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Water-hammer wave-equation adapter

## i. Overview

For the linear frictionless water-hammer pair for head `h` and discharge
`q` (time first),
`h_t + (a^2 / (g * A)) * q_x = 0` and `q_t + (g * A) * h_x = 0`, with
wave speed `a > 0`, gravity `g > 0`, and pipe area `A > 0`, this file
eliminates one field to obtain the scalar second-order wave equations
`h_tt = a^2 * h_xx` and `q_tt = a^2 * q_xx`, and transports them to
Physlib's `ClassicalMechanics.WaveEquation` predicate at `d = 1` with
speed `a`. The convention is that of the sibling energy theorem
`FluidDynamics.WaterHammerEnergy.energy_hasDerivAt`; fields are on the
whole line and all partial derivatives are supplied fields with
`HasDerivAt` slice witnesses. A scalar field is transported by
`scalarWaveField φ t x = WithLp.toLp 2 (fun _ => φ t.val (x 0))`, where
`x 0` is the single coordinate of `Space 1` (the value of
`Space.oneEquiv x`).

Given the other premises, the mixed-partial equalities are pointwise
equivalent to the corresponding wave equations; no claim is made that
data violating those equalities exist under the global premises. The
deriv-form shallow-water analogue is
`EarthScience.shallow_water_wave_eq`.

Not claimed: the Physlib predicate is pointwise on the whole line, so
this file carries no pipe-end, interval, or boundary-energy statement;
boundary energy flux stays with
`FluidDynamics.WaterHammerEnergy.energy_hasDerivAt`. No valve,
friction, or boundary model, and no adapter for `Space d` with `d ≠ 1`,
is given. Units: `h` is a head (length), `q` a discharge, `a` a speed,
and all derivative fields use the same coherent unit system as the
sibling energy theorem.

## ii. Key results

- `FluidDynamics.WaterHammer.laplacianVec_scalarWaveField` and
  `FluidDynamics.WaterHammer.deriv_deriv_scalarWaveField`: the two
  `Space 1`/`Time` derivative adapters.
- `FluidDynamics.WaterHammer.head_wave_iff_mixed` and
  `FluidDynamics.WaterHammer.discharge_wave_iff_mixed`: pointwise
  mixed-partial criteria.
- `FluidDynamics.WaterHammer.head_wave` and
  `FluidDynamics.WaterHammer.discharge_wave`: the eliminations.
- `FluidDynamics.WaterHammer.waveEquation_head` and
  `FluidDynamics.WaterHammer.waveEquation_discharge`: the transported
  fields satisfy `ClassicalMechanics.WaveEquation` at speed `a`.

## iii. Table of contents

- A. Scalar transport and derivative adapters
- B. Mixed-partial criteria and eliminations
- C. Physlib wave-equation maps

## iv. References

- E. B. Wylie and V. L. Streeter, *Fluid Transients in Systems*,
  Prentice Hall, 1993 (linear water-hammer equations).
- Physlib `ClassicalMechanics.WaveEquation.Basic` for the target
  predicate `ClassicalMechanics.WaveEquation`.
-/

@[expose] public section

namespace FluidDynamics.WaterHammer

open Space Time

/-! ## A. Scalar transport and derivative adapters -/

/-- A scalar field `φ t x` (time first) as a field `Time → Space 1 → EuclideanSpace ℝ (Fin 1)`,
read through `Time.val` and the coordinate `x 0` of `Space 1`. -/
def scalarWaveField (φ : ℝ → ℝ → ℝ) : Time → Space 1 → EuclideanSpace ℝ (Fin 1) :=
  fun t x => WithLp.toLp 2 (fun _ => φ t.val (x 0))

private def evalZeroLinear : Space 1 →ₗ[ℝ] ℝ where
  toFun x' := x' 0
  map_add' x y := Space.add_apply x y 0
  map_smul' c x := by
    show (c • x) 0 = c • x 0
    rw [smul_eq_mul]
    exact Space.smul_apply c x 0

private noncomputable def evalZeroCLM : Space 1 →L[ℝ] ℝ :=
  LinearMap.mkContinuous evalZeroLinear 1 (fun x' => by
    show ‖x' 0‖ ≤ 1 * ‖x'‖
    rw [Real.norm_eq_abs, one_mul]
    exact Space.abs_eval_le_norm x' 0)

private theorem evalZeroCLM_basis_zero :
    evalZeroCLM (Space.basis (d := 1) 0) = 1 := by
  show ((Space.basis (d := 1)) 0) (0 : Fin 1) = 1
  have h1 := OrthonormalBasis.repr_self (Space.basis (d := 1)) (0 : Fin 1)
  have h2 : ((Space.basis (d := 1)).repr ((Space.basis (d := 1)) 0)).ofLp (0 : Fin 1) =
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)).ofLp (0 : Fin 1) :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v.ofLp (0 : Fin 1)) h1
  have hLHS : ((Space.basis (d := 1)).repr ((Space.basis (d := 1)) 0)).ofLp 0 =
      ((Space.basis (d := 1)) 0) 0 := rfl
  rw [hLHS] at h2
  have hRHS : (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)).ofLp 0 = 1 := by
    show (PiLp.single (β := fun _ : Fin 1 => ℝ) 2 (0 : Fin 1) (1 : ℝ)).ofLp 0 = 1
    rw [PiLp.single_apply]
    simp
  rw [hRHS] at h2
  exact h2

private theorem fderiv_space_slice (ψ : ℝ → ℝ) (ψ' : ℝ) (x' : Space 1)
    (hψ : HasDerivAt ψ ψ' (x' 0)) :
    fderiv ℝ (fun z : Space 1 => ψ (z 0)) x' (Space.basis (d := 1) 0) = ψ' := by
  have hπ : HasFDerivAt (fun z : Space 1 => z 0) evalZeroCLM x' :=
    evalZeroCLM.hasFDerivAt
  have hψF : HasFDerivAt ψ (ContinuousLinearMap.toSpanSingleton ℝ ψ') (x' 0) :=
    hψ.hasFDerivAt
  have hcomp := hψF.comp x' hπ
  have hfd := hcomp.fderiv
  show fderiv ℝ (ψ ∘ fun z : Space 1 => z 0) x' (Space.basis (d := 1) 0) = ψ'
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply, evalZeroCLM_basis_zero,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]

private def timeValLinear : Time →ₗ[ℝ] ℝ where
  toFun t := t.val
  map_add' t1 t2 := Time.add_val t1 t2
  map_smul' c t := by
    show (c • t).val = c • t.val
    rw [smul_eq_mul]
    exact Time.smul_real_val c t

private def timeValCLM : Time →L[ℝ] ℝ :=
  LinearMap.mkContinuous timeValLinear 1
    (fun t => le_of_eq ((Time.norm_eq_val t).symm.trans (one_mul _).symm))

private theorem timeValCLM_one : timeValCLM 1 = 1 := by
  show (1 : Time).val = 1
  exact Time.one_val

private def constVecLinear : ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) where
  toFun y := WithLp.toLp 2 (fun _ : Fin 1 => y)
  map_add' a b := by
    show WithLp.toLp 2 (fun _ : Fin 1 => a + b) =
      WithLp.toLp 2 (fun _ : Fin 1 => a) + WithLp.toLp 2 (fun _ : Fin 1 => b)
    rw [WithLp.ext_iff]
    funext i
    simp only [PiLp.add_apply]
  map_smul' c y := by
    show WithLp.toLp 2 (fun _ : Fin 1 => c • y) =
      c • WithLp.toLp 2 (fun _ : Fin 1 => y)
    rw [WithLp.ext_iff]
    funext i
    simp only [PiLp.smul_apply]

private noncomputable def constVecCLM : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  LinearMap.mkContinuous constVecLinear 1 (fun y => by
    show ‖WithLp.toLp 2 (fun _ : Fin 1 => y)‖ ≤ 1 * ‖y‖
    have hnorm : ‖WithLp.toLp 2 (fun _ : Fin 1 => y)‖ = ‖y‖ := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, WithLp.ofLp_toLp,
        Real.sqrt_sq (norm_nonneg y)]
    rw [hnorm]
    exact le_of_eq (one_mul _).symm)

private theorem constVecCLM_apply (y : ℝ) :
    constVecCLM y = WithLp.toLp 2 (fun _ : Fin 1 => y) := rfl

private theorem fderiv_time_transport (ψ : ℝ → ℝ) (ψ' : ℝ) (t' : Time)
    (hψ : HasDerivAt ψ ψ' t'.val) :
    fderiv ℝ (fun s : Time => WithLp.toLp 2 (fun _ : Fin 1 => ψ s.val)) t' 1 =
      WithLp.toLp 2 (fun _ : Fin 1 => ψ') := by
  have hV : HasFDerivAt (fun s : Time => s.val) timeValCLM t' :=
    timeValCLM.hasFDerivAt
  have hψF : HasFDerivAt ψ (ContinuousLinearMap.toSpanSingleton ℝ ψ') t'.val :=
    hψ.hasFDerivAt
  have hE : HasFDerivAt (fun y : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => y)) constVecCLM (ψ t'.val) :=
    constVecCLM.hasFDerivAt
  have h1 := hψF.comp t' hV
  have h2 := hE.comp t' h1
  have hfd := h2.fderiv
  show fderiv ℝ ((fun y : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => y)) ∘
      (ψ ∘ fun s : Time => s.val)) t' 1 =
    WithLp.toLp 2 (fun _ : Fin 1 => ψ')
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply, timeValCLM_one,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, constVecCLM_apply]

private theorem smul_toLp_const (c v : ℝ) :
    c • WithLp.toLp 2 (fun _ : Fin 1 => v) =
      WithLp.toLp 2 (fun _ : Fin 1 => c * v) := by
  rw [WithLp.ext_iff]
  funext i
  simp only [PiLp.smul_apply, smul_eq_mul]

/-- On `Space 1`, the vector Laplacian of a transported field is the second `x`-derivative:
if the slice `φ t.val` has derivative `φx t.val y` at every `y`, and `φx t.val` has derivative
`φxx t.val (x 0)` at `x 0`, then `Δᵥ (scalarWaveField φ t) x` has component `φxx t.val (x 0)`. -/
lemma laplacianVec_scalarWaveField {φ φx φxx : ℝ → ℝ → ℝ} (t : Time) (x : Space 1)
    (hφx : ∀ y, HasDerivAt (fun y' => φ t.val y') (φx t.val y) y)
    (hφxx : HasDerivAt (fun y => φx t.val y) (φxx t.val (x 0)) (x 0)) :
    Δᵥ (scalarWaveField φ t) x = WithLp.toLp 2 (fun _ => φxx t.val (x 0)) := by
  have h1 : (fun x' : Space 1 => ∂[0] (fun z : Space 1 => φ t.val (z 0)) x') =
      (fun x' => φx t.val (x' 0)) := by
    funext x'
    exact fderiv_space_slice (fun y => φ t.val y) (φx t.val (x' 0)) x' (hφx (x' 0))
  have h2 : Δ (fun x' : Space 1 => φ t.val (x' 0)) x =
      ∂[0] (fun x' => φx t.val (x' 0)) x := by
    show (∑ i : Fin 1, ∂[i] (fun x' => ((Space.grad (fun z : Space 1 => φ t.val (z 0)) x') i)) x) =
      ∂[0] (fun x' => φx t.val (x' 0)) x
    rw [Fin.sum_univ_one]
    show ∂[0] (fun x' => ∂[0] (fun z : Space 1 => φ t.val (z 0)) x') x =
      ∂[0] (fun x' => φx t.val (x' 0)) x
    rw [h1]
  have hmain : Δ (fun x' : Space 1 => φ t.val (x' 0)) x = φxx t.val (x 0) := by
    rw [h2]
    exact fderiv_space_slice (fun y => φx t.val y) (φxx t.val (x 0)) x hφxx
  show WithLp.toLp 2 (fun i => Δ (fun x' => (scalarWaveField φ t x') i) x) =
    WithLp.toLp 2 (fun _ => φxx t.val (x 0))
  congr 1
  funext i
  exact hmain

/-- The iterated Physlib time derivative of a transported field is the second `t`-derivative:
if the slice `fun s => φ s (x 0)` has derivative `φt s (x 0)` at every `s`, and
`fun s => φt s (x 0)` has derivative `φtt t.val (x 0)` at `t.val`, then the second time
derivative in `ClassicalMechanics.WaveEquation` has component `φtt t.val (x 0)`. -/
lemma deriv_deriv_scalarWaveField {φ φt φtt : ℝ → ℝ → ℝ} (t : Time) (x : Space 1)
    (hφt : ∀ s, HasDerivAt (fun s' => φ s' (x 0)) (φt s (x 0)) s)
    (hφtt : HasDerivAt (fun s => φt s (x 0)) (φtt t.val (x 0)) t.val) :
    ∂ₜ (fun t => (∂ₜ (fun t => scalarWaveField φ t x) t)) t =
      WithLp.toLp 2 (fun _ => φtt t.val (x 0)) := by
  have h1 : (fun t : Time => ∂ₜ (fun t => scalarWaveField φ t x) t) =
      (fun t => WithLp.toLp 2 (fun _ : Fin 1 => φt t.val (x 0))) := by
    funext t
    exact fderiv_time_transport (fun s => φ s (x 0)) (φt t.val (x 0)) t (hφt t.val)
  have h2 : ∂ₜ (fun t : Time => ∂ₜ (fun t => scalarWaveField φ t x) t) t =
      ∂ₜ (fun t : Time => WithLp.toLp 2 (fun _ : Fin 1 => φt t.val (x 0))) t := by
    rw [h1]
  rw [h2]
  exact fderiv_time_transport (fun s => φt s (x 0)) (φtt t.val (x 0)) t hφtt

/-! ## B. Mixed-partial criteria and eliminations -/

set_option linter.unusedVariables false in
/-- Mixed-partial criterion for the head. For the water-hammer pair with first partials
`ht hx qt qx`, second derivatives `hxx = ∂ₓ hx`, `qxt = ∂ₜ qx` and `qtx = ∂ₓ qt`, the head
satisfies `h_tt = a² h_xx` at `(t, x)` exactly when `qxt t x = qtx t x`. The four basic
slice-derivative premises are interface premises and are idle in this pointwise criterion. -/
lemma head_wave_iff_mixed {a g A : ℝ} (ha : 0 < a) (hg : 0 < g) (hA : 0 < A)
    {h q ht hx qt qx hxx qxt qtx : ℝ → ℝ → ℝ}
    (hht : ∀ t x, HasDerivAt (fun s => h s x) (ht t x) t)
    (hqt : ∀ t x, HasDerivAt (fun s => q s x) (qt t x) t)
    (hhx : ∀ t x, HasDerivAt (fun y => h t y) (hx t x) x)
    (hqx : ∀ t x, HasDerivAt (fun y => q t y) (qx t x) x)
    (hpde1 : ∀ t x, ht t x + (a ^ 2 / (g * A)) * qx t x = 0)
    (hpde2 : ∀ t x, qt t x + (g * A) * hx t x = 0)
    (hhxx : ∀ t x, HasDerivAt (fun y => hx t y) (hxx t x) x)
    (hqxt : ∀ t x, HasDerivAt (fun s => qx s x) (qxt t x) t)
    (hqtx : ∀ t x, HasDerivAt (fun y => qt t y) (qtx t x) x) (t x : ℝ) :
    HasDerivAt (fun s => ht s x) (a ^ 2 * hxx t x) t ↔ qxt t x = qtx t x := by
  have hd : (g * A) ≠ 0 := mul_ne_zero (ne_of_gt hg) (ne_of_gt hA)
  have hcd : (a ^ 2 / (g * A)) * (g * A) = a ^ 2 := div_mul_cancel₀ (a ^ 2) hd
  have ha2 : (a ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt ha)
  have hc : (a ^ 2 / (g * A)) ≠ 0 := div_ne_zero ha2 hd
  have hD : HasDerivAt (fun y => (g * A) * hx t y) ((g * A) * hxx t x) x :=
    (hhxx t x).const_mul (g * A)
  have hsum2 := (hqtx t x).add hD
  have hzero2 : HasDerivAt ((fun y => qt t y) + (fun y => (g * A) * hx t y)) 0 x := by
    have hfun2 : ((fun y => qt t y) + (fun y => (g * A) * hx t y)) = fun _ => 0 := by
      funext y
      show qt t y + (g * A) * hx t y = 0
      exact hpde2 t y
    rw [hfun2]
    exact hasDerivAt_const x 0
  have heq2 := hsum2.unique hzero2
  have e2 : (a ^ 2 / (g * A)) * qtx t x = -(a ^ 2 * hxx t x) := by
    have hqx : qtx t x = -((g * A) * hxx t x) := eq_neg_of_add_eq_zero_left heq2
    rw [hqx, mul_neg, ← mul_assoc, hcd]
  constructor
  · intro H
    have hC : HasDerivAt (fun s => (a ^ 2 / (g * A)) * qx s x)
        ((a ^ 2 / (g * A)) * qxt t x) t :=
      (hqxt t x).const_mul (a ^ 2 / (g * A))
    have hsum := H.add hC
    have hzero : HasDerivAt ((fun s => ht s x) + (fun s => (a ^ 2 / (g * A)) * qx s x)) 0 t := by
      have hfun1 : ((fun s => ht s x) + (fun s => (a ^ 2 / (g * A)) * qx s x)) = fun _ => 0 := by
        funext s
        show ht s x + (a ^ 2 / (g * A)) * qx s x = 0
        exact hpde1 s x
      rw [hfun1]
      exact hasDerivAt_const t 0
    have heq := hsum.unique hzero
    have e1 : (a ^ 2 / (g * A)) * qxt t x = -(a ^ 2 * hxx t x) :=
      eq_neg_of_add_eq_zero_right heq
    have key : (a ^ 2 / (g * A)) * qxt t x = (a ^ 2 / (g * A)) * qtx t x := by
      rw [e1, e2]
    exact mul_left_cancel₀ hc key
  · intro hmix1
    have hval : -((a ^ 2 / (g * A)) * qxt t x) = a ^ 2 * hxx t x := by
      rw [hmix1, e2, neg_neg]
    have hfun : (fun s => ht s x) = (fun s => -((a ^ 2 / (g * A)) * qx s x)) := by
      funext s
      show ht s x = -((a ^ 2 / (g * A)) * qx s x)
      exact eq_neg_of_add_eq_zero_left (hpde1 s x)
    rw [hfun, ← hval]
    have hC : HasDerivAt (fun s => (a ^ 2 / (g * A)) * qx s x)
        ((a ^ 2 / (g * A)) * qxt t x) t :=
      (hqxt t x).const_mul (a ^ 2 / (g * A))
    have hneg := hC.neg
    exact hneg.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => rfl)

set_option linter.unusedVariables false in
/-- Mixed-partial criterion for the discharge. With `hxt = ∂ₜ hx`, `htx = ∂ₓ ht` and
`qxx = ∂ₓ qx`, the discharge satisfies `q_tt = a² q_xx` at `(t, x)` exactly when
`hxt t x = htx t x`. The four basic slice-derivative premises are interface premises and
are idle in this pointwise criterion. -/
lemma discharge_wave_iff_mixed {a g A : ℝ} (ha : 0 < a) (hg : 0 < g) (hA : 0 < A)
    {h q ht hx qt qx qxx hxt htx : ℝ → ℝ → ℝ}
    (hht : ∀ t x, HasDerivAt (fun s => h s x) (ht t x) t)
    (hqt : ∀ t x, HasDerivAt (fun s => q s x) (qt t x) t)
    (hhx : ∀ t x, HasDerivAt (fun y => h t y) (hx t x) x)
    (hqx : ∀ t x, HasDerivAt (fun y => q t y) (qx t x) x)
    (hpde1 : ∀ t x, ht t x + (a ^ 2 / (g * A)) * qx t x = 0)
    (hpde2 : ∀ t x, qt t x + (g * A) * hx t x = 0)
    (hqxx : ∀ t x, HasDerivAt (fun y => qx t y) (qxx t x) x)
    (hhxt : ∀ t x, HasDerivAt (fun s => hx s x) (hxt t x) t)
    (hhtx : ∀ t x, HasDerivAt (fun y => ht t y) (htx t x) x) (t x : ℝ) :
    HasDerivAt (fun s => qt s x) (a ^ 2 * qxx t x) t ↔ hxt t x = htx t x := by
  have hd : (g * A) ≠ 0 := mul_ne_zero (ne_of_gt hg) (ne_of_gt hA)
  have hcd : (a ^ 2 / (g * A)) * (g * A) = a ^ 2 := div_mul_cancel₀ (a ^ 2) hd
  have ha2 : (a ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt ha)
  have hdc : (g * A) * (a ^ 2 / (g * A)) = a ^ 2 := by
    rw [mul_comm]
    exact hcd
  have hD : HasDerivAt (fun y => (a ^ 2 / (g * A)) * qx t y)
      ((a ^ 2 / (g * A)) * qxx t x) x :=
    (hqxx t x).const_mul (a ^ 2 / (g * A))
  have hsum2 := (hhtx t x).add hD
  have hzero2 : HasDerivAt ((fun y => ht t y) + (fun y => (a ^ 2 / (g * A)) * qx t y)) 0 x := by
    have hfun2 : ((fun y => ht t y) + (fun y => (a ^ 2 / (g * A)) * qx t y)) = fun _ => 0 := by
      funext y
      show ht t y + (a ^ 2 / (g * A)) * qx t y = 0
      exact hpde1 t y
    rw [hfun2]
    exact hasDerivAt_const x 0
  have heq2 := hsum2.unique hzero2
  have e2 : (g * A) * htx t x = -(a ^ 2 * qxx t x) := by
    have htxeq : htx t x = -((a ^ 2 / (g * A)) * qxx t x) :=
      eq_neg_of_add_eq_zero_left heq2
    rw [htxeq, mul_neg, ← mul_assoc, hdc]
  constructor
  · intro H
    have hC : HasDerivAt (fun s => (g * A) * hx s x) ((g * A) * hxt t x) t :=
      (hhxt t x).const_mul (g * A)
    have hsum := H.add hC
    have hzero : HasDerivAt ((fun s => qt s x) + (fun s => (g * A) * hx s x)) 0 t := by
      have hfun1 : ((fun s => qt s x) + (fun s => (g * A) * hx s x)) = fun _ => 0 := by
        funext s
        show qt s x + (g * A) * hx s x = 0
        exact hpde2 s x
      rw [hfun1]
      exact hasDerivAt_const t 0
    have heq := hsum.unique hzero
    have e1 : (g * A) * hxt t x = -(a ^ 2 * qxx t x) :=
      eq_neg_of_add_eq_zero_right heq
    have key : (g * A) * hxt t x = (g * A) * htx t x := by
      rw [e1, e2]
    have key2 : a ^ 2 * hxt t x = a ^ 2 * htx t x := by
      calc a ^ 2 * hxt t x
          = (a ^ 2 / (g * A)) * ((g * A) * hxt t x) := by rw [← mul_assoc, hcd]
        _ = (a ^ 2 / (g * A)) * ((g * A) * htx t x) := by rw [key]
        _ = a ^ 2 * htx t x := by rw [← mul_assoc, hcd]
    exact mul_left_cancel₀ ha2 key2
  · intro hmix1
    have hval : -((g * A) * hxt t x) = a ^ 2 * qxx t x := by
      rw [hmix1, e2, neg_neg]
    have hfun : (fun s => qt s x) = (fun s => -((g * A) * hx s x)) := by
      funext s
      show qt s x = -((g * A) * hx s x)
      exact eq_neg_of_add_eq_zero_left (hpde2 s x)
    rw [hfun, ← hval]
    have hC : HasDerivAt (fun s => (g * A) * hx s x) ((g * A) * hxt t x) t :=
      (hhxt t x).const_mul (g * A)
    have hneg := hC.neg
    exact hneg.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => rfl)

/-- Head wave equation: eliminating `q` from the water-hammer pair, under the second
derivatives `hxx = ∂ₓ hx`, `qxt = ∂ₜ qx`, `qtx = ∂ₓ qt` and the mixed-partial equality
`qxt = qtx`, gives `h_tt = a² h_xx` (as a derivative of the time-derivative field `ht`). -/
theorem head_wave {a g A : ℝ} (ha : 0 < a) (hg : 0 < g) (hA : 0 < A)
    {h q ht hx qt qx hxx qxt qtx : ℝ → ℝ → ℝ}
    (hht : ∀ t x, HasDerivAt (fun s => h s x) (ht t x) t)
    (hqt : ∀ t x, HasDerivAt (fun s => q s x) (qt t x) t)
    (hhx : ∀ t x, HasDerivAt (fun y => h t y) (hx t x) x)
    (hqx : ∀ t x, HasDerivAt (fun y => q t y) (qx t x) x)
    (hpde1 : ∀ t x, ht t x + (a ^ 2 / (g * A)) * qx t x = 0)
    (hpde2 : ∀ t x, qt t x + (g * A) * hx t x = 0)
    (hhxx : ∀ t x, HasDerivAt (fun y => hx t y) (hxx t x) x)
    (hqxt : ∀ t x, HasDerivAt (fun s => qx s x) (qxt t x) t)
    (hqtx : ∀ t x, HasDerivAt (fun y => qt t y) (qtx t x) x)
    (hmix : ∀ t x, qxt t x = qtx t x) (t x : ℝ) :
    HasDerivAt (fun s => ht s x) (a ^ 2 * hxx t x) t := by
  exact (head_wave_iff_mixed ha hg hA hht hqt hhx hqx hpde1 hpde2 hhxx hqxt hqtx t x).mpr
    (hmix t x)

/-- Discharge wave equation: eliminating `h`, under `qxx = ∂ₓ qx`, `hxt = ∂ₜ hx`,
`htx = ∂ₓ ht` and the mixed-partial equality `hxt = htx`, gives `q_tt = a² q_xx`. -/
theorem discharge_wave {a g A : ℝ} (ha : 0 < a) (hg : 0 < g) (hA : 0 < A)
    {h q ht hx qt qx qxx hxt htx : ℝ → ℝ → ℝ}
    (hht : ∀ t x, HasDerivAt (fun s => h s x) (ht t x) t)
    (hqt : ∀ t x, HasDerivAt (fun s => q s x) (qt t x) t)
    (hhx : ∀ t x, HasDerivAt (fun y => h t y) (hx t x) x)
    (hqx : ∀ t x, HasDerivAt (fun y => q t y) (qx t x) x)
    (hpde1 : ∀ t x, ht t x + (a ^ 2 / (g * A)) * qx t x = 0)
    (hpde2 : ∀ t x, qt t x + (g * A) * hx t x = 0)
    (hqxx : ∀ t x, HasDerivAt (fun y => qx t y) (qxx t x) x)
    (hhxt : ∀ t x, HasDerivAt (fun s => hx s x) (hxt t x) t)
    (hhtx : ∀ t x, HasDerivAt (fun y => ht t y) (htx t x) x)
    (hmix : ∀ t x, hxt t x = htx t x) (t x : ℝ) :
    HasDerivAt (fun s => qt s x) (a ^ 2 * qxx t x) t := by
  exact (discharge_wave_iff_mixed ha hg hA hht hqt hhx hqx hpde1 hpde2 hqxx hhxt hhtx t x).mpr
    (hmix t x)

/-! ## C. Physlib wave-equation maps -/

/-- Under the hypotheses of `head_wave`, the transported head satisfies Physlib's
`ClassicalMechanics.WaveEquation` at `d = 1` with speed `a`, at every instant and point. -/
theorem waveEquation_head {a g A : ℝ} (ha : 0 < a) (hg : 0 < g) (hA : 0 < A)
    {h q ht hx qt qx hxx qxt qtx : ℝ → ℝ → ℝ}
    (hht : ∀ t x, HasDerivAt (fun s => h s x) (ht t x) t)
    (hqt : ∀ t x, HasDerivAt (fun s => q s x) (qt t x) t)
    (hhx : ∀ t x, HasDerivAt (fun y => h t y) (hx t x) x)
    (hqx : ∀ t x, HasDerivAt (fun y => q t y) (qx t x) x)
    (hpde1 : ∀ t x, ht t x + (a ^ 2 / (g * A)) * qx t x = 0)
    (hpde2 : ∀ t x, qt t x + (g * A) * hx t x = 0)
    (hhxx : ∀ t x, HasDerivAt (fun y => hx t y) (hxx t x) x)
    (hqxt : ∀ t x, HasDerivAt (fun s => qx s x) (qxt t x) t)
    (hqtx : ∀ t x, HasDerivAt (fun y => qt t y) (qtx t x) x)
    (hmix : ∀ t x, qxt t x = qtx t x) :
    ∀ (t : Time) (x : Space 1), ClassicalMechanics.WaveEquation (scalarWaveField h) t x a := by
  intro t x
  have hL : Δᵥ (scalarWaveField h t) x = WithLp.toLp 2 (fun _ => hxx t.val (x 0)) :=
    laplacianVec_scalarWaveField (φ := h) (φx := hx) (φxx := hxx) t x
      (fun y => hhx t.val y) (hhxx t.val (x 0))
  have htt : HasDerivAt (fun s => ht s (x 0)) (a ^ 2 * hxx t.val (x 0)) t.val :=
    head_wave ha hg hA hht hqt hhx hqx hpde1 hpde2 hhxx hqxt hqtx hmix t.val (x 0)
  have hT : ∂ₜ (fun t => (∂ₜ (fun t => scalarWaveField h t x) t)) t =
      WithLp.toLp 2 (fun _ => a ^ 2 * hxx t.val (x 0)) :=
    deriv_deriv_scalarWaveField (φ := h) (φt := ht) (φtt := fun t x => a ^ 2 * hxx t x) t x
      (fun s => hht s (x 0)) htt
  show a ^ 2 • Δᵥ (scalarWaveField h t) x -
      ∂ₜ (fun t => (∂ₜ (fun t => scalarWaveField h t x) t)) t = 0
  rw [hL, hT, smul_toLp_const, sub_self]

/-- Under the hypotheses of `discharge_wave`, the transported discharge satisfies Physlib's
`ClassicalMechanics.WaveEquation` at `d = 1` with speed `a`, at every instant and point. -/
theorem waveEquation_discharge {a g A : ℝ} (ha : 0 < a) (hg : 0 < g) (hA : 0 < A)
    {h q ht hx qt qx qxx hxt htx : ℝ → ℝ → ℝ}
    (hht : ∀ t x, HasDerivAt (fun s => h s x) (ht t x) t)
    (hqt : ∀ t x, HasDerivAt (fun s => q s x) (qt t x) t)
    (hhx : ∀ t x, HasDerivAt (fun y => h t y) (hx t x) x)
    (hqx : ∀ t x, HasDerivAt (fun y => q t y) (qx t x) x)
    (hpde1 : ∀ t x, ht t x + (a ^ 2 / (g * A)) * qx t x = 0)
    (hpde2 : ∀ t x, qt t x + (g * A) * hx t x = 0)
    (hqxx : ∀ t x, HasDerivAt (fun y => qx t y) (qxx t x) x)
    (hhxt : ∀ t x, HasDerivAt (fun s => hx s x) (hxt t x) t)
    (hhtx : ∀ t x, HasDerivAt (fun y => ht t y) (htx t x) x)
    (hmix : ∀ t x, hxt t x = htx t x) :
    ∀ (t : Time) (x : Space 1), ClassicalMechanics.WaveEquation (scalarWaveField q) t x a := by
  intro t x
  have hL : Δᵥ (scalarWaveField q t) x = WithLp.toLp 2 (fun _ => qxx t.val (x 0)) :=
    laplacianVec_scalarWaveField (φ := q) (φx := qx) (φxx := qxx) t x
      (fun y => hqx t.val y) (hqxx t.val (x 0))
  have htt : HasDerivAt (fun s => qt s (x 0)) (a ^ 2 * qxx t.val (x 0)) t.val :=
    discharge_wave ha hg hA hht hqt hhx hqx hpde1 hpde2 hqxx hhxt hhtx hmix t.val (x 0)
  have hT : ∂ₜ (fun t => (∂ₜ (fun t => scalarWaveField q t x) t)) t =
      WithLp.toLp 2 (fun _ => a ^ 2 * qxx t.val (x 0)) :=
    deriv_deriv_scalarWaveField (φ := q) (φt := qt) (φtt := fun t x => a ^ 2 * qxx t x) t x
      (fun s => hqt s (x 0)) htt
  show a ^ 2 • Δᵥ (scalarWaveField q t) x -
      ∂ₜ (fun t => (∂ₜ (fun t => scalarWaveField q t x) t)) t = 0
  rw [hL, hT, smul_toLp_const, sub_self]

end FluidDynamics.WaterHammer
