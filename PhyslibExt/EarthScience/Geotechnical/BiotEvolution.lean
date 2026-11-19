/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.LinearAlgebra.Matrix.BiotSchur
public import MathlibExt.Analysis.ODE.Duhamel
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Nonsingular finite Biot evolution

## i. Overview

The finite Biot rate system with constant load rate `df` and
constant source `s`: differentiable displacement and pressure
paths `u, p` satisfying at every time the equilibrium rate
equation `K *ᵥ u' + Q *ᵥ p' = df` and the storage balance
`-Qᵀ *ᵥ u' + C *ᵥ p' = s - H *ᵥ p` (the dissipative sign
convention of `PhyslibExt.Mechanics.PoroelasticEnergy`: with
`Q = 0`, `C = H = I`, `s = 0` the pressure decays, `p' = -p`). With reduced storage
`S = Qᵀ K⁻¹ Q + C`, the pressure rate solves the reduced
storage equation (the canonical algebraic Biot rate identity),
and when `S` is positive definite the coupled system has a
unique solution for given initial data, transported from the
canonical finite linear-ODE (Duhamel) existence and uniqueness
theorem. When no dynamics remain (`Q = 0`, `C = 0`, `df = 0`),
a solution forces the source into the range of `H`. No new
linear-ODE or DAE theory and no continuum Biot PDE is
included; arbitrary singular DAEs are outside this module.

## ii. Key results

- `EarthScience.biotStorage`: the reduced storage matrix
  `Qᵀ K⁻¹ Q + C`.
- `EarthScience.biotStorage_posDef`: positive-definite storage
  from positive-definite compliance and positive-semidefinite
  stiffness inverse.
- `EarthScience.SatisfiesBiotRateSystem`: the coupled rate
  equations as a predicate on paths.
- `EarthScience.biot_pressure_rate_eq`: the reduced pressure
  rate equation and displacement-rate recovery.
- `EarthScience.biot_existsUnique`: existence and uniqueness
  for nonsingular (positive-definite) storage.
- `EarthScience.biot_source_mem_range_of_no_dynamics`: the
  singular-range rejection.

## iii. Table of contents

- A. Storage matrix and the rate-system predicate
- B. Transported rate and evolution results
- C. Public evolution results

## iv. References

- `MathlibExt.LinearAlgebra.Matrix.BiotSchur` for the algebraic
  Biot Schur reduction and rate identity.
- `MathlibExt.Analysis.ODE.Duhamel` for the finite linear-ODE
  variation-of-constants existence and uniqueness theorem.
- M. A. Biot, "General theory of three-dimensional
  consolidation", *Journal of Applied Physics* 12 (1941),
  155-164: the coupled equilibrium/storage consolidation
  equations discretized here.
-/

@[expose] public section

open Matrix

namespace EarthScience

/-! ## A. Storage matrix and the rate-system predicate -/

/-- Reduced Biot storage matrix `Qᵀ K⁻¹ Q + C` for stiffness
inverse `Kinv`, coupling `Q`, and storage compliance `C`. -/
def biotStorage {n m : Type*} [Fintype n] [Fintype m]
    (Kinv : Matrix n n ℝ) (Q : Matrix n m ℝ) (C : Matrix m m ℝ) :
    Matrix m m ℝ :=
  Qᵀ * Kinv * Q + C

/-- Auxiliary transported form of the rate system (opposite
storage sign); the public predicate `SatisfiesBiotRateSystem`
below is equivalent to this one at `(-Q, -H)` on the negated
pressure path. -/
private def SatisfiesBiotRateSystemAux {n m : Type*} [Fintype n] [Fintype m]
    (K : Matrix n n ℝ) (Q : Matrix n m ℝ) (C H : Matrix m m ℝ)
    (df : n → ℝ) (s : m → ℝ)
    (u : ℝ → n → ℝ) (p : ℝ → m → ℝ) : Prop :=
  Differentiable ℝ u ∧ Differentiable ℝ p ∧ ∀ t : ℝ,
    (K *ᵥ deriv u t + Q *ᵥ deriv p t = df)
      ∧ (Qᵀ *ᵥ deriv u t - C *ᵥ deriv p t = s - H *ᵥ p t)

private theorem hasDerivAt_mulVec_left {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (M : Matrix n m ℝ) (f : ℝ → m → ℝ) (f' : m → ℝ) (t : ℝ)
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun t => M *ᵥ f t) (M *ᵥ f') t := by
  have h :=
    ((Matrix.mulVecLin M).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hf
  simpa [Matrix.mulVecLin_apply, Function.comp_def] using h

/-! ## B. Transported rate and evolution results -/

/-- If the storage compliance is positive definite and the
stiffness inverse is positive semidefinite, the reduced Biot
storage matrix is positive definite. -/
theorem biotStorage_posDef {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    {Kinv : Matrix n n ℝ} {Q : Matrix n m ℝ} {C : Matrix m m ℝ}
    (hKinv : Kinv.PosSemidef) (hC : C.PosDef) :
    (biotStorage Kinv Q C).PosDef := by
  unfold biotStorage
  have hQ : (Qᵀ * Kinv * Q).PosSemidef := by
    have h := hKinv.conjTranspose_mul_mul_same Q
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial Q] at h
  have h := hC.add_posSemidef hQ
  rwa [add_comm] at h

/-- The pressure rate of a Biot solution solves the reduced
storage equation, and the displacement rate is recovered from
the equilibrium rate equation, transported from the canonical
algebraic Biot rate identity supplied as `hrate`. -/
private theorem biot_pressure_rate_eq_of {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (hrate : ∀ (K Kinv : Matrix n n ℝ),
      K * Kinv = 1 → Kinv * K = 1 →
      ∀ (Q : Matrix n m ℝ) (C H : Matrix m m ℝ)
        (du : n → ℝ) (dp : m → ℝ) (df : n → ℝ) (s : m → ℝ)
        (p : m → ℝ),
        K *ᵥ du + Q *ᵥ dp = df →
        Qᵀ *ᵥ du - C *ᵥ dp = s - H *ᵥ p →
        du = Kinv *ᵥ (df - Q *ᵥ dp)
          ∧ (Qᵀ * Kinv * Q + C) *ᵥ dp
            = Qᵀ *ᵥ (Kinv *ᵥ df) - s + H *ᵥ p)
    {K Kinv : Matrix n n ℝ} (hK : K * Kinv = 1) (hK' : Kinv * K = 1)
    {Q : Matrix n m ℝ} {C H : Matrix m m ℝ}
    {df : n → ℝ} {s : m → ℝ} {u : ℝ → n → ℝ} {p : ℝ → m → ℝ}
    (hsat : SatisfiesBiotRateSystemAux K Q C H df s u p) (t : ℝ) :
    biotStorage Kinv Q C *ᵥ deriv p t
        = Qᵀ *ᵥ (Kinv *ᵥ df) - s + H *ᵥ p t
      ∧ deriv u t = Kinv *ᵥ (df - Q *ᵥ deriv p t) := by
  obtain ⟨-, -, heq⟩ := hsat
  obtain ⟨heq1, heq2⟩ := heq t
  obtain ⟨hdu, hdp⟩ := hrate K Kinv hK hK' Q C H _ _ df s (p t) heq1 heq2
  constructor
  · simpa [biotStorage] using hdp
  · exact hdu

/-- Existence and uniqueness for the nonsingular finite Biot
rate system with constant forcing, transported from the
algebraic Biot rate identity (`hrate`) and a finite linear-ODE
existence/uniqueness provider (`hODE`) for the reduced pressure
equation. The displacement is recovered by integrating its
rate formula; no new linear-ODE or DAE theory is proved. At
integration `Sinv` is obtained from positive-definite reduced
storage (`biotStorage_posDef`). -/
private theorem biot_existsUnique_of {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (hrate : ∀ (K Kinv : Matrix n n ℝ),
      K * Kinv = 1 → Kinv * K = 1 →
      ∀ (Q : Matrix n m ℝ) (C H : Matrix m m ℝ)
        (du : n → ℝ) (dp : m → ℝ) (df : n → ℝ) (s : m → ℝ)
        (p : m → ℝ),
        K *ᵥ du + Q *ᵥ dp = df →
        Qᵀ *ᵥ du - C *ᵥ dp = s - H *ᵥ p →
        du = Kinv *ᵥ (df - Q *ᵥ dp)
          ∧ (Qᵀ * Kinv * Q + C) *ᵥ dp
            = Qᵀ *ᵥ (Kinv *ᵥ df) - s + H *ᵥ p)
    (hODE : ∀ (A : Matrix m m ℝ) (b : m → ℝ) (p0 : m → ℝ),
      ∃ p : ℝ → m → ℝ, p 0 = p0 ∧ Differentiable ℝ p
        ∧ (∀ t, deriv p t = A *ᵥ p t + b)
        ∧ ∀ p' : ℝ → m → ℝ, p' 0 = p0 → Differentiable ℝ p'
          → (∀ t, deriv p' t = A *ᵥ p' t + b) → p' = p)
    {K Kinv : Matrix n n ℝ} {Q : Matrix n m ℝ}
    {C H Sinv : Matrix m m ℝ}
    (hK : K * Kinv = 1) (hK' : Kinv * K = 1)
    (hS : biotStorage Kinv Q C * Sinv = 1)
    (hS' : Sinv * biotStorage Kinv Q C = 1)
    {df : n → ℝ} {s : m → ℝ} (u0 : n → ℝ) (p0 : m → ℝ) :
    ∃ u : ℝ → n → ℝ, ∃ p : ℝ → m → ℝ,
      SatisfiesBiotRateSystemAux K Q C H df s u p
        ∧ u 0 = u0 ∧ p 0 = p0
        ∧ ∀ u' : ℝ → n → ℝ, ∀ p' : ℝ → m → ℝ,
            SatisfiesBiotRateSystemAux K Q C H df s u' p'
            → u' 0 = u0 → p' 0 = p0 → u' = u ∧ p' = p := by
  obtain ⟨p, hp0, hp_diff, hp_eq, hp_unique⟩ :=
    hODE (Sinv * H) (Sinv *ᵥ (Qᵀ *ᵥ (Kinv *ᵥ df) - s)) p0
  have hu_has : ∀ t, HasDerivAt
      (fun t => u0 + Kinv *ᵥ (t • df - Q *ᵥ (p t - p0)))
      (Kinv *ᵥ (df - Q *ᵥ deriv p t)) t := fun t => by
    have h1 : HasDerivAt (fun y : ℝ => y • df) df t := by
      simpa using (hasDerivAt_id t).smul_const df
    have h2 : HasDerivAt (fun t => p t - p0) (deriv p t) t :=
      ((hp_diff t).hasDerivAt).sub_const p0
    have h3 : HasDerivAt (fun t => Q *ᵥ (p t - p0)) (Q *ᵥ deriv p t) t :=
      hasDerivAt_mulVec_left Q _ _ t h2
    have h4 : HasDerivAt (fun t => t • df - Q *ᵥ (p t - p0))
        (df - Q *ᵥ deriv p t) t :=
      h1.sub h3
    have h5 : HasDerivAt (fun t => Kinv *ᵥ (t • df - Q *ᵥ (p t - p0)))
        (Kinv *ᵥ (df - Q *ᵥ deriv p t)) t :=
      hasDerivAt_mulVec_left Kinv _ _ t h4
    exact h5.const_add u0
  have hu_diff : Differentiable ℝ
      (fun t => u0 + Kinv *ᵥ (t • df - Q *ᵥ (p t - p0))) :=
    fun t => (hu_has t).differentiableAt
  have hu_deriv : ∀ t, deriv
      (fun t => u0 + Kinv *ᵥ (t • df - Q *ᵥ (p t - p0))) t
      = Kinv *ᵥ (df - Q *ᵥ deriv p t) :=
    fun t => (hu_has t).deriv
  have hred : ∀ t, biotStorage Kinv Q C *ᵥ deriv p t
      = Qᵀ *ᵥ (Kinv *ᵥ df) - s + H *ᵥ p t := fun t => by
    have hSH : biotStorage Kinv Q C * (Sinv * H) = H := by
      rw [← Matrix.mul_assoc, hS, Matrix.one_mul]
    have hSv : ∀ v : m → ℝ,
        biotStorage Kinv Q C *ᵥ (Sinv *ᵥ v) = v := fun v => by
      rw [Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]
    have hSA : ∀ x : m → ℝ,
        biotStorage Kinv Q C *ᵥ ((Sinv * H) *ᵥ x) = H *ᵥ x := fun x => by
      rw [Matrix.mulVec_mulVec, hSH]
    rw [hp_eq t, Matrix.mulVec_add, hSA, hSv]
    exact add_comm _ _
  have hu0 : (fun t => u0 + Kinv *ᵥ (t • df - Q *ᵥ (p t - p0))) 0 = u0 := by
    change u0 + Kinv *ᵥ ((0 : ℝ) • df - Q *ᵥ (p 0 - p0)) = u0
    simp [hp0]
  refine ⟨fun t => u0 + Kinv *ᵥ (t • df - Q *ᵥ (p t - p0)), p,
    ⟨hu_diff, hp_diff, fun t => ⟨?_, ?_⟩⟩, hu0, hp0, ?_⟩
  · rw [hu_deriv t]
    have h : K *ᵥ (Kinv *ᵥ (df - Q *ᵥ deriv p t))
        = df - Q *ᵥ deriv p t := by
      rw [Matrix.mulVec_mulVec, hK, Matrix.one_mulVec]
    rw [h, sub_add_cancel]
  · rw [hu_deriv t]
    have hQK : ∀ X : n → ℝ, Qᵀ *ᵥ (Kinv *ᵥ X) = (Qᵀ * Kinv) *ᵥ X :=
      fun X => Matrix.mulVec_mulVec _ _ _
    have hQQ : (Qᵀ * Kinv) *ᵥ (Q *ᵥ deriv p t)
        = ((Qᵀ * Kinv) * Q) *ᵥ deriv p t :=
      Matrix.mulVec_mulVec _ _ _
    have hsplit : (Qᵀ * Kinv) *ᵥ (df - Q *ᵥ deriv p t)
        = (Qᵀ * Kinv) *ᵥ df - ((Qᵀ * Kinv) * Q) *ᵥ deriv p t := by
      rw [Matrix.mulVec_sub, hQQ]
    have hA : (Qᵀ * Kinv) *ᵥ df = Qᵀ *ᵥ (Kinv *ᵥ df) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    have hC : ((Qᵀ * Kinv) * Q) *ᵥ deriv p t + C *ᵥ deriv p t
        = biotStorage Kinv Q C *ᵥ deriv p t := by
      rw [show biotStorage Kinv Q C = ((Qᵀ * Kinv) * Q) + C from rfl,
        Matrix.add_mulVec]
    rw [hQK, hsplit]
    have hsub : (Qᵀ * Kinv) *ᵥ df - ((Qᵀ * Kinv) * Q) *ᵥ deriv p t
        - C *ᵥ deriv p t
        = (Qᵀ * Kinv) *ᵥ df - biotStorage Kinv Q C *ᵥ deriv p t := by
      rw [← hC]
      abel
    rw [hsub, hred t, hA]
    abel
  · intro u' p' hsat' hu'0 hp'0
    obtain ⟨hu'_diff, hp'_diff, heq'⟩ := hsat'
    have hp'_ode : ∀ t, deriv p' t
        = (Sinv * H) *ᵥ p' t + Sinv *ᵥ (Qᵀ *ᵥ (Kinv *ᵥ df) - s) :=
      fun t => by
        obtain ⟨heq1, heq2⟩ := heq' t
        obtain ⟨-, hdp⟩ :=
          hrate K Kinv hK hK' Q C H _ _ df s (p' t) heq1 heq2
        have hred' : biotStorage Kinv Q C *ᵥ deriv p' t
            = Qᵀ *ᵥ (Kinv *ᵥ df) - s + H *ᵥ p' t := by
          simpa [biotStorage] using hdp
        have hback : Sinv *ᵥ (biotStorage Kinv Q C *ᵥ deriv p' t)
            = deriv p' t := by
          rw [Matrix.mulVec_mulVec, hS', Matrix.one_mulVec]
        have h2 : Sinv *ᵥ (H *ᵥ p' t) = (Sinv * H) *ᵥ p' t :=
          Matrix.mulVec_mulVec _ _ _
        have hsplit : Sinv *ᵥ (Qᵀ *ᵥ (Kinv *ᵥ df) - s + H *ᵥ p' t)
            = Sinv *ᵥ (Qᵀ *ᵥ (Kinv *ᵥ df) - s)
              + (Sinv * H) *ᵥ p' t := by
          rw [Matrix.mulVec_add, h2]
        have h := congrArg (Sinv *ᵥ ·) hred'
        rw [hback, hsplit] at h
        rw [h, add_comm]
    have hpp : p' = p := hp_unique p' hp'0 hp'_diff hp'_ode
    have hu'_deriv : ∀ t, deriv u' t = Kinv *ᵥ (df - Q *ᵥ deriv p' t) :=
      fun t => by
        obtain ⟨heq1, heq2⟩ := heq' t
        obtain ⟨hdu, -⟩ :=
          hrate K Kinv hK hK' Q C H _ _ df s (p' t) heq1 heq2
        exact hdu
    have hderiv_eq : ∀ t, deriv u' t
        = deriv (fun t => u0 + Kinv *ᵥ (t • df - Q *ᵥ (p t - p0))) t :=
      fun t => by
        rw [hu'_deriv t, hu_deriv t, hpp]
    have hw : Differentiable ℝ
        (u' - fun t => u0 + Kinv *ᵥ (t • df - Q *ᵥ (p t - p0))) :=
      hu'_diff.sub hu_diff
    have hw0 : ∀ t, deriv
        (u' - fun t => u0 + Kinv *ᵥ (t • df - Q *ᵥ (p t - p0))) t = 0 :=
      fun t => by
        rw [deriv_sub (hu'_diff t) (hu_diff t), hderiv_eq t, sub_self]
    have hconst := is_const_of_deriv_eq_zero hw hw0
    have hU0 : ∀ t, (u' - fun t => u0 + Kinv *ᵥ (t • df - Q *ᵥ (p t - p0))) t
        = 0 := fun t => by
      have h := hconst t 0
      have h0 : (u' - fun t => u0 + Kinv *ᵥ (t • df - Q *ᵥ (p t - p0))) 0
          = 0 := by
        simp [Pi.sub_apply, hu'0, hp0]
      rw [h0] at h
      exact h
    have hsub : u' - (fun t => u0 + Kinv *ᵥ (t • df - Q *ᵥ (p t - p0))) = 0 :=
      funext hU0
    have huu : u' = fun t => u0 + Kinv *ᵥ (t • df - Q *ᵥ (p t - p0)) :=
      sub_eq_zero.mp hsub
    exact ⟨huu, hpp⟩

/-- Singular rejection: when no dynamics remain (`Q = 0`,
`C = 0`, `df = 0`), a solution forces the source `s` to lie in
the range of `H`; a source outside a singular `H` range admits
no solution. -/
private theorem biot_source_mem_range_of_no_dynamics_of {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {K : Matrix n n ℝ} {H : Matrix m m ℝ}
    {s : m → ℝ} {u : ℝ → n → ℝ} {p : ℝ → m → ℝ}
    (hsat : SatisfiesBiotRateSystemAux K 0 0 H 0 s u p) :
    ∃ w : m → ℝ, s = H *ᵥ w := by
  obtain ⟨-, -, heq⟩ := hsat
  obtain ⟨-, heq2⟩ := heq 0
  simp at heq2
  exact ⟨p 0, sub_eq_zero.mp heq2.symm⟩

/-! ## C. Public evolution results -/

open MathlibExt.Analysis.ODE.DuhamelWanted in
/-- Finite linear-ODE existence and uniqueness in `deriv`
form, from the canonical Duhamel variation-of-constants
theorem at the matrix operator. -/
private theorem linearODE_existsUnique {m : Type*} [Fintype m]
    [DecidableEq m] (A : Matrix m m ℝ) (b : m → ℝ) (p0 : m → ℝ) :
    ∃ p : ℝ → m → ℝ, p 0 = p0 ∧ Differentiable ℝ p
      ∧ (∀ t, deriv p t = A *ᵥ p t + b)
      ∧ ∀ p' : ℝ → m → ℝ, p' 0 = p0 → Differentiable ℝ p'
        → (∀ t, deriv p' t = A *ᵥ p' t + b) → p' = p := by
  obtain ⟨x, hx0, -, hderiv, huniq⟩ :=
    duhamel_variation_of_constants
      (LinearMap.toContinuousLinearMap (Matrix.toLin' A))
      (fun _ => b) 0 p0 (continuous_const)
  refine ⟨x, hx0, fun t => (hderiv t).differentiableAt, ?_, ?_⟩
  · intro t
    have h := (hderiv t).deriv
    exact h
  · intro p' hp'0 hp'diff hp'deriv
    exact huniq p' hp'0 (fun t => by
      have h := (hp'diff t).hasDerivAt
      rwa [hp'deriv t] at h)

/-- The pressure rate of a Biot solution solves the reduced
storage equation, and the displacement rate is recovered from
the equilibrium rate equation. -/
private theorem biot_pressure_rate_eq_aux {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    {K Kinv : Matrix n n ℝ} (hK : K * Kinv = 1)
    (hK' : Kinv * K = 1)
    {Q : Matrix n m ℝ} {C H : Matrix m m ℝ}
    {df : n → ℝ} {s : m → ℝ} {u : ℝ → n → ℝ} {p : ℝ → m → ℝ}
    (hsat : SatisfiesBiotRateSystemAux K Q C H df s u p) (t : ℝ) :
    biotStorage Kinv Q C *ᵥ deriv p t
        = Qᵀ *ᵥ (Kinv *ᵥ df) - s + H *ᵥ p t
      ∧ deriv u t = Kinv *ᵥ (df - Q *ᵥ deriv p t) :=
  biot_pressure_rate_eq_of BiotSchur.biot_rate_equation hK hK' hsat t

/-- Existence and uniqueness for the nonsingular finite Biot
rate system with constant forcing and positive-definite
reduced storage. -/
private theorem biot_existsUnique_aux {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    {K Kinv : Matrix n n ℝ} {Q : Matrix n m ℝ}
    {C H : Matrix m m ℝ}
    (hK : K * Kinv = 1) (hK' : Kinv * K = 1)
    (hS : (biotStorage Kinv Q C).PosDef)
    {df : n → ℝ} {s : m → ℝ} (u0 : n → ℝ) (p0 : m → ℝ) :
    ∃ u : ℝ → n → ℝ, ∃ p : ℝ → m → ℝ,
      SatisfiesBiotRateSystemAux K Q C H df s u p
        ∧ u 0 = u0 ∧ p 0 = p0
        ∧ ∀ u' : ℝ → n → ℝ, ∀ p' : ℝ → m → ℝ,
            SatisfiesBiotRateSystemAux K Q C H df s u' p'
            → u' 0 = u0 → p' 0 = p0 → u' = u ∧ p' = p := by
  have hunit : IsUnit (biotStorage Kinv Q C).det :=
    isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  letI := Matrix.invertibleOfIsUnitDet (biotStorage Kinv Q C) hunit
  exact biot_existsUnique_of BiotSchur.biot_rate_equation
    linearODE_existsUnique hK hK'
    (Matrix.mul_inv_of_invertible _) (Matrix.inv_mul_of_invertible _)
    u0 p0

/-- The finite Biot rate system with constant load rate `df`
and constant source `s`: paths `u, p` are differentiable and
at every time the rates satisfy the equilibrium rate equation
`K *ᵥ u' + Q *ᵥ p' = df` and the storage balance
`-Qᵀ *ᵥ u' + C *ᵥ p' = s - H *ᵥ p`, the dissipative sign
convention (with `Q = 0`, `C = H = I`, `s = 0` the pressure
decays: `p' = -p`). Nonsingularity hypotheses are carried by
the theorems that need them. -/
def SatisfiesBiotRateSystem {n m : Type*} [Fintype n] [Fintype m]
    (K : Matrix n n ℝ) (Q : Matrix n m ℝ) (C H : Matrix m m ℝ)
    (df : n → ℝ) (s : m → ℝ)
    (u : ℝ → n → ℝ) (p : ℝ → m → ℝ) : Prop :=
  Differentiable ℝ u ∧ Differentiable ℝ p ∧ ∀ t : ℝ,
    (K *ᵥ deriv u t + Q *ᵥ deriv p t = df)
      ∧ (-(Qᵀ *ᵥ deriv u t) + C *ᵥ deriv p t = s - H *ᵥ p t)

/-- The public (dissipative-sign) rate system is the auxiliary
transported system at `(-Q, -H)` on the negated pressure
path. -/
private theorem satisfiesBiotRateSystem_iff_aux {n m : Type*}
    [Fintype n] [Fintype m] {K : Matrix n n ℝ}
    {Q : Matrix n m ℝ} {C H : Matrix m m ℝ} {df : n → ℝ}
    {s : m → ℝ} {u : ℝ → n → ℝ} {p : ℝ → m → ℝ} :
    SatisfiesBiotRateSystem K Q C H df s u p
      ↔ SatisfiesBiotRateSystemAux K (-Q) C (-H) df s u
          (fun t => -p t) := by
  constructor
  · rintro ⟨hu, hp, heq⟩
    refine ⟨hu, hp.neg, fun t => ?_⟩
    have hderiv : deriv (fun t => -p t) t = -deriv p t :=
      ((hp t).hasDerivAt.neg).deriv
    obtain ⟨h1, h2⟩ := heq t
    refine ⟨?_, ?_⟩
    · rw [hderiv, Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg]
      exact h1
    · rw [hderiv]
      simp only [Matrix.transpose_neg, Matrix.neg_mulVec,
        Matrix.mulVec_neg, neg_neg, sub_neg_eq_add]
      exact h2
  · rintro ⟨hu, hp, heq⟩
    have hp' : Differentiable ℝ p := by
      have h := hp.neg
      simpa using h
    refine ⟨hu, hp', fun t => ?_⟩
    have hderiv : deriv (fun t => -p t) t = -deriv p t :=
      ((hp' t).hasDerivAt.neg).deriv
    obtain ⟨h1, h2⟩ := heq t
    rw [hderiv, Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg] at h1
    rw [hderiv] at h2
    simp only [Matrix.transpose_neg, Matrix.neg_mulVec,
      Matrix.mulVec_neg, neg_neg, sub_neg_eq_add] at h2
    exact ⟨h1, h2⟩

/-- Negating the coupling does not change reduced storage. -/
private theorem biotStorage_neg {n m : Type*} [Fintype n]
    [Fintype m] (Kinv : Matrix n n ℝ) (Q : Matrix n m ℝ)
    (C : Matrix m m ℝ) :
    biotStorage Kinv (-Q) C = biotStorage Kinv Q C := by
  simp [biotStorage, Matrix.transpose_neg, Matrix.neg_mul,
    Matrix.mul_neg]

/-- The pressure rate of a Biot solution solves the reduced
storage equation `S p' = Qᵀ K⁻¹ df + s - H p` (dissipative in
`H`), and the displacement rate is recovered from the
equilibrium rate equation. -/
theorem biot_pressure_rate_eq {n m : Type*} [Fintype n]
    [Fintype m] [DecidableEq n] [DecidableEq m]
    {K Kinv : Matrix n n ℝ} (hK : K * Kinv = 1)
    (hK' : Kinv * K = 1)
    {Q : Matrix n m ℝ} {C H : Matrix m m ℝ}
    {df : n → ℝ} {s : m → ℝ} {u : ℝ → n → ℝ} {p : ℝ → m → ℝ}
    (hsat : SatisfiesBiotRateSystem K Q C H df s u p) (t : ℝ) :
    biotStorage Kinv Q C *ᵥ deriv p t
        = Qᵀ *ᵥ (Kinv *ᵥ df) + s - H *ᵥ p t
      ∧ deriv u t = Kinv *ᵥ (df - Q *ᵥ deriv p t) := by
  have haux := satisfiesBiotRateSystem_iff_aux.mp hsat
  obtain ⟨h1, h2⟩ := biot_pressure_rate_eq_aux hK hK' haux t
  rw [biotStorage_neg] at h1
  have hderiv : deriv (fun t => -p t) t = -deriv p t :=
    ((hsat.2.1 t).hasDerivAt.neg).deriv
  rw [hderiv, Matrix.mulVec_neg] at h1
  rw [hderiv] at h2
  simp only [Matrix.transpose_neg, Matrix.neg_mulVec,
    Matrix.mulVec_neg, neg_neg] at h1 h2
  refine ⟨?_, h2⟩
  apply neg_inj.mp
  rw [h1, Matrix.mulVec_mulVec]
  abel

/-- Existence and uniqueness for the nonsingular finite Biot
rate system with constant forcing and positive-definite
reduced storage. -/
theorem biot_existsUnique {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    {K Kinv : Matrix n n ℝ} {Q : Matrix n m ℝ}
    {C H : Matrix m m ℝ}
    (hK : K * Kinv = 1) (hK' : Kinv * K = 1)
    (hS : (biotStorage Kinv Q C).PosDef)
    {df : n → ℝ} {s : m → ℝ} (u0 : n → ℝ) (p0 : m → ℝ) :
    ∃ u : ℝ → n → ℝ, ∃ p : ℝ → m → ℝ,
      SatisfiesBiotRateSystem K Q C H df s u p
        ∧ u 0 = u0 ∧ p 0 = p0
        ∧ ∀ u' : ℝ → n → ℝ, ∀ p' : ℝ → m → ℝ,
            SatisfiesBiotRateSystem K Q C H df s u' p'
            → u' 0 = u0 → p' 0 = p0 → u' = u ∧ p' = p := by
  rw [← biotStorage_neg Kinv Q C] at hS
  obtain ⟨u, pq, hsat, hu0, hp0, huniq⟩ :=
    biot_existsUnique_aux hK hK' hS u0 (-p0)
  refine ⟨u, fun t => -pq t, ?_, hu0, by simp [hp0], ?_⟩
  · exact satisfiesBiotRateSystem_iff_aux.mpr (by simpa using hsat)
  · intro u' p' hsat' hu0' hp0'
    have haux' := satisfiesBiotRateSystem_iff_aux.mp hsat'
    obtain ⟨huu, hpq⟩ := huniq u' (fun t => -p' t) haux' hu0'
      (by simp [hp0'])
    refine ⟨huu, ?_⟩
    funext t
    have h := congrFun hpq t
    simpa using congrArg Neg.neg h

/-- Singular rejection: when no dynamics remain (`Q = 0`,
`C = 0`, `df = 0`), a solution forces the source `s` to lie in
the range of `H`. -/
theorem biot_source_mem_range_of_no_dynamics {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {K : Matrix n n ℝ} {H : Matrix m m ℝ}
    {s : m → ℝ} {u : ℝ → n → ℝ} {p : ℝ → m → ℝ}
    (hsat : SatisfiesBiotRateSystem K 0 0 H 0 s u p) :
    ∃ w : m → ℝ, s = H *ᵥ w := by
  have haux := satisfiesBiotRateSystem_iff_aux.mp hsat
  obtain ⟨w, hw⟩ := biot_source_mem_range_of_no_dynamics_of
    (by simpa using haux)
  exact ⟨-w, by simp [hw, Matrix.neg_mulVec, Matrix.mulVec_neg]⟩

end EarthScience
