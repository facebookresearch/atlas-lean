/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Classical balance laws and harmonic mechanics

Oscillator energy, force and moment balance, and finite spring networks with stiffness matrices
and normal modes.

## i. Overview

Section A treats the one-dimensional oscillator with real-valued position `x` and velocity `v`,
`x' = v`, `v' = -(k / m) * x`: the energy `(1 / 2) * m * v ^ 2 + (1 / 2) * k * x ^ 2` has
derivative `0` along a solution, so it takes the same value at any two times, and the cosine
solution carries the energy `(1 / 2) * k * A ^ 2`. Only first-order derivative hypotheses and
`m ≠ 0` are assumed. The same conservation law is stated for smooth trajectories in
`EuclideanSpace ℝ (Fin 1)` with `m, k > 0` in Physlib
(`ClassicalMechanics.HarmonicOscillator.energy_conservation_of_equationOfMotion'`), and for unit
mass with velocity `deriv x` in `EarthScience.oscillator_energy_const`.

Section B covers resultant forces, action-reaction cancellation, 2D scalar moments, and discrete
work. Section C covers finite spring networks: energy, stiffness matrix, zero modes,
mass-orthogonal normal modes, and nonnegative generalized eigenvalues.

Newton's equation, the balance conditions, and the linear spring law are model assumptions,
carried as explicit hypotheses or definitions. Continuum stress and strain are in
`PhyslibExt.CondensedMatter.Elasticity.StressStrain`.

## ii. Key results

* `hasDerivAt_oscillatorEnergy`: the oscillator energy has derivative `0` at each time of a
  solution.
* `oscillatorEnergy_const`: energy conservation, the energy is the same at any two times.
* `oscillator_explicit_solution`: the cosine/sine pair solves Newton's equation with energy
  `(1 / 2) * k * A ^ 2`.
* `sum_pairwise_antisymmetric_eq_zero`: action-reaction cancellation for
  real-valued pair forces.
* `moment2D_add`, `central_pair_moment_eq_zero`: 2D moment linearity and the
  single central-pair zero moment (no-body-couple model).
* `totalWork_add`: discrete work distributes over force families.
* `springEnergy_eq_quadForm`: for reciprocal weights without self-springs, the
  spring energy equals `(1 / 2)` times the stiffness quadratic form;
  `springEnergy_nonneg`.
* `stiffnessMatrix_transpose`: for reciprocal weights the stiffness matrix is
  symmetric.
* `stiffnessMatrix_mulVec_one`, `stiffnessMatrix_free_zeroMode`,
  `springEnergy_free_const`: without self-springs the stiffness matrix sends
  the all-ones vector to `w`, so rigid translations are in its kernel only in
  the free (`w = 0`) case, where they also carry zero energy;
  `stiffnessMatrix_fixedEnds_rowNonzero` for fixed ends.
* `stiffnessMatrix_free_not_posDef`: on a nonempty node type without
  self-springs, the stiffness matrix of a free network is not positive
  definite.
* `innerProductM_eq_zero_of_ne`: for a symmetric stiffness, normal modes with
  distinct eigenvalues are mass-orthogonal.
* `rayleigh_nonneg`: generalized eigenvalues are nonnegative for spring
  stiffness (reciprocal nonnegative weights, no self-springs, nonnegative
  walls) and positive masses.

## iii. Table of contents

* A. Harmonic oscillator energy, conservation, and explicit solution.
* B. Resultant force, action-reaction, 2D moment, and discrete work.
* C. Finite spring networks, stiffness matrices, and normal modes.

## iv. References

* Physlib, `ClassicalMechanics/HarmonicOscillator/Basic.lean`: the harmonic oscillator with
  trajectories in `EuclideanSpace ℝ (Fin 1)`, its equation of motion, and energy conservation.
-/

@[expose] public section

open scoped Matrix
open scoped BigOperators

namespace PhyslibExt.Mechanics.HarmonicMechanics

/-! ## A. Harmonic oscillator energy, conservation, and explicit solution. -/

/-- Oscillator energy: kinetic plus harmonic potential energy. -/
noncomputable def oscillatorEnergy (m k x v : ℝ) : ℝ :=
  (1 / 2) * m * v ^ 2 + (1 / 2) * k * x ^ 2

/-- Energy derivative (MC): if at time `t` the position has derivative `v t` and the velocity
has derivative `-(k / m) * x t` (Newton's equation in divided form, MOD), then the oscillator
energy has derivative `0` at `t`. `oscillatorEnergy_const` turns this into conservation. -/
lemma hasDerivAt_oscillatorEnergy (m k : ℝ) (x v : ℝ → ℝ) (t : ℝ)
    (hm : m ≠ 0)
    (hx : HasDerivAt x (v t) t)
    (hv : HasDerivAt v (-(k / m) * x t) t) :
    HasDerivAt (fun t => oscillatorEnergy m k (x t) (v t)) 0 t := by
  unfold oscillatorEnergy
  have hv2 : HasDerivAt (v * v)
      ((-(k / m) * x t) * v t + v t * (-(k / m) * x t)) t :=
    hv.mul hv
  have hx2 : HasDerivAt (x * x)
      (v t * x t + x t * v t) t :=
    hx.mul hx
  have hsum := (hv2.const_mul ((1 / 2) * m)).add (hx2.const_mul ((1 / 2) * k))
  have hder : ((1 / 2) * m) * ((-(k / m) * x t) * v t + v t * (-(k / m) * x t)) +
      ((1 / 2) * k) * (v t * x t + x t * v t) = 0 := by
    field_simp
    ring
  have hfg : ((fun y => ((1 / 2) * m) * (v * v) y) +
      (fun y => ((1 / 2) * k) * (x * x) y)) =
      (fun t => ((1 / 2) * m) * (v t) ^ 2 + ((1 / 2) * k) * (x t) ^ 2) := by
    funext t
    simp only [Pi.add_apply, Pi.mul_apply, ← pow_two]
  rw [hfg, hder] at hsum
  exact hsum

/-- Energy conservation (MC): along a solution of `x' = v`, `v' = -(k / m) * x` at all times
(MOD), the oscillator energy takes the same value at any two times. -/
lemma oscillatorEnergy_const (m k : ℝ) (x v : ℝ → ℝ) (hm : m ≠ 0)
    (hx : ∀ t, HasDerivAt x (v t) t)
    (hv : ∀ t, HasDerivAt v (-(k / m) * x t) t) (t₁ t₂ : ℝ) :
    oscillatorEnergy m k (x t₁) (v t₁) = oscillatorEnergy m k (x t₂) (v t₂) := by
  have hE : ∀ t, HasDerivAt (fun t => oscillatorEnergy m k (x t) (v t)) 0 t :=
    fun t => hasDerivAt_oscillatorEnergy m k x v t hm (hx t) (hv t)
  exact is_const_of_deriv_eq_zero (fun t => (hE t).differentiableAt) (fun t => (hE t).deriv)
    t₁ t₂

/-- Explicit solution (MC): for positive mass and stiffness, with
`ω = Real.sqrt (k / m)`, the cosine/sine pair satisfies Newton's divided
equation and carries the constant energy `(1 / 2) * k * A ^ 2`. -/
lemma oscillator_explicit_solution (m k A ω t : ℝ) (hm : 0 < m) (hk : 0 < k)
    (hω : ω = Real.sqrt (k / m)) :
    HasDerivAt (fun t : ℝ => A * Real.cos (ω * t))
      (-A * ω * Real.sin (ω * t)) t ∧
    HasDerivAt (fun t : ℝ => -A * ω * Real.sin (ω * t))
      (-(k / m) * (A * Real.cos (ω * t))) t ∧
    oscillatorEnergy m k (A * Real.cos (ω * t))
        (-A * ω * Real.sin (ω * t)) = (1 / 2) * k * A ^ 2 := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hω2 : ω ^ 2 = k / m := by
    rw [hω]
    exact Real.sq_sqrt (le_of_lt (div_pos hk hm))
  have hlin : HasDerivAt (fun t : ℝ => ω * t) ω t := by
    have h := (hasDerivAt_id t).const_mul ω
    simpa using h
  refine ⟨?_, ?_, ?_⟩
  · have hcos : HasDerivAt (fun t : ℝ => A * Real.cos (ω * t))
        (A * (-Real.sin (ω * t) * ω)) t :=
      hlin.cos.const_mul A
    have hd1 : A * (-Real.sin (ω * t) * ω) = -A * ω * Real.sin (ω * t) := by
      ring
    rw [hd1] at hcos
    exact hcos
  · have hsin : HasDerivAt (fun t : ℝ => -A * ω * Real.sin (ω * t))
        ((-A * ω) * (Real.cos (ω * t) * ω)) t :=
      hlin.sin.const_mul (-A * ω)
    have hd2 : (-A * ω) * (Real.cos (ω * t) * ω) =
        -(k / m) * (A * Real.cos (ω * t)) := by
      have hfactor : (-A * ω) * (Real.cos (ω * t) * ω) =
          -A * Real.cos (ω * t) * (ω ^ 2) := by ring
      rw [hfactor, hω2]
      ring
    rw [hd2] at hsin
    exact hsin
  · have hcs : Real.cos (ω * t) ^ 2 + Real.sin (ω * t) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq _
    have hmω : m * ω ^ 2 = k := by
      rw [hω2, div_eq_mul_inv, ← mul_assoc, mul_comm m k, mul_assoc,
        mul_inv_cancel₀ hm0, mul_one]
    unfold oscillatorEnergy
    linear_combination ((1 / 2) * A ^ 2 * (Real.sin (ω * t)) ^ 2) * hmω +
      ((1 / 2) * k * A ^ 2) * hcs

/-! ## B. Resultant force, action-reaction, 2D moment, and discrete work. -/

/-- Resultant of a family of forces: the sum over the family index. -/
noncomputable def resultantForce {ρ ι : Type*} [Fintype ρ] (F : ρ → (ι → ℝ)) :
    ι → ℝ :=
  ∑ r, F r

/-- Equilibrium predicate: the resultant force vanishes. -/
noncomputable def IsEquilibrated {ρ ι : Type*} [Fintype ρ] (F : ρ → (ι → ℝ)) :
    Prop :=
  resultantForce F = 0

/-- Equilibrium unfolds to the vanishing of the force sum; nothing more. -/
lemma isEquilibrated_iff {ρ ι : Type*} [Fintype ρ] (F : ρ → (ι → ℝ)) :
    IsEquilibrated F ↔ ∑ r, F r = 0 := by
  simp only [IsEquilibrated, resultantForce]

/-- Action-reaction cancellation (MC): pair forces on a finite type,
antisymmetric under pair swap with `F (j, i) = -F (i, j)`, sum to zero.
Stated for real-valued pair forces: over a general additive group the claim
is false (diagonal terms are only 2-torsion), so the vector case follows by
applying this lemma pointwise (see the test file). -/
lemma sum_pairwise_antisymmetric_eq_zero {ι : Type*} [Fintype ι]
    (F : ι × ι → ℝ) (h : ∀ i j, F (j, i) = -F (i, j)) :
    ∑ p, F p = 0 := by
  have hcomp := Equiv.sum_comp (Equiv.prodComm ι ι) F
  have hsym : ∑ p, F (Equiv.prodComm ι ι p) = ∑ p, -F p := by
    apply Finset.sum_congr rfl
    intro p _
    obtain ⟨i, j⟩ := p
    exact h i j
  have hneg : ∑ p, -F p = -∑ p, F p := Finset.sum_neg_distrib F
  have hself : -∑ p, F p = ∑ p, F p := by
    rw [← hneg, ← hsym, hcomp]
  linarith

/-- 2D scalar moment about the origin:
`∑ i, r i 0 * F i 1 - r i 1 * F i 0`. Only 2D scalar moments are treated in
this module; there are no 3D cross-product moments. -/
noncomputable def moment2D {ρ : Type*} [Fintype ρ] (r F : ρ → (Fin 2 → ℝ)) :
    ℝ :=
  ∑ i, (r i 0 * F i 1 - r i 1 * F i 0)

/-- Linearity (MC): the moment of a sum of force families is the sum of the
moments. -/
lemma moment2D_add {ρ : Type*} [Fintype ρ] (r F G : ρ → (Fin 2 → ℝ)) :
    moment2D r (fun i => F i + G i) = moment2D r F + moment2D r G := by
  unfold moment2D
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

/-- Single central-pair zero moment (MC, no-body-couple model): one pair of
forces, equal, opposite, and each a scalar multiple of the separation vector
`q - p` (centrality hypothesis), has zero total 2D moment about any point
`o`. Together with `moment2D_add` this is the single-pair case; the summed
pairwise-central statement over many pairs is not claimed. -/
lemma central_pair_moment_eq_zero (p q o : Fin 2 → ℝ) (c : ℝ) :
    ((p 0 - o 0) * (c • (q - p)) 1 - (p 1 - o 1) * (c • (q - p)) 0) +
      ((q 0 - o 0) * (-(c • (q - p))) 1 - (q 1 - o 1) * (-(c • (q - p))) 0) =
      0 := by
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- Discrete work of a force family under a common constant displacement.
This is the discrete constant-displacement work, not a path-dependent
integral. -/
noncomputable def totalWork {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (F : ρ → (ι → ℝ)) (d : ι → ℝ) : ℝ :=
  ∑ r, ∑ i, F r i * d i

/-- Work distribution (MC): the work of a sum of force families is the sum
of the works. -/
lemma totalWork_add {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (F G : ρ → (ι → ℝ)) (d : ι → ℝ) :
    totalWork (fun r => F r + G r) d = totalWork F d + totalWork G d := by
  unfold totalWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

/-! ## C. Finite spring networks, stiffness matrices, and normal modes. -/

/-- Spring-network energy (DEF) for scalar displacements on a finite node
type: pair weights `k i j` plus wall springs of stiffness `w i` from node `i`
to a fixed wall. `w = 0` is the free network; `w i > 0` is a fixed end. The
definition accepts any `k`, but it is the physical spring energy only for
reciprocal weights `k i j = k j i` (as in `springEnergy_eq_quadForm`): the
ordered double sum then counts each spring twice, so the `1 / 4` gives each
spring its energy `(1 / 2) * k i j * (u j - u i) ^ 2`, and diagonal terms
vanish. For other `k` the pair `{i, j}` gets the average weight
`(k i j + k j i) / 2`. -/
noncomputable def springEnergy {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (w : ι → ℝ) (u : ι → ℝ) : ℝ :=
  (1 / 4) * (∑ i, ∑ j, k i j * (u j - u i) ^ 2) +
    (1 / 2) * (∑ i, w i * u i ^ 2)

/-- Stiffness matrix (DEF): diagonal `(∑ j, k i j) + w i`, off-diagonal
`-k i j`. For reciprocal weights without self-springs (`k i j = k j i`,
`k i i = 0`), row `i` is the force balance on node `i` and half the quadratic
form is `springEnergy` (`springEnergy_eq_quadForm`). -/
noncomputable def stiffnessMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ι → ℝ) (w : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => if i = j then (∑ l, k i l) + w i else -k i j

/-- Diagonal entries of the stiffness matrix. -/
lemma stiffnessMatrix_apply_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ι → ι → ℝ} {w : ι → ℝ} {i : ι} :
    stiffnessMatrix k w i i = (∑ l, k i l) + w i := by
  unfold stiffnessMatrix
  simp

/-- Off-diagonal entries of the stiffness matrix. -/
lemma stiffnessMatrix_apply_offdiag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ι → ι → ℝ} {w : ι → ℝ} {i j : ι} (h : i ≠ j) :
    stiffnessMatrix k w i j = -k i j := by
  unfold stiffnessMatrix
  simp [h]

/-- Energy-quadratic-form identity (MC): the spring energy equals `(1 / 2)`
times the stiffness quadratic form. -/
lemma springEnergy_eq_quadForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ι → ℝ) (w : ι → ℝ) (u : ι → ℝ)
    (hksymm : ∀ i j, k i j = k j i)
    (hkii : ∀ i, k i i = 0) :
    springEnergy k w u =
      (1 / 2) * dotProduct u (stiffnessMatrix k w *ᵥ u) := by
  have hKu : ∀ i, (stiffnessMatrix k w *ᵥ u) i =
      ((∑ j, k i j) + w i) * u i - ∑ j, k i j * u j := by
    intro i
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, stiffnessMatrix]
    have hterm : ∀ j, (if i = j then (∑ l, k i l) + w i else -k i j) * u j =
        (if i = j then (((∑ l, k i l) + w i) * u j) else 0) - k i j * u j := by
      intro j
      by_cases h : i = j
      · rw [ite_eq_left h, ite_eq_left h, h, hkii j]
        ring
      · rw [ite_eq_right h, ite_eq_right h]
        ring
    have hcongr :
        (∑ j, (if i = j then (∑ l, k i l) + w i else -k i j) * u j) =
          ∑ j, ((if i = j then (((∑ l, k i l) + w i) * u j) else 0) -
            k i j * u j) :=
      Finset.sum_congr rfl (fun j _ => hterm j)
    have hite : (∑ j, (if i = j then (((∑ l, k i l) + w i) * u j) else (0 : ℝ))) =
        ((∑ l, k i l) + w i) * u i := by
      rw [Finset.sum_ite_eq]
      simp
    rw [hcongr, Finset.sum_sub_distrib, hite]
  have hE1 : (∑ i, ∑ j, k i j * (u j - u i) ^ 2) =
      (∑ i, ∑ j, k i j * u j ^ 2) + (∑ i, ∑ j, k i j * u i ^ 2) -
        ∑ i, ∑ j, k i j * (2 * u i * u j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hQ : (∑ i, ∑ j, k i j * u i ^ 2) = ∑ i, (∑ j, k i j) * u i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact (Finset.sum_mul _ _ _).symm
  have hP : (∑ i, ∑ j, k i j * u j ^ 2) = ∑ i, (∑ j, k i j) * u i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hksymm i j]
  have hR : (∑ i, ∑ j, k i j * (2 * u i * u j)) =
      ∑ i, 2 * u i * (∑ j, k i j * u j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hA2 : (∑ i, ∑ j, k i j * (u j - u i) ^ 2) =
      ∑ i, (2 * ((∑ j, k i j) * u i ^ 2) - 2 * u i * (∑ j, k i j * u j)) := by
    rw [hE1, hP, hQ, hR, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdot : dotProduct u (stiffnessMatrix k w *ᵥ u) =
      ∑ i, u i * (((∑ j, k i j) + w i) * u i - ∑ j, k i j * u j) := by
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    rw [hKu]
  unfold springEnergy
  rw [hdot, hA2]
  rw [Finset.mul_sum _ _ (1 / 4), Finset.mul_sum _ _ (1 / 2),
    Finset.mul_sum _ _ (1 / 2)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Energy nonnegativity (MC): the spring energy is nonnegative for
nonnegative stiffnesses. -/
lemma springEnergy_nonneg {ι : Type*} [Fintype ι]
    (k : ι → ι → ℝ) (w : ι → ℝ) (u : ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ springEnergy k w u := by
  unfold springEnergy
  apply add_nonneg
  · apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (hk i j)
    exact sq_nonneg _
  · apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (hw i)
    exact sq_nonneg _

/-- Symmetry (MC): the stiffness matrix is symmetric for symmetric pair
stiffness, stated as transpose equality. -/
lemma stiffnessMatrix_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ι → ℝ) (w : ι → ℝ)
    (hksymm : ∀ i j, k i j = k j i) :
    (stiffnessMatrix k w)ᵀ = stiffnessMatrix k w := by
  apply Matrix.ext
  intro i j
  rw [Matrix.transpose_apply]
  by_cases h : i = j
  · rw [h]
  · rw [stiffnessMatrix_apply_offdiag (Ne.symm h),
      stiffnessMatrix_apply_offdiag h, hksymm j i]

/-- Row-sum identity (MC): the stiffness matrix applied to the all-ones
vector recovers the wall stiffnesses. -/
lemma stiffnessMatrix_mulVec_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ι → ℝ) (w : ι → ℝ) (hkii : ∀ i, k i i = 0) :
    stiffnessMatrix k w *ᵥ (fun _ => (1 : ℝ)) = w := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  have hterm : ∀ j, stiffnessMatrix k w i j * (1 : ℝ) =
      (if i = j then ((∑ l, k i l) + w i) else 0) - k i j := by
    intro j
    by_cases h : i = j
    · rw [h, stiffnessMatrix_apply_diag, ite_eq_left rfl, hkii j, mul_one,
        sub_zero]
    · rw [stiffnessMatrix_apply_offdiag h, ite_eq_right h]
      ring
  have hcongr : (∑ j, stiffnessMatrix k w i j * 1) =
      ∑ j, ((if i = j then ((∑ l, k i l) + w i) else 0) - k i j) :=
    Finset.sum_congr rfl (fun j _ => hterm j)
  have hite : (∑ j, (if i = j then ((∑ l, k i l) + w i) else (0 : ℝ))) =
      (∑ j, k i j) + w i := by
    rw [Finset.sum_ite_eq]
    simp
  rw [hcongr, Finset.sum_sub_distrib, hite]
  ring

/-- Rigid-translation kernel identity (MC, free network only): with `w = 0` the
stiffness matrix sends the all-ones vector to `0`. On an empty node type that
vector is itself `0` and the identity is trivial; see
`stiffnessMatrix_free_not_posDef` for the nonempty case. -/
lemma stiffnessMatrix_free_zeroMode {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ι → ℝ) (hkii : ∀ i, k i i = 0) :
    stiffnessMatrix k 0 *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  rw [stiffnessMatrix_mulVec_one k 0 hkii]

/-- The stiffness matrix of a free network is not positive definite (MC): on a
nonempty node type the all-ones vector is nonzero and, by
`stiffnessMatrix_free_zeroMode`, in its kernel. `[Nonempty ι]` cannot be
dropped: on an empty node type every matrix is positive definite, vacuously. -/
lemma stiffnessMatrix_free_not_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (k : ι → ι → ℝ) (hkii : ∀ i, k i i = 0) :
    ¬ (stiffnessMatrix k 0).PosDef := by
  intro hK
  have hone : (fun _ => (1 : ℝ)) ≠ (0 : ι → ℝ) := fun h =>
    one_ne_zero (congrFun h (Classical.arbitrary ι))
  have hpos := hK.dotProduct_mulVec_pos hone
  rw [stiffnessMatrix_free_zeroMode k hkii, dotProduct_zero] at hpos
  exact lt_irrefl 0 hpos

/-- Constant displacements of a free network carry zero energy. -/
lemma springEnergy_free_const {ι : Type*} [Fintype ι]
    (k : ι → ι → ℝ) (c : ℝ) :
    springEnergy k 0 (fun _ => c) = 0 := by
  unfold springEnergy
  have hpair : (∑ i, ∑ j, k i j * ((fun _ => c) j - (fun _ => c) i) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    change k i j * (c - c) ^ 2 = 0
    rw [sub_self, pow_two, mul_zero, mul_zero]
  have hwall : (∑ i, (0 : ι → ℝ) i * (fun _ => c) i ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [Pi.zero_apply, zero_mul]
  rw [hpair, hwall]
  simp

/-- Fixed-end networks have no rigid-translation zero mode (MC): at any node
with positive wall stiffness, the all-ones vector is not in the kernel. -/
lemma stiffnessMatrix_fixedEnds_rowNonzero {ι : Type*} [Fintype ι]
    [DecidableEq ι] (k : ι → ι → ℝ) (w : ι → ℝ) (i : ι)
    (hkii : ∀ i, k i i = 0) (hw : 0 < w i) :
    (stiffnessMatrix k w *ᵥ (fun _ => (1 : ℝ))) i ≠ 0 := by
  have h := congrFun (stiffnessMatrix_mulVec_one k w hkii) i
  rw [h]
  exact ne_of_gt hw

/-- Mass-weighted bilinear form (DEF) `∑ i, m i * v i * w i`; an inner product
when every mass is positive. -/
noncomputable def innerProductM {ι : Type*} [Fintype ι] (m : ι → ℝ)
    (v w : ι → ℝ) : ℝ :=
  ∑ i, m i * v i * w i

/-- Distinct normal modes are mass-orthogonal (MC): generalized eigenvectors
of a symmetric stiffness for distinct eigenvalues are orthogonal in
`innerProductM`. -/
lemma innerProductM_eq_zero_of_ne {ι : Type*} [Fintype ι]
    (K : Matrix ι ι ℝ) (m v w : ι → ℝ)
    (ω2 μ2 : ℝ) (hne : ω2 ≠ μ2)
    (hsymm : Kᵀ = K)
    (hv : K *ᵥ v = ω2 • (fun i => m i * v i))
    (hw : K *ᵥ w = μ2 • (fun i => m i * w i)) :
    innerProductM m v w = 0 := by
  have hsym_dot : dotProduct (K *ᵥ v) w = dotProduct v (K *ᵥ w) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm,
      dotProduct_comm]
  have hlhs : dotProduct (K *ᵥ v) w = ω2 * innerProductM m v w := by
    rw [hv]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, innerProductM,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrhs : dotProduct v (K *ᵥ w) = μ2 * innerProductM m v w := by
    rw [hw]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, innerProductM,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hlhs, hrhs] at hsym_dot
  have hIP : (ω2 - μ2) * innerProductM m v w = 0 := by
    linear_combination hsym_dot
  have hne' : ω2 - μ2 ≠ 0 := sub_ne_zero.mpr hne
  exact (mul_eq_zero.mp hIP).resolve_left hne'

/-- Rayleigh nonnegativity (MC, spring stiffness only): a generalized
eigenvalue of a spring stiffness matrix with positive masses is nonnegative
for nonzero modes. This is NOT claimed for an arbitrary symmetric `K`; it is
false in general. -/
lemma rayleigh_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ι → ℝ) (w : ι → ℝ) (m v : ι → ℝ) (lam : ℝ)
    (hksymm : ∀ i j, k i j = k j i)
    (hkii : ∀ i, k i i = 0)
    (hk : ∀ i j, 0 ≤ k i j) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ i, 0 < m i)
    (hv0 : v ≠ 0)
    (heig : stiffnessMatrix k w *ᵥ v = lam • (fun i => m i * v i)) :
    0 ≤ lam := by
  have hIP_pos : 0 < innerProductM m v v := by
    unfold innerProductM
    have hnn : ∀ i ∈ (Finset.univ : Finset ι), (0 : ℝ) ≤ m i * v i * v i := by
      intro i _
      have h1 : (0 : ℝ) ≤ m i * (v i * v i) :=
        mul_nonneg (le_of_lt (hm i)) (mul_self_nonneg _)
      rwa [mul_assoc]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
    have hj' : v j ≠ 0 := by simpa using hj
    have hpos : (0 : ℝ) < m j * v j * v j := by
      have h1 : (0 : ℝ) < m j * (v j * v j) :=
        mul_pos (hm j) (mul_self_pos.mpr hj')
      rwa [mul_assoc]
    exact Finset.sum_pos' hnn ⟨j, Finset.mem_univ j, hpos⟩
  have hdot : dotProduct v (stiffnessMatrix k w *ᵥ v) =
      lam * innerProductM m v v := by
    rw [heig]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, innerProductM,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hquad := springEnergy_eq_quadForm k w v hksymm hkii
  rw [hdot] at hquad
  have h2 : 2 * springEnergy k w v = lam * innerProductM m v v := by
    rw [hquad]
    ring
  have hse := springEnergy_nonneg k w v hk hw
  have hnn2 : (0 : ℝ) ≤ 2 * springEnergy k w v := by linarith
  rw [h2] at hnn2
  exact nonneg_of_mul_nonneg_left hnn2 hIP_pos

end PhyslibExt.Mechanics.HarmonicMechanics
