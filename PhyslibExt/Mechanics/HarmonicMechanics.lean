/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Classical balance laws, harmonic mechanics, and continuum bookkeeping

Finite spring networks, normal-mode identities, force/moment balance, and
continuum bookkeeping for classical harmonic mechanics, self-contained
against Mathlib only.

## i. Overview

This module develops the finite-system layer of classical mechanics around
harmonic force laws: conservation of oscillator energy along solutions of
Newton's equation plus the explicit cosine/sine solution, resultant-force /
2D-scalar-moment / discrete-work balances, finite spring networks with
stiffness matrices and mass-orthogonal normal modes, and continuum
bookkeeping (volume change, tension-positive traction, infinitesimal strain
with the engineering shear conversion).

Reuse-verified against Mathlib / ATLAS main: this module imports no next-50
prerequisite module.

The pinned Physlib 1D harmonic-oscillator file
(ClassicalMechanics/HarmonicOscillator/Basic.lean, R12) is the upstream
canonical 1D oscillator API; this module does not introduce a second
1D-oscillator data definition and instead proves the finite-system layer
that file does not cover.

Model boundary (fixed): Newtonian/continuum balance and harmonic force laws
are named model assumptions carried as explicit hypotheses; conservation and
explicit-solution results are proved within them. Constitutive laws (for
example Hooke's law) are NOT assumed anywhere in this module.

## ii. Key results

* `oscillatorEnergy_conserved`: energy is constant along oscillator
  solutions.
* `oscillator_explicit_solution`: the cosine/sine pair solves Newton's
  equation with constant energy `(1 / 2) * k * A ^ 2`.
* `sum_pairwise_antisymmetric_eq_zero`: action-reaction cancellation for
  real-valued pair forces.
* `moment2D_add`, `central_pair_moment_eq_zero`: 2D moment linearity and the
  single central-pair zero moment (no-body-couple model).
* `totalWork_add`: discrete work distributes over force families.
* `springEnergy_eq_quadForm`: spring energy equals `(1 / 2)` times the
  stiffness quadratic form; `springEnergy_nonneg`.
* `stiffnessMatrix_transpose`: the stiffness matrix is symmetric.
* `stiffnessMatrix_mulVec_one`, `stiffnessMatrix_free_zeroMode`,
  `springEnergy_free_const`: rigid translations are zero modes only in the
  free (`w = 0`) case; `stiffnessMatrix_fixedEnds_rowNonzero` for fixed ends.
* `innerProductM_eq_zero_of_ne`: distinct normal modes are mass-orthogonal.
* `rayleigh_nonneg`: Rayleigh quotient nonnegativity for spring stiffness.
* `det_volume_pos`, `det_composition`: volume-change bookkeeping.
* `traction_hydrostatic`, `traction_reciprocity`: tension-positive traction.
* `infStrain_symmetric`, `infStrain_diag`, `infStrain_offdiag`,
  `engShear_eq`: infinitesimal strain and the factor-of-2 engineering
  convention.

## iii. Table of contents

* A. Harmonic oscillator energy, conservation, and explicit solution.
* B. Resultant force, action-reaction, 2D moment, and discrete work.
* C. Finite spring networks, stiffness matrices, and normal modes.
* D. Continuum bookkeeping: volume, traction, and strain conversion.

## iv. References

* Pinned Physlib ClassicalMechanics/HarmonicOscillator/Basic.lean (R12):
  canonical 1D oscillator data, equation of motion, energy interface.
* MIT OCW 3.032 Mechanical Behavior of Materials, Fall 2007, syllabus
  (MAT-S04): chapter-level curriculum anchor for stress/strain and
  mechanical behaviour.
-/

@[expose] public section

open scoped Matrix
open scoped BigOperators

namespace PhyslibExt.Mechanics.HarmonicMechanics

/-! ## A. Harmonic oscillator energy, conservation, and explicit solution. -/

/-- Oscillator energy: kinetic plus harmonic potential energy. -/
noncomputable def oscillatorEnergy (m k x v : ℝ) : ℝ :=
  (1 / 2) * m * v ^ 2 + (1 / 2) * k * x ^ 2

/-- Energy conservation (MC): along any solution of Newton's equation in
divided form `v' = -(k / m) * x` with `x' = v` (MOD), the oscillator energy
has zero time derivative, hence is constant. -/
lemma oscillatorEnergy_conserved (m k : ℝ) (x v : ℝ → ℝ) (t : ℝ)
    (hm : m ≠ 0)
    (hx : ∀ t, HasDerivAt x (v t) t)
    (hv : ∀ t, HasDerivAt v (-(k / m) * x t) t) :
    HasDerivAt (fun t => oscillatorEnergy m k (x t) (v t)) 0 t := by
  unfold oscillatorEnergy
  have hv2 : HasDerivAt (v * v)
      ((-(k / m) * x t) * v t + v t * (-(k / m) * x t)) t :=
    (hv t).mul (hv t)
  have hx2 : HasDerivAt (x * x)
      (v t * x t + x t * v t) t :=
    (hx t).mul (hx t)
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
type: pair springs of stiffness `k i j` plus wall springs of stiffness `w i`
from node `i` to a fixed wall. `w = 0` is the free network; `w i > 0` is a
fixed end. The `1 / 4` on the pair sum counts each unordered pair once with
the physical spring energy `(1 / 2) * k * stretch ^ 2`: the ordered double
sum counts every pair twice, and each spring carries its own `1 / 2`. -/
noncomputable def springEnergy {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (w : ι → ℝ) (u : ι → ℝ) : ℝ :=
  (1 / 4) * (∑ i, ∑ j, k i j * (u j - u i) ^ 2) +
    (1 / 2) * (∑ i, w i * u i ^ 2)

/-- Stiffness matrix (DEF): diagonal `(∑ j, k i j) + w i`, off-diagonal
`-k i j`. Row `i` encodes force balance on node `i`. -/
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

/-- Rigid-translation zero mode (MC, free network only): with `w = 0` the
all-ones vector is in the kernel. Stiffness is positive definite only after
removing rigid translations; `K` itself is NOT claimed positive definite. -/
lemma stiffnessMatrix_free_zeroMode {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ι → ℝ) (hkii : ∀ i, k i i = 0) :
    stiffnessMatrix k 0 *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  rw [stiffnessMatrix_mulVec_one k 0 hkii]

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

/-- Mass-weighted inner product (DEF) for positive masses. -/
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
  have hij : ∀ a b, K a b = K b a := by
    intro a b
    have h := congrFun (congrFun hsymm a) b
    rw [Matrix.transpose_apply] at h
    exact h.symm
  have hsym_dot : dotProduct (K *ᵥ v) w =
      dotProduct v (K *ᵥ w) := by
    have hexpand : ∀ a b : ι → ℝ, dotProduct (K *ᵥ a) b =
        ∑ i, ∑ j, K i j * a j * b i := by
      intro a b
      simp only [dotProduct, Matrix.mulVec]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    rw [hexpand, dotProduct_comm, hexpand]
    have hsum0 : ∑ i, ∑ j, (K i j * v j * w i - K i j * w j * v i) = 0 := by
      have hF : (∑ p : ι × ι, (K p.1 p.2 * v p.2 * w p.1 -
          K p.1 p.2 * w p.2 * v p.1)) =
          ∑ i, ∑ j, (K i j * v j * w i - K i j * w j * v i) :=
        Fintype.sum_prod_type _
      rw [← hF]
      apply sum_pairwise_antisymmetric_eq_zero
      intro i j
      change K j i * v i * w j - K j i * w i * v j =
        -(K i j * v j * w i - K i j * w j * v i)
      rw [hij j i]
      ring
    have h1 : ∀ i, (∑ j, K i j * v j * w i) - (∑ j, K i j * w j * v i) =
        ∑ j, (K i j * v j * w i - K i j * w j * v i) :=
      fun i => (Finset.sum_sub_distrib _ _).symm
    have h2 : (∑ i, ∑ j, K i j * v j * w i) - (∑ i, ∑ j, K i j * w j * v i) =
        ∑ i, ((∑ j, K i j * v j * w i) - (∑ j, K i j * w j * v i)) :=
      (Finset.sum_sub_distrib _ _).symm
    have h3 : (∑ i, ((∑ j, K i j * v j * w i) - (∑ j, K i j * w j * v i))) =
        ∑ i, ∑ j, (K i j * v j * w i - K i j * w j * v i) :=
      Finset.sum_congr rfl (fun i _ => h1 i)
    have hdiff : (∑ i, ∑ j, K i j * v j * w i) -
        (∑ i, ∑ j, K i j * w j * v i) = 0 := by
      rw [h2, h3, hsum0]
    exact sub_eq_zero.mp hdiff
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

/-! ## D. Continuum bookkeeping: volume, traction, and strain conversion. -/

/-- Volume positivity (MC): with an orientation-preserving deformation
gradient (`F.det > 0`, the orientation hypothesis on the reference vs
current configuration), any positive reference volume element stays
positive. -/
lemma det_volume_pos {F : Matrix (Fin 3) (Fin 3) ℝ} {V0 : ℝ}
    (hJ : 0 < F.det) (hV : 0 < V0) :
    0 < F.det * V0 :=
  mul_pos hJ hV

/-- Volume-change rule (MC): the determinant of a composition of deformation
gradients is the product of the determinants. -/
lemma det_composition {F G : Matrix (Fin 3) (Fin 3) ℝ} :
    (F * G).det = F.det * G.det :=
  Matrix.det_mul F G

/-- Cauchy traction (DEF): the traction on a plane with normal `n` is
`σ *ᵥ n`, under the tension-positive sign convention. -/
noncomputable def traction (σ : Matrix (Fin 3) (Fin 3) ℝ)
    (n : Fin 3 → ℝ) : Fin 3 → ℝ :=
  σ *ᵥ n

/-- Hydrostatic tension (MC): under a tensile stress `σ = s • I` with
`s > 0`, the traction on any normal `n` is `s • n` (outward traction on an
outward normal). The positivity hypothesis records the tension-positive
convention. -/
lemma traction_hydrostatic {s : ℝ} (_hs : 0 < s) (n : Fin 3 → ℝ) :
    traction (s • (1 : Matrix (Fin 3) (Fin 3) ℝ)) n = s • n := by
  unfold traction
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Traction reciprocity (MC, opposite face): flipping the normal flips the
traction. -/
lemma traction_reciprocity (σ : Matrix (Fin 3) (Fin 3) ℝ) (n : Fin 3 → ℝ) :
    traction σ (-n) = -traction σ n := by
  unfold traction
  exact Matrix.mulVec_neg _ _

/-- Infinitesimal strain (DEF): the symmetric part of the displacement
gradient. Only infinitesimal strain is defined; there is no finite strain or
geometric nonlinearity in this module. -/
noncomputable def infStrain (H : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 2 : ℝ) • (H + Hᵀ)

/-- Infinitesimal strain is symmetric (MC). -/
lemma infStrain_symmetric (H : Matrix (Fin 3) (Fin 3) ℝ) :
    (infStrain H)ᵀ = infStrain H := by
  apply Matrix.ext
  intro i j
  simp only [infStrain, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.add_apply, smul_eq_mul]
  ring

/-- Diagonal entries of infinitesimal strain agree with `H` (MC). -/
lemma infStrain_diag (H : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    infStrain H i i = H i i := by
  simp only [infStrain, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul]
  ring

/-- Off-diagonal entries of infinitesimal strain (MC): the symmetrized
average. The `i ≠ j` hypothesis is carried though the formula is uniform. -/
lemma infStrain_offdiag (H : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3)
    (_h : i ≠ j) :
    infStrain H i j = (H i j + H j i) / 2 := by
  simp only [infStrain, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul]
  ring

/-- Engineering shear strain (DEF): twice the tensor shear, defined only
off-diagonal (factor-of-2 Voigt/engineering convention). The diagonal is not
used. -/
noncomputable def engShear (H : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    ℝ :=
  2 * infStrain H i j

/-- Engineering vs tensor shear conversion (MC): off-diagonal, engineering
shear is the sum of the displacement-gradient cross terms. -/
lemma engShear_eq (H : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) (h : i ≠ j) :
    engShear H i j = H i j + H j i := by
  unfold engShear
  rw [infStrain_offdiag H i j h]
  ring

end PhyslibExt.Mechanics.HarmonicMechanics
