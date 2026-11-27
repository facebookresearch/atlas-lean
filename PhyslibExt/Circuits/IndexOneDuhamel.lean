/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import MathlibExt.Analysis.ODE.Duhamel
public import PhyslibExt.Circuits.IndexOneElimination

import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Existence and uniqueness for an index-one linear descriptor system

## i. Overview

Let `A`, `B`, `C` and `D` be constant real matrices of compatible
shapes on finite index types, with `D` invertible, and let `f` and
`g` be continuous time-dependent forcing vectors. For the descriptor
system `x' = A x + B y + f t`, `0 = C x + D y + g t`, eliminating the
algebraic vector `y` gives the constant-coefficient reduced equation
`x' = (A - B D⁻¹ C) x + (f t - B D⁻¹ g t)` on the state space
`n → ℝ`, a finite-dimensional real Banach space. Duhamel's
variation-of-constants formula gives a unique global solution of the
reduced equation through any initial state `x₀` at any initial time
`t₀`, and the reconstruction `y t = -D⁻¹ (C x t + g t)` is continuous.

For an initial pair `(x₀, y₀)` that is consistent at `t₀`, meaning
`C x₀ + D y₀ + g t₀ = 0`, the descriptor system therefore has a
global solution through `(x₀, y₀)`, its state is given by the
operator-exponential formula, and every solution whose state passes
through `x₀` at `t₀` coincides with it. An inconsistent initial pair
is reached by no solution, whatever `D`. Only continuity of the
algebraic component is asserted: a continuous but nondifferentiable
algebraic forcing produces a nondifferentiable algebraic component.

The proof applies the index-one reduction of
`PhyslibExt.Circuits.IndexOneElimination` in both directions: a
Duhamel solution of the reduced equation, paired with its
reconstruction, satisfies the descriptor system, and any descriptor
solution satisfies the reduced equation, so Duhamel uniqueness fixes
its state and the reconstruction fixes its algebraic component.

## ii. Key results

- `reducedState_existsUnique`: the reduced state equation has a
  unique global solution through `x₀` at `t₀`, given by the
  variation-of-constants formula.
- `descriptor_existsUnique_of_consistentPair`: a consistent initial
  pair determines a unique global descriptor solution, with explicit
  state and continuous algebraic component.
- `not_exists_solution_of_not_consistentPair`: an inconsistent
  initial pair is reached by no solution.
- `exists_solution_algebraic_not_differentiableAt`: the algebraic
  component of a solution need not be differentiable.

## iii. Table of contents

- A. Reduced operator and forcing
- B. Reduced state equation
- C. Algebraic component
- D. Descriptor existence and uniqueness
- E. Validation boundaries

## iv. References

- P. Kunkel and V. Mehrmann, *Differential-Algebraic Equations:
  Analysis and Numerical Solution*, EMS Textbooks in Mathematics,
  European Mathematical Society, 2006: linear descriptor systems with
  constant coefficients, consistent initial values, and index-one
  reduction to an ordinary differential equation.
- G. Teschl, *Ordinary Differential Equations and Dynamical Systems*,
  Graduate Studies in Mathematics 140, American Mathematical Society,
  2012, Section 3.2: the variation-of-constants formula for linear
  systems with constant coefficients.

## A. Reduced operator and forcing
-/

@[expose] public section

open MeasureTheory Matrix MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv
open PhyslibExt.Circuits.IndexOneElimination

namespace PhyslibExt.Circuits.IndexOneDuhamel

/-- The Schur-reduced coefficient matrix `A - B D⁻¹ C` as a bounded
linear operator on the finite-dimensional state space `n → ℝ`. -/
noncomputable def reducedOperator {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    [DecidableEq m] (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ)
    (D : Matrix m m ℝ) [Invertible D] : (n → ℝ) →L[ℝ] (n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (schur A B C D))

/-- The reduced operator acts by multiplication with the Schur
complement. -/
lemma reducedOperator_apply {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    [DecidableEq m] (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ)
    (D : Matrix m m ℝ) [Invertible D] (v : n → ℝ) :
    reducedOperator A B C D v = schur A B C D *ᵥ v := by
  simp [reducedOperator, Matrix.toLin'_apply]

/-- The reduced forcing path `s ↦ f s - B D⁻¹ g s`. -/
noncomputable def reducedForcingPath {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) (D : Matrix m m ℝ) [Invertible D] (f : ℝ → n → ℝ)
    (g : ℝ → m → ℝ) : ℝ → n → ℝ :=
  fun s => reducedForcing B D (f s) (g s)

/-- Continuous forcing gives a continuous reduced forcing path. -/
lemma continuous_reducedForcingPath {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (B : Matrix n m ℝ) (D : Matrix m m ℝ) [Invertible D] (f : ℝ → n → ℝ)
    (g : ℝ → m → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (reducedForcingPath B D f g) := by
  unfold reducedForcingPath reducedForcing
  exact hf.sub (continuous_const.matrix_mulVec (continuous_const.matrix_mulVec hg))

/-! ### B. Reduced state equation -/

/-- **Reduced state.** The reduced state equation
`x' = (A - B D⁻¹ C) x + (f t - B D⁻¹ g t)` has a unique global
solution through `x₀` at time `t₀`, given by the
variation-of-constants formula with the operator exponential of the
reduced operator. -/
theorem reducedState_existsUnique {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    [DecidableEq m] (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ)
    (D : Matrix m m ℝ) [Invertible D] (f : ℝ → n → ℝ) (g : ℝ → m → ℝ)
    (hf : Continuous f) (hg : Continuous g) (t₀ : ℝ) (x₀ : n → ℝ) :
    ∃ x : ℝ → n → ℝ, x t₀ = x₀ ∧
      (∀ t, x t = (NormedSpace.exp ((t - t₀) • reducedOperator A B C D)) x₀ +
        ∫ s in t₀..t, (NormedSpace.exp ((t - s) • reducedOperator A B C D))
          (reducedForcingPath B D f g s)) ∧
      (∀ t, HasDerivAt x (schur A B C D *ᵥ x t + reducedForcingPath B D f g t) t) ∧
      ∀ x' : ℝ → n → ℝ, x' t₀ = x₀ →
        (∀ t, HasDerivAt x' (schur A B C D *ᵥ x' t + reducedForcingPath B D f g t) t) →
        x' = x := by
  obtain ⟨x, hx0, hformula, hderiv, huniq⟩ :=
    MathlibExt.Analysis.ODE.DuhamelWanted.duhamel_variation_of_constants
      (reducedOperator A B C D) (reducedForcingPath B D f g) t₀ x₀
      (continuous_reducedForcingPath B D f g hf hg)
  refine ⟨x, hx0, hformula, ?_, ?_⟩
  · intro t
    have h := hderiv t
    rwa [reducedOperator_apply] at h
  · intro x' hx0' hderiv'
    apply huniq x' hx0'
    intro t
    have h := hderiv' t
    rwa [reducedOperator_apply]

/-! ### C. Algebraic component -/

/-- The algebraic component reconstructed from a continuous state
under continuous algebraic forcing is continuous. -/
lemma continuous_algebraicReconstruction {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq m] (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D]
    (x : ℝ → n → ℝ) (g : ℝ → m → ℝ) (hx : Continuous x) (hg : Continuous g) :
    Continuous (fun t => algebraicReconstruction D C (x t) (g t)) := by
  unfold algebraicReconstruction
  exact (continuous_const.matrix_mulVec
    ((continuous_const.matrix_mulVec hx).add hg)).neg

/-! ### D. Descriptor existence and uniqueness -/

/-- **Existence and uniqueness for a consistent initial pair.** With
invertible `D`, continuous forcing and an initial pair `(x₀, y₀)`
consistent at time `t₀`, the descriptor system has a global solution
`(x, y)` through `(x₀, y₀)`: `x` is the variation-of-constants
solution of the reduced equation, `y` is its continuous
reconstruction, and every solution whose state passes through `x₀` at
`t₀` equals `(x, y)`. -/
theorem descriptor_existsUnique_of_consistentPair {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (A : Matrix n n ℝ) (B : Matrix n m ℝ)
    (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D] (f : ℝ → n → ℝ)
    (g : ℝ → m → ℝ) (hf : Continuous f) (hg : Continuous g) (t₀ : ℝ) (x₀ : n → ℝ)
    (y₀ : m → ℝ) (hcons : consistentPair C D (g t₀) x₀ y₀) :
    ∃ x : ℝ → n → ℝ, ∃ y : ℝ → m → ℝ,
      satisfiesDescriptorSystem A B C D f g x y ∧ x t₀ = x₀ ∧ y t₀ = y₀ ∧
      Continuous y ∧
      (∀ t, x t = (NormedSpace.exp ((t - t₀) • reducedOperator A B C D)) x₀ +
        ∫ s in t₀..t, (NormedSpace.exp ((t - s) • reducedOperator A B C D))
          (reducedForcingPath B D f g s)) ∧
      (∀ t, y t = algebraicReconstruction D C (x t) (g t)) ∧
      ∀ x' : ℝ → n → ℝ, ∀ y' : ℝ → m → ℝ,
        satisfiesDescriptorSystem A B C D f g x' y' → x' t₀ = x₀ → x' = x ∧ y' = y := by
  obtain ⟨x, hx0, hformula, hderiv, huniq⟩ :=
    reducedState_existsUnique A B C D f g hf hg t₀ x₀
  have hdiff : Differentiable ℝ x := fun t => (hderiv t).differentiableAt
  set y : ℝ → m → ℝ := fun t => algebraicReconstruction D C (x t) (g t) with hy
  have hycont : Continuous y :=
    continuous_algebraicReconstruction C D x g hdiff.continuous hg
  have hy0 : y t₀ = y₀ := by
    have h := (consistentPair_iff_eq_algebraicReconstruction C D (g t₀) x₀ y₀).mp hcons
    change algebraicReconstruction D C (x t₀) (g t₀) = y₀
    rw [hx0]
    exact h.symm
  have hred : satisfiesReducedSystem A B C D f g x y :=
    ⟨hdiff, fun t => (hderiv t).deriv, fun _ => rfl⟩
  have hsat : satisfiesDescriptorSystem A B C D f g x y :=
    (satisfiesDescriptorSystem_iff_satisfiesReducedSystem A B C D f g x y).mpr hred
  refine ⟨x, y, hsat, hx0, hy0, hycont, hformula, fun _ => rfl, ?_⟩
  intro x' y' hsat' hx0'
  obtain ⟨hdiff', hderivEq, hrecon⟩ :=
    (satisfiesDescriptorSystem_iff_satisfiesReducedSystem A B C D f g x' y').mp hsat'
  have hx'eq : x' = x := by
    apply huniq x' hx0'
    intro t
    have hda : HasDerivAt x' (deriv x' t) t := (hdiff' t).hasDerivAt
    rwa [hderivEq t] at hda
  refine ⟨hx'eq, ?_⟩
  have hrw : y' = fun t => algebraicReconstruction D C (x' t) (g t) := funext hrecon
  rw [hrw, hx'eq]

/-! ### E. Validation boundaries -/

/-- **Consistency is necessary.** An initial pair that is not
consistent at time `t₀` is reached by no solution of the descriptor
system; no invertibility of `D` is needed. -/
lemma not_exists_solution_of_not_consistentPair {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ)
    (f : ℝ → n → ℝ) (g : ℝ → m → ℝ) (t₀ : ℝ) (x₀ : n → ℝ) (y₀ : m → ℝ)
    (hcons : ¬ consistentPair C D (g t₀) x₀ y₀) :
    ¬ ∃ x : ℝ → n → ℝ, ∃ y : ℝ → m → ℝ,
      satisfiesDescriptorSystem A B C D f g x y ∧ x t₀ = x₀ ∧ y t₀ = y₀ := by
  rintro ⟨x, y, hsat, hx0, hy0⟩
  have h := consistentPair_of_satisfiesDescriptorSystem A B C D f g x y hsat t₀
  rw [hx0, hy0] at h
  exact hcons h

/-- **The algebraic component need not be differentiable.** For the
scalar system `x' = 0`, `0 = y + |t|`, a solution exists and its
algebraic component is not differentiable at `0`. -/
lemma exists_solution_algebraic_not_differentiableAt :
    ∃ x : ℝ → Fin 1 → ℝ, ∃ y : ℝ → Fin 1 → ℝ,
      satisfiesDescriptorSystem (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 1
        (fun _ _ => 0) (fun t _ => |t|) x y ∧
      ¬ DifferentiableAt ℝ y 0 := by
  refine ⟨(fun _ _ => 0), (fun t _ => -|t|), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun t => (hasDerivAt_const t _).differentiableAt
  · intro t
    have h : deriv (fun _ : ℝ => (0 : Fin 1 → ℝ)) t =
        (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (0 : Fin 1 → ℝ) +
        (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (fun _ => -|t|) + (0 : Fin 1 → ℝ) := by
      simp [deriv_const, Matrix.zero_mulVec]
    exact h
  · intro t
    simp only [Matrix.zero_mulVec, Matrix.one_mulVec, zero_add]
    funext i
    simp
  · intro hdiff
    have h0 : DifferentiableAt ℝ (fun t : ℝ => -|t|) 0 :=
      (differentiableAt_pi.mp hdiff) 0
    have hneg := h0.neg
    have heq : (-(fun t : ℝ => -|t|)) = (fun t : ℝ => |t|) := by
      funext t
      simp
    rw [heq] at hneg
    exact not_differentiableAt_abs_zero hneg

end PhyslibExt.Circuits.IndexOneDuhamel
