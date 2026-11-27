/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.MetricSpace.Lipschitz
public import PhyslibExt.Circuits.IndexOneDuhamel

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.LinearCombination
import MathlibExt.Analysis.ODE.ExplicitEuler
import MathlibExt.Analysis.ODE.OneStepStability

/-!
# Explicit Euler error for an index-one linear descriptor system

## i. Overview

Let `A`, `B`, `C` and `D` be constant real matrices of compatible shapes on finite index types,
with `D` invertible, and let the forcing vectors `f` and `g` be `C²` in time. On a finite horizon
`[t₀, T]` with `t₀ < T`, consider the descriptor system `x' = A x + B y + f t`,
`0 = C x + D y + g t` with an initial pair `(x₀, y₀)` that is consistent at `t₀`, meaning
`C x₀ + D y₀ + g t₀ = 0`. Eliminating `y` gives the reduced equation
`x' = (A - B D⁻¹ C) x + (f t - B D⁻¹ g t)`, whose right-hand side is `C²` and globally Lipschitz
in the state with constant `L`, the operator norm of `A - B D⁻¹ C`.

Explicit Euler is applied to the reduced equation, `X (k + 1) = X k + h F (t₀ + k h) (X k)`, from
an arbitrary starting value `X 0`, and the algebraic vector is reconstructed from `X k` at the same
time sample, `Y k = -D⁻¹ (C X k + g (t₀ + k h))`. Then there is a constant `K ≥ 0`, independent of
the step `h`, of `X 0` and of the solution, such that for every step `h ∈ (0, T - t₀]` and every
`k` with `k h ≤ T - t₀`,

  `‖X k - x (t₀ + k h)‖ ≤ exp (L (T - t₀)) ‖X 0 - x₀‖ + K h`,

and the reconstructed algebraic error is at most `‖D⁻¹ C‖` times the same bound. The initial
mismatch `X 0 - x₀` enters through the factor `exp (L (T - t₀))`; the `O(h)` part comes from the
first-order convergence of explicit Euler for a `C²` right-hand side. Norms are the sup norms of
`n → ℝ` and `m → ℝ` in the given coordinates, so state and time scales are fixed by the choice of
coordinates: a positive diagonal rescaling is another instance of the same theorem, with its own
`L`, `‖D⁻¹ C‖` and `K`.

The proof feeds the reduced field to
`MathlibExt.Analysis.ODE.ExplicitEulerWanted.explicit_euler_first_order_convergence`, which also
supplies a solution on the horizon. Uniqueness of solutions of Lipschitz equations identifies every
horizon solution through `x₀` with that one, the one-step stability estimate
`MathlibExt.Analysis.ODE.OneStepMethod.norm_sub_le_of_lipschitzWith` propagates the initial
mismatch, and the reconstruction map, affine with linear part `-D⁻¹ C`, transfers the state bound
to the algebraic component. Existence on the horizon only needs continuous forcing: it restricts
the global solution of
`PhyslibExt.Circuits.IndexOneDuhamel.descriptor_existsUnique_of_consistentPair`.

## ii. Key results

- `solvesDescriptorOn_iff`: on the horizon, a pair solves the descriptor system exactly when its
  state solves the reduced equation and its algebraic component is the reconstruction.
- `exists_solvesDescriptorOn`: with continuous forcing, a consistent initial pair is reached by a
  solution on every horizon.
- `norm_sub_le_of_isReducedEulerSequence`: Euler sequences of the reduced field separate at most by
  the factor `exp (L k h)`.
- `indexOneEuler_error`: existence on the horizon, and the state and reconstructed algebraic error
  bounds of explicit Euler, including the initial error.
- `scalarEuler_twoStepSizes`, `not_forall_le_of_not_consistentPair`: a scalar fixture with two step
  sizes and a nonzero initial mismatch, and an inconsistent algebraic value that inherits no `O(h)`
  bound.

## iii. Table of contents

- A. Reduced field, constants, horizon solutions and Euler iterates
- B. Provider hypotheses and the reduction on the horizon
- C. Error propagation and the error bound
- D. Validation

## iv. References

- E. Hairer, S. P. Nørsett and G. Wanner, *Solving Ordinary Differential Equations I: Nonstiff
  Problems*, 2nd ed., Springer Series in Computational Mathematics 8, Springer, 1993,
  Section I.7: convergence of Euler polygons with an error bound of the form
  `exp (L (T - t₀))` times the initial error plus a term of order `h`.
- E. Hairer and G. Wanner, *Solving Ordinary Differential Equations II: Stiff and
  Differential-Algebraic Problems*, 2nd ed., Springer Series in Computational Mathematics 14,
  Springer, 1996, Section VI.1: index-one problems solved through the reduced (state space) form.
- P. Kunkel and V. Mehrmann, *Differential-Algebraic Equations: Analysis and Numerical Solution*,
  EMS Textbooks in Mathematics, European Mathematical Society, 2006: consistent initial values and
  index-one reduction of linear descriptor systems with constant coefficients.

## A. Reduced field, constants, horizon solutions and Euler iterates
-/

@[expose] public section

open Matrix MathlibExt.LinearAlgebra.Matrix.BlockSolutionEquiv
open PhyslibExt.Circuits.IndexOneElimination PhyslibExt.Circuits.IndexOneDuhamel

namespace PhyslibExt.Circuits.IndexOneEulerBridge

/-- The reduced vector field of the index-one system,
`(t, v) ↦ (A - B D⁻¹ C) v + (f t - B D⁻¹ g t)`. -/
noncomputable def reducedField {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D]
    (f : ℝ → n → ℝ) (g : ℝ → m → ℝ) : ℝ → (n → ℝ) → (n → ℝ) :=
  fun t v => schur A B C D *ᵥ v + reducedForcingPath B D f g t

/-- The Lipschitz constant of the reduced field in the state: the operator norm of the reduced
operator on `n → ℝ` with its sup norm. -/
noncomputable def reducedLipschitzConstant {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ)
    (D : Matrix m m ℝ) [Invertible D] : NNReal :=
  ‖reducedOperator A B C D‖₊

/-- The reconstruction gain `‖D⁻¹ * C‖`: the operator norm of `v ↦ (D⁻¹ * C) *ᵥ v` from the
state space `n → ℝ` to the algebraic space `m → ℝ`, both with their sup norms. -/
noncomputable def reconstructionGain {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    [DecidableEq m] (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D] : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toLin' (D⁻¹ * C))‖

/-- A trajectory pair solves the descriptor system on the horizon `[t₀, T]`: at every time of the
horizon, `x` has derivative `A x + B y + f t` and the algebraic equation holds. No regularity is
required of `y`. -/
def SolvesDescriptorOn {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ)
    (f : ℝ → n → ℝ) (g : ℝ → m → ℝ) (t₀ T : ℝ) (x : ℝ → n → ℝ) (y : ℝ → m → ℝ) : Prop :=
  ∀ t ∈ Set.Icc t₀ T,
    HasDerivAt x (A *ᵥ x t + B *ᵥ y t + f t) t ∧ C *ᵥ x t + D *ᵥ y t + g t = 0

/-- `X` is an explicit-Euler sequence for the reduced field with step `h` from time `t₀`, in the
exact recursion form of the explicit-Euler provider. The initial value `X 0` is free, so an
initial mismatch is allowed. -/
def IsReducedEulerSequence {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D]
    (f : ℝ → n → ℝ) (g : ℝ → m → ℝ) (t₀ h : ℝ) (X : ℕ → n → ℝ) : Prop :=
  ∀ k : ℕ, X (k + 1) = X k + h • reducedField A B C D f g (t₀ + (k : ℝ) * h) (X k)

/-- The algebraic iterates reconstructed from the Euler state iterates at the same time samples
`t₀ + k h`. -/
noncomputable def reconstructedAlgebraic {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D] (g : ℝ → m → ℝ) (t₀ h : ℝ)
    (X : ℕ → n → ℝ) : ℕ → m → ℝ :=
  fun k => algebraicReconstruction D C (X k) (g (t₀ + (k : ℝ) * h))

/-! ### B. Provider hypotheses and the reduction on the horizon -/

private lemma contDiff_reducedForcingPath {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq m] (B : Matrix n m ℝ) (D : Matrix m m ℝ) [Invertible D]
    (f : ℝ → n → ℝ) (g : ℝ → m → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (reducedForcingPath B D f g) := by
  have hopB : ∀ v : m → ℝ, (LinearMap.toContinuousLinearMap (Matrix.toLin' B)) v
      = B *ᵥ v := fun v => by simp [Matrix.toLin'_apply]
  have hopD : ∀ v : m → ℝ, (LinearMap.toContinuousLinearMap (Matrix.toLin' D⁻¹)) v
      = D⁻¹ *ᵥ v := fun v => by simp [Matrix.toLin'_apply]
  have hfun : reducedForcingPath B D f g = fun s =>
      f s - (LinearMap.toContinuousLinearMap (Matrix.toLin' B))
        ((LinearMap.toContinuousLinearMap (Matrix.toLin' D⁻¹)) (g s)) := by
    ext s
    simp [reducedForcingPath, reducedForcing, hopB, hopD]
  rw [hfun]
  exact hf.sub ((LinearMap.toContinuousLinearMap (Matrix.toLin' B)).contDiff.comp
    ((LinearMap.toContinuousLinearMap (Matrix.toLin' D⁻¹)).contDiff.comp hg))

/-- **C² hypothesis of the provider.** `C²` forcing gives a `C²` reduced field. -/
lemma contDiff_reducedField {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D]
    (f : ℝ → n → ℝ) (g : ℝ → m → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (Function.uncurry (reducedField A B C D f g)) := by
  have hop : ∀ v : n → ℝ, (schur A B C D).mulVecLin.toContinuousLinearMap v
      = schur A B C D *ᵥ v := fun v => by simp
  have hfun : Function.uncurry (reducedField A B C D f g) =
      fun p : ℝ × (n → ℝ) => (schur A B C D).mulVecLin.toContinuousLinearMap p.2
        + reducedForcingPath B D f g p.1 := by
    apply funext
    intro ⟨t, v⟩
    change reducedField A B C D f g t v = _
    unfold reducedField
    rw [hop]
  rw [hfun]
  exact ((schur A B C D).mulVecLin.toContinuousLinearMap.contDiff.comp contDiff_snd).add
    ((contDiff_reducedForcingPath B D f g hf hg).comp contDiff_fst)

/-- **Lipschitz hypothesis of the provider.** At every time the reduced field is Lipschitz in
the state with constant `reducedLipschitzConstant`. -/
lemma lipschitzWith_reducedField {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    [DecidableEq m] (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ)
    [Invertible D] (f : ℝ → n → ℝ) (g : ℝ → m → ℝ) (t : ℝ) :
    LipschitzWith (reducedLipschitzConstant A B C D) (reducedField A B C D f g t) := by
  have hfield : reducedField A B C D f g t =
      fun v => reducedOperator A B C D v + reducedForcingPath B D f g t := by
    ext v
    simp [reducedField, reducedOperator_apply]
  rw [hfield]
  unfold reducedLipschitzConstant
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (reducedOperator A B C D).lipschitzWith.dist_le_mul x y
  rw [dist_eq_norm] at h
  rw [dist_eq_norm, add_sub_add_right_eq_sub]
  exact h

/-- Pointwise index-one elimination: with `y` the algebraic reconstruction, the right-hand side of
the differential equation is the reduced field. -/
private lemma descriptorRHS_eq_reducedField {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq m] (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ)
    [Invertible D] (f : ℝ → n → ℝ) (g : ℝ → m → ℝ) (t : ℝ) (x : n → ℝ) (y : m → ℝ)
    (hy : y = algebraicReconstruction D C x (g t)) :
    A *ᵥ x + B *ᵥ y + f t = reducedField A B C D f g t x := by
  rw [hy]
  simp only [reducedField, reducedForcingPath, algebraicReconstruction, schur, reducedForcing,
    Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_neg, Matrix.mulVec_add,
    Matrix.mul_assoc]
  abel

/-- **Index-one reduction on the horizon.** With invertible `D`, a pair solves the descriptor
system on `[t₀, T]` exactly when `x` solves the reduced equation there and `y` is the algebraic
reconstruction at every time of the horizon. -/
theorem solvesDescriptorOn_iff {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D]
    (f : ℝ → n → ℝ) (g : ℝ → m → ℝ) (t₀ T : ℝ) (x : ℝ → n → ℝ) (y : ℝ → m → ℝ) :
    SolvesDescriptorOn A B C D f g t₀ T x y ↔
      (∀ t ∈ Set.Icc t₀ T, HasDerivAt x (reducedField A B C D f g t (x t)) t) ∧
        ∀ t ∈ Set.Icc t₀ T, y t = algebraicReconstruction D C (x t) (g t) := by
  constructor
  · intro h
    constructor
    · intro t ht
      obtain ⟨hderiv, halg⟩ := h t ht
      have hy : y t = algebraicReconstruction D C (x t) (g t) :=
        eq_algebraicReconstruction_of_algebraicEquation C D _ _ _ halg
      have heq : A *ᵥ x t + B *ᵥ y t + f t = reducedField A B C D f g t (x t) :=
        descriptorRHS_eq_reducedField A B C D f g t _ _ hy
      rwa [heq] at hderiv
    · intro t ht
      obtain ⟨_, halg⟩ := h t ht
      exact eq_algebraicReconstruction_of_algebraicEquation C D _ _ _ halg
  · intro h t ht
    obtain ⟨hxred, hyrec⟩ := h
    have hy : y t = algebraicReconstruction D C (x t) (g t) := hyrec t ht
    have hx : HasDerivAt x (reducedField A B C D f g t (x t)) t := hxred t ht
    have heq : A *ᵥ x t + B *ᵥ y t + f t = reducedField A B C D f g t (x t) :=
      descriptorRHS_eq_reducedField A B C D f g t _ _ hy
    have halg : C *ᵥ x t + D *ᵥ y t + g t = 0 :=
      algebraicEquation_of_eq_algebraicReconstruction C D _ _ _ hy
    rw [← heq] at hx
    exact ⟨hx, halg⟩

/-- **Existence on the horizon.** With continuous forcing and a consistent initial pair, the
descriptor system has a solution on `[t₀, T]` through `(x₀, y₀)`, for every horizon: the global
solution of `PhyslibExt.Circuits.IndexOneDuhamel.descriptor_existsUnique_of_consistentPair`
restricted to it. -/
theorem exists_solvesDescriptorOn {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D]
    (f : ℝ → n → ℝ) (g : ℝ → m → ℝ) (hf : Continuous f) (hg : Continuous g) (t₀ T : ℝ)
    (x₀ : n → ℝ) (y₀ : m → ℝ) (hcons : consistentPair C D (g t₀) x₀ y₀) :
    ∃ x : ℝ → n → ℝ, ∃ y : ℝ → m → ℝ,
      x t₀ = x₀ ∧ y t₀ = y₀ ∧ SolvesDescriptorOn A B C D f g t₀ T x y := by
  classical
  obtain ⟨x, y, ⟨hd, hde, halg⟩, hx0, hy0, -⟩ :=
    descriptor_existsUnique_of_consistentPair A B C D f g hf hg t₀ x₀ y₀ hcons
  exact ⟨x, y, hx0, hy0, fun t _ => ⟨hde t ▸ (hd t).hasDerivAt, halg t⟩⟩

/-! ### C. Error propagation and the error bound -/

/-- **Initial-error propagation.** Two reduced Euler sequences with the same nonnegative step
differ, after `k` steps, by at most `exp (L k h)` times their initial difference, where `L` is
the reduced Lipschitz constant. This is the one-step stability estimate
`MathlibExt.Analysis.ODE.OneStepMethod.norm_sub_le_of_lipschitzWith` on the grid `t₀ + j h`, with
no perturbation. -/
lemma norm_sub_le_of_isReducedEulerSequence {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ)
    (D : Matrix m m ℝ) [Invertible D] (f : ℝ → n → ℝ) (g : ℝ → m → ℝ) (t₀ h : ℝ) (hh : 0 ≤ h)
    (X X' : ℕ → n → ℝ) (hX : IsReducedEulerSequence A B C D f g t₀ h X)
    (hX' : IsReducedEulerSequence A B C D f g t₀ h X') (k : ℕ) :
    ‖X k - X' k‖ ≤
      Real.exp ((reducedLipschitzConstant A B C D : ℝ) * ((k : ℝ) * h)) * ‖X 0 - X' 0‖ := by
  have hstep : ∀ j : ℕ, (t₀ + ((j + 1 : ℕ) : ℝ) * h) - (t₀ + (j : ℝ) * h) = h := fun j => by
    push_cast
    ring
  have key := MathlibExt.Analysis.ODE.OneStepMethod.norm_sub_le_of_lipschitzWith
    (Φ := fun s v _ => reducedField A B C D f g s v) (t := fun j : ℕ => t₀ + (j : ℝ) * h)
    (δ := 0) (J := k) (fun j _ => by linarith [hstep j])
    (fun j _ => lipschitzWith_reducedField A B C D f g _)
    (fun j _ => by simpa only [hstep j] using hX j)
    (fun j _ => by simpa only [hstep j, Pi.zero_apply, add_zero] using hX' j) k le_rfl
  simpa using key

/-- **Reconstruction error at a common time sample.** Reconstructing two states with the same
algebraic forcing value gives algebraic values at distance at most `‖D⁻¹ * C‖` times the state
distance. -/
lemma norm_algebraicReconstruction_sub_le {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D]
    (u w : n → ℝ) (g₀ : m → ℝ) :
    ‖algebraicReconstruction D C u g₀ - algebraicReconstruction D C w g₀‖ ≤
      reconstructionGain C D * ‖u - w‖ := by
  have hop : ∀ v : n → ℝ, (LinearMap.toContinuousLinearMap (Matrix.toLin' (D⁻¹ * C))) v
      = (D⁻¹ * C) *ᵥ v := fun v => by simp [Matrix.toLin'_apply]
  have hdiff : algebraicReconstruction D C u g₀ - algebraicReconstruction D C w g₀ =
      -((LinearMap.toContinuousLinearMap (Matrix.toLin' (D⁻¹ * C))) (u - w)) := by
    unfold algebraicReconstruction
    simp only [sub_neg_eq_add, Matrix.mulVec_add, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec,
      hop]
    abel
  rw [hdiff, norm_neg]
  unfold reconstructionGain
  exact (LinearMap.toContinuousLinearMap (Matrix.toLin' (D⁻¹ * C))).le_opNorm _

/-- **Explicit Euler for the index-one system (headline).** Let `D` be invertible, the forcing
`f, g` be `C²`, `t₀ < T`, and `(x₀, y₀)` be consistent at `t₀`. Then (1) the descriptor system has
a solution on `[t₀, T]` through `(x₀, y₀)`; and (2) there is a constant `K ≥ 0` such that, for
every solution `(x, y)` on `[t₀, T]` with `x t₀ = x₀`, every step `h ∈ (0, T - t₀]`, every
explicit-Euler sequence `X` of the reduced field with step `h` (any initial value `X 0`) and every
`k` with `k h ≤ T - t₀`, the state error at `t₀ + k h` is at most
`exp (L (T - t₀)) ‖X 0 - x₀‖ + K h`, and the error of the algebraic value reconstructed at the
same time sample is at most `‖D⁻¹ * C‖` times that bound. -/
theorem indexOneEuler_error {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    [DecidableEq m] (A : Matrix n n ℝ) (B : Matrix n m ℝ) (C : Matrix m n ℝ) (D : Matrix m m ℝ)
    [Invertible D] (f : ℝ → n → ℝ) (g : ℝ → m → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (t₀ T : ℝ) (hT : t₀ < T) (x₀ : n → ℝ) (y₀ : m → ℝ)
    (hcons : consistentPair C D (g t₀) x₀ y₀) :
    (∃ x : ℝ → n → ℝ, ∃ y : ℝ → m → ℝ,
        x t₀ = x₀ ∧ y t₀ = y₀ ∧ SolvesDescriptorOn A B C D f g t₀ T x y) ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ (x : ℝ → n → ℝ) (y : ℝ → m → ℝ), x t₀ = x₀ →
          SolvesDescriptorOn A B C D f g t₀ T x y →
          ∀ h ∈ Set.Ioc 0 (T - t₀), ∀ X : ℕ → n → ℝ,
            IsReducedEulerSequence A B C D f g t₀ h X →
            ∀ k : ℕ, (k : ℝ) * h ≤ T - t₀ →
              ‖X k - x (t₀ + (k : ℝ) * h)‖ ≤
                  Real.exp ((reducedLipschitzConstant A B C D : ℝ) * (T - t₀)) *
                    ‖X 0 - x₀‖ + K * h ∧
                ‖reconstructedAlgebraic C D g t₀ h X k - y (t₀ + (k : ℝ) * h)‖ ≤
                  reconstructionGain C D *
                    (Real.exp ((reducedLipschitzConstant A B C D : ℝ) * (T - t₀)) *
                      ‖X 0 - x₀‖ + K * h) := by
  have hexists :=
    exists_solvesDescriptorOn A B C D f g hf.continuous hg.continuous t₀ T x₀ y₀ hcons
  have hfF : ContDiff ℝ 2 (Function.uncurry (reducedField A B C D f g)) :=
    contDiff_reducedField A B C D f g hf hg
  have hlipF : ∀ t ∈ Set.Icc t₀ T, LipschitzWith (reducedLipschitzConstant A B C D)
      (reducedField A B C D f g t) :=
    fun t _ => lipschitzWith_reducedField A B C D f g t
  obtain ⟨xE, hxE0, hxE, CE, hC⟩ :=
    MathlibExt.Analysis.ODE.ExplicitEulerWanted.explicit_euler_first_order_convergence
      (reducedField A B C D f g) t₀ T x₀ (reducedLipschitzConstant A B C D) hT hfF hlipF
  refine ⟨hexists, max CE 0, le_max_right _ _, ?_⟩
  intro x y hx0 hsol h hh X hX k hkh
  rw [solvesDescriptorOn_iff] at hsol
  obtain ⟨hxred, hyrec⟩ := hsol
  have hunique : Set.EqOn x xE (Set.Icc t₀ T) := by
    refine ODE_solution_unique_of_mem_Icc_right (v := reducedField A B C D f g)
      (s := fun _ => Set.univ) (K := reducedLipschitzConstant A B C D) ?hv ?hf ?hf' ?hfs
      ?hg ?hg' ?hgs ?ha
    · intro t ht
      exact (lipschitzWith_reducedField A B C D f g t).lipschitzOnWith
    · intro t ht
      exact (hxred t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hxred t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht
      exact Set.mem_univ _
    · intro t ht
      exact (hxE t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hxE t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht
      exact Set.mem_univ _
    · exact hx0.trans hxE0.symm
  have hEx : ∃ X' : ℕ → (n → ℝ), X' 0 = x₀ ∧
      (∀ n, X' (n + 1) = X' n + h • reducedField A B C D f g (t₀ + (n : ℝ) * h) (X' n)) := by
    refine ⟨Nat.rec (motive := fun _ => n → ℝ) x₀
      (fun k Xk => Xk + h • reducedField A B C D f g (t₀ + (k : ℝ) * h) Xk), rfl,
      fun k => rfl⟩
  obtain ⟨X', hX'0, hX'rec⟩ := hEx
  have hX'seq : IsReducedEulerSequence A B C D f g t₀ h X' := hX'rec
  have hkh0 : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.1.le
  have hmem : t₀ + (k : ℝ) * h ∈ Set.Icc t₀ T :=
    ⟨le_add_of_nonneg_right hkh0, by linarith⟩
  have hxeq : x (t₀ + (k : ℝ) * h) = xE (t₀ + (k : ℝ) * h) := hunique hmem
  have hstab0 :=
    norm_sub_le_of_isReducedEulerSequence A B C D f g t₀ h hh.1.le X X' hX hX'seq k
  rw [hX'0] at hstab0
  have hmono : Real.exp ((reducedLipschitzConstant A B C D : ℝ) * ((k : ℝ) * h)) * ‖X 0 - x₀‖ ≤
      Real.exp ((reducedLipschitzConstant A B C D : ℝ) * (T - t₀)) * ‖X 0 - x₀‖ :=
    mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hkh (by positivity))) (norm_nonneg _)
  have hstab := hstab0.trans hmono
  have hprov0 := hC h hh X' hX'0 hX'rec k hkh
  have hCK : CE * h ≤ max CE 0 * h := mul_le_mul_of_nonneg_right (le_max_left _ _) hh.1.le
  have hprov : ‖X' k - x (t₀ + (k : ℝ) * h)‖ ≤ max CE 0 * h := by
    rw [hxeq]
    exact hprov0.trans hCK
  have htri : ‖X k - x (t₀ + (k : ℝ) * h)‖ ≤
      ‖X k - X' k‖ + ‖X' k - x (t₀ + (k : ℝ) * h)‖ := by
    have heq : X k - x (t₀ + (k : ℝ) * h) =
        (X k - X' k) + (X' k - x (t₀ + (k : ℝ) * h)) := by abel
    rw [heq]
    exact norm_add_le _ _
  have hstate : ‖X k - x (t₀ + (k : ℝ) * h)‖ ≤
      Real.exp ((reducedLipschitzConstant A B C D : ℝ) * (T - t₀)) * ‖X 0 - x₀‖ + max CE 0 * h :=
    htri.trans (add_le_add hstab hprov)
  have hyalg : y (t₀ + (k : ℝ) * h) =
      algebraicReconstruction D C (x (t₀ + (k : ℝ) * h)) (g (t₀ + (k : ℝ) * h)) :=
    hyrec _ hmem
  have halg : reconstructedAlgebraic C D g t₀ h X k - y (t₀ + (k : ℝ) * h) =
      algebraicReconstruction D C (X k) (g (t₀ + (k : ℝ) * h)) -
        algebraicReconstruction D C (x (t₀ + (k : ℝ) * h)) (g (t₀ + (k : ℝ) * h)) := by
    simp only [reconstructedAlgebraic]
    rw [hyalg]
  have hrec := norm_algebraicReconstruction_sub_le C D (X k) (x (t₀ + (k : ℝ) * h))
    (g (t₀ + (k : ℝ) * h))
  have hg0 : 0 ≤ reconstructionGain C D := by
    unfold reconstructionGain
    exact norm_nonneg _
  refine ⟨hstate, ?_⟩
  rw [halg]
  refine hrec.trans ?_
  exact mul_le_mul_of_nonneg_left hstate hg0

/-! ### D. Validation -/

-- The scalar fixture below uses `D = 1`; its invertibility is a local instance only.
attribute [local instance] invertibleOne

/-- Scalar fixture: `x' = y`, `0 = x + y` (so `y = -x` and the reduced equation is `x' = -x`),
with zero forcing. The iterates `X k = (11/10) (1 - h)^k` start with initial mismatch `1/10`
against the exact initial state `1`. -/
noncomputable def scalarEulerIterates (h : ℝ) : ℕ → Fin 1 → ℝ :=
  fun k _ => (11 / 10 : ℝ) * (1 - h) ^ k

/-- **Two step sizes and a nonzero initial mismatch.** For each step size `h ∈ {1/2, 1/4}`, the
scalar iterates are a reduced Euler sequence of the fixture with initial mismatch `1/10`, the
reconstructed algebraic iterates are their negatives, and `(e^{-t}, -e^{-t})` is a solution on
`[0, 1]` through the consistent pair `(1, -1)`; at the horizon `T = 1` the iterates take the
values `11/40` (two steps of `1/2`) and `891/2560` (four steps of `1/4`). -/
lemma scalarEuler_twoStepSizes (h : ℝ) (hh : h = 1 / 2 ∨ h = 1 / 4) :
    IsReducedEulerSequence (0 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 0) (fun _ _ => 0)
        0 h (scalarEulerIterates h) ∧
      scalarEulerIterates h 0 - (fun _ => 1) = (fun _ => 1 / 10) ∧
      (∀ k, reconstructedAlgebraic (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (fun _ _ => 0) 0 h
          (scalarEulerIterates h) k = -scalarEulerIterates h k) ∧
      consistentPair (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (fun _ => 0) (fun _ => 1) (fun _ => -1) ∧
      SolvesDescriptorOn (0 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 0) (fun _ _ => 0)
        0 1 (fun t _ => Real.exp (-t)) (fun t _ => -Real.exp (-t)) ∧
      scalarEulerIterates (1 / 2) 2 = (fun _ => 11 / 40) ∧
      scalarEulerIterates (1 / 4) 4 = (fun _ => 891 / 2560) := by
  have _ := hh
  have hfield : ∀ (t : ℝ) (v : Fin 1 → ℝ), reducedField (0 : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 0) (fun _ _ => 0) t v = -v := by
    intro t v
    simp [reducedField, reducedForcingPath, reducedForcing, schur, Matrix.neg_mulVec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [hfield]
    ext i
    simp only [scalarEulerIterates, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    rw [pow_succ]
    ring
  · ext i
    simp only [scalarEulerIterates, Pi.sub_apply, pow_zero, mul_one]
    norm_num
  · intro k
    unfold reconstructedAlgebraic algebraicReconstruction
    rw [show ((fun _ _ => (0 : ℝ)) ((0 : ℝ) + (k : ℝ) * h)) = 0 from rfl, add_zero, inv_one,
      Matrix.one_mulVec, Matrix.one_mulVec]
  · change (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (fun _ => 1) +
        (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (fun _ => -1) + (fun _ => 0) = 0
    ext i
    simp
  · intro t ht
    constructor
    · have hneg : HasDerivAt (fun t : ℝ => -t) (-1) t := (hasDerivAt_id t).neg
      have hexp1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
        have h := HasDerivAt.comp t (Real.hasDerivAt_exp (-t)) hneg
        simpa [Function.comp_def] using h
      have hsmul := hexp1.smul_const (fun _ : Fin 1 => (1 : ℝ))
      have hfun : (fun y : ℝ => Real.exp (-y) • (fun _ : Fin 1 => (1 : ℝ))) =
          (fun t : ℝ => fun _ : Fin 1 => Real.exp (-t)) := by
        funext y i
        simp
      have hderiv : (-Real.exp (-t)) • (fun _ : Fin 1 => (1 : ℝ)) =
          (fun _ : Fin 1 => -Real.exp (-t)) := by
        funext i
        simp
      rw [hfun, hderiv] at hsmul
      have hval : (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ((fun t _ => Real.exp (-t)) t) +
          (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ((fun t _ => -Real.exp (-t)) t) +
          (fun _ _ => (0 : ℝ)) t = (fun _ => -Real.exp (-t)) := by
        ext i
        simp
      rw [hval]
      exact hsmul
    · ext i
      simp
  · ext i
    simp only [scalarEulerIterates]
    norm_num
  · ext i
    simp only [scalarEulerIterates]
    norm_num

/-- **An inconsistent algebraic reconstruction does not inherit the error bound.** If `y₀'` is
not consistent with `x₀` at `t₀`, then even with zero state error its distance to the exact
algebraic value at `t₀` is a positive constant, so it is bounded by `K h` for no constant `K` and
all steps `h ∈ (0, T - t₀]`. -/
lemma not_forall_le_of_not_consistentPair {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq m] (C : Matrix m n ℝ) (D : Matrix m m ℝ) [Invertible D] (g : ℝ → m → ℝ)
    (t₀ T : ℝ) (hT : t₀ < T) (x₀ : n → ℝ) (y₀' : m → ℝ)
    (hbad : ¬ consistentPair C D (g t₀) x₀ y₀') (K : ℝ) :
    ¬ ∀ h ∈ Set.Ioc 0 (T - t₀),
      ‖y₀' - algebraicReconstruction D C x₀ (g t₀)‖ ≤ K * h := by
  have hne : y₀' ≠ algebraicReconstruction D C x₀ (g t₀) := by
    intro heq
    apply hbad
    rw [consistentPair_iff_eq_algebraicReconstruction]
    exact heq
  have hpos : 0 < ‖y₀' - algebraicReconstruction D C x₀ (g t₀)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  intro hall
  by_cases hK : K ≤ 0
  · have hmem : (T - t₀) / 2 ∈ Set.Ioc 0 (T - t₀) := by
      constructor
      · linarith [hT]
      · linarith [sub_pos.mpr hT]
    have hle := hall _ hmem
    have hnonpos : K * ((T - t₀) / 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hK (by linarith [sub_pos.mpr hT])
    linarith
  · have hK : 0 < K := lt_of_not_ge hK
    have hKne : K ≠ 0 := ne_of_gt hK
    set c := ‖y₀' - algebraicReconstruction D C x₀ (g t₀)‖ with hc
    have hmem : min (T - t₀) (c / (2 * K)) ∈ Set.Ioc 0 (T - t₀) := by
      constructor
      · exact lt_min (sub_pos.mpr hT) (div_pos hpos (mul_pos (by norm_num) hK))
      · exact min_le_left _ _
    have hle := hall _ hmem
    have hKmin : K * min (T - t₀) (c / (2 * K)) ≤ K * (c / (2 * K)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le
    have hcalc : K * (c / (2 * K)) = c / 2 := by
      field_simp
    linarith


end PhyslibExt.Circuits.IndexOneEulerBridge
