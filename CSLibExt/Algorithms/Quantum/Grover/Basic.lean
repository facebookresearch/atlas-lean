/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Real.Sqrt

/-!
# Finite real-amplitude model for Grover search

Grover's algorithm stays in a real two-dimensional subspace when it starts in
the uniform state and uses the standard phase oracle. This file therefore uses
real amplitude vectors on a finite type. It defines the phase oracle and the
probability mass assigned to a finite set of outcomes.
-/

@[expose] public section

open scoped BigOperators

namespace Cslib.Grover

/-- **Real amplitude vectors.** For a type $\alpha$ (the search space), a real amplitude vector
indexed by $\alpha$ is a function $\psi : \alpha \to \mathbb{R}$, assigning a real amplitude to
each point of $\alpha$. -/
abbrev Amplitude (α : Type*) := α → ℝ

/-- **Phase oracle.** For a type $\alpha$ and a finite set $M \subseteq \alpha$ of marked
elements, the phase oracle sends a real amplitude vector $\psi$ on $\alpha$ to the amplitude
vector whose value at $x$ is $-\psi(x)$ if $x \in M$ and $\psi(x)$ if $x \notin M$; that is, it
negates exactly the amplitudes at the marked elements. -/
def phaseOracle {α : Type*} [DecidableEq α] (marked : Finset α)
    (ψ : Amplitude α) : Amplitude α :=
  fun x => if x ∈ marked then -ψ x else ψ x

@[simp]
theorem phaseOracle_apply_of_mem {α : Type*} [DecidableEq α]
    (marked : Finset α) (ψ : Amplitude α) {x : α} (hx : x ∈ marked) :
    phaseOracle marked ψ x = -ψ x := by
  simp [phaseOracle, hx]

@[simp]
theorem phaseOracle_apply_of_not_mem {α : Type*} [DecidableEq α]
    (marked : Finset α) (ψ : Amplitude α) {x : α} (hx : x ∉ marked) :
    phaseOracle marked ψ x = ψ x := by
  simp [phaseOracle, hx]

@[simp]
theorem phaseOracle_involutive {α : Type*} [DecidableEq α]
    (marked : Finset α) (ψ : Amplitude α) :
    phaseOracle marked (phaseOracle marked ψ) = ψ := by
  funext x
  by_cases hx : x ∈ marked <;> simp [phaseOracle, hx]

/-- **Squared norm of an amplitude vector.** For a finite type $\alpha$ and a real amplitude
vector $\psi : \alpha \to \mathbb{R}$, the squared norm of $\psi$ is its squared Euclidean
norm $\sum_{x \in \alpha} \psi(x)^2$. -/
def amplitudeNormSq {α : Type*} [Fintype α] (ψ : Amplitude α) : ℝ :=
  ∑ x, (ψ x) ^ 2

/-- **Probability of the marked outcomes.** For a real amplitude vector $\psi$ on a type
$\alpha$ and a finite set $M \subseteq \alpha$ of marked elements, the marked probability is
$\sum_{x \in M} \psi(x)^2$. When $\alpha$ is finite and $\psi$ has squared norm $1$, this is
the probability of observing a marked outcome. -/
def markedProbability {α : Type*} (marked : Finset α) (ψ : Amplitude α) : ℝ :=
  ∑ x ∈ marked, (ψ x) ^ 2

@[simp]
theorem amplitudeNormSq_phaseOracle {α : Type*} [Fintype α] [DecidableEq α]
    (marked : Finset α) (ψ : Amplitude α) :
    amplitudeNormSq (phaseOracle marked ψ) = amplitudeNormSq ψ := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ marked <;> simp [phaseOracle, hx]

@[simp]
theorem markedProbability_phaseOracle {α : Type*} [DecidableEq α]
    (marked : Finset α) (ψ : Amplitude α) :
    markedProbability marked (phaseOracle marked ψ) =
      markedProbability marked ψ := by
  apply Finset.sum_congr rfl
  intro x hx
  simp [phaseOracle, hx]

/-- **Uniform amplitude vector.** For a finite type $\alpha$, the uniform amplitude vector on
$\alpha$ is the real amplitude vector whose value at every point is $1/\sqrt{|\alpha|}$, where
$|\alpha|$ is the number of elements of $\alpha$. -/
noncomputable def uniformAmplitude (α : Type*) [Fintype α] : Amplitude α :=
  fun _ => 1 / Real.sqrt (Fintype.card α)

@[simp]
theorem uniformAmplitude_apply (α : Type*) [Fintype α] (x : α) :
    uniformAmplitude α x = 1 / Real.sqrt (Fintype.card α) := rfl

/-- **The uniform amplitude vector is normalized.** For every nonempty finite type
$\alpha$, the uniform amplitude vector on $\alpha$ has squared Euclidean norm $1$. -/
@[simp]
theorem amplitudeNormSq_uniformAmplitude (α : Type*) [Fintype α] [Nonempty α] :
    amplitudeNormSq (uniformAmplitude α) = 1 := by
  rw [amplitudeNormSq]
  simp only [uniformAmplitude, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcardpos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [div_pow, one_pow, Real.sq_sqrt hcardpos.le]
  field_simp

end Cslib.Grover
