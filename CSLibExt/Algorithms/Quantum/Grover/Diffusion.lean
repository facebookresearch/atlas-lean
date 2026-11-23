/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Grover.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Grover diffusion operator

The diffusion operator reflects every amplitude about their arithmetic mean.
This file proves that the reflection is involutive and preserves the squared
Euclidean norm, then composes it with the phase oracle to form one Grover step.
-/

@[expose] public section

open scoped BigOperators

namespace Cslib.Grover

/-- **Mean amplitude.** For a finite type $\alpha$ and a real amplitude vector $\psi$ on $\alpha$,
the mean amplitude of $\psi$ is $\bigl(\sum_{x \in \alpha} \psi(x)\bigr) / |\alpha|$, the
arithmetic mean of its amplitudes. When $\alpha$ is empty it is $0$. -/
noncomputable def meanAmplitude {α : Type*} [Fintype α] (ψ : Amplitude α) : ℝ :=
  (∑ x, ψ x) / Fintype.card α

/-- **Inversion about the mean.** For a finite type $\alpha$, the diffusion operator sends a
real amplitude vector $\psi$ on $\alpha$ to the amplitude vector $x \mapsto 2\bar\psi - \psi(x)$,
where $\bar\psi$ is the arithmetic mean of the amplitudes of $\psi$. -/
noncomputable def diffusion {α : Type*} [Fintype α]
    (ψ : Amplitude α) : Amplitude α :=
  fun x => 2 * meanAmplitude ψ - ψ x

@[simp]
theorem diffusion_apply {α : Type*} [Fintype α] (ψ : Amplitude α) (x : α) :
    diffusion ψ x = 2 * meanAmplitude ψ - ψ x := rfl

theorem sum_eq_card_mul_meanAmplitude {α : Type*} [Fintype α] [Nonempty α]
    (ψ : Amplitude α) :
    ∑ x, ψ x = (Fintype.card α : ℝ) * meanAmplitude ψ := by
  rw [meanAmplitude]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

@[simp]
theorem meanAmplitude_diffusion {α : Type*} [Fintype α] [Nonempty α]
    (ψ : Amplitude α) :
    meanAmplitude (diffusion ψ) = meanAmplitude ψ := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum := sum_eq_card_mul_meanAmplitude ψ
  rw [meanAmplitude]
  simp only [diffusion, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [hsum]
  field_simp
  ring

@[simp]
theorem diffusion_involutive {α : Type*} [Fintype α] [Nonempty α]
    (ψ : Amplitude α) : diffusion (diffusion ψ) = ψ := by
  funext x
  rw [diffusion_apply, meanAmplitude_diffusion, diffusion_apply]
  ring

@[simp]
theorem amplitudeNormSq_diffusion {α : Type*} [Fintype α] [Nonempty α]
    (ψ : Amplitude α) :
    amplitudeNormSq (diffusion ψ) = amplitudeNormSq ψ := by
  have hsum := sum_eq_card_mul_meanAmplitude ψ
  unfold amplitudeNormSq
  simp only [diffusion]
  have hpoint (x : α) :
      (2 * meanAmplitude ψ - ψ x) ^ 2 =
        (ψ x) ^ 2 + 4 * (meanAmplitude ψ) ^ 2 -
          4 * meanAmplitude ψ * ψ x := by
    ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  rw [hsum]
  ring

/-- **Grover step.** Let $\alpha$ be a finite type and $M \subseteq \alpha$ a set of marked
elements. Write $O_M$ for the phase oracle, which negates the amplitudes at the points of $M$,
and $D$ for inversion about the mean, which sends an amplitude vector $\varphi$ on $\alpha$ to
$x \mapsto 2\bar\varphi - \varphi(x)$, where $\bar\varphi$ is the arithmetic mean of the amplitudes
of $\varphi$. One Grover step sends a real amplitude vector $\psi$ on $\alpha$ to $D(O_M \psi)$:
phase inversion followed by inversion about the mean. -/
noncomputable def groverStep {α : Type*} [Fintype α] [DecidableEq α]
    (marked : Finset α) (ψ : Amplitude α) : Amplitude α :=
  diffusion (phaseOracle marked ψ)

@[simp]
theorem groverStep_apply {α : Type*} [Fintype α] [DecidableEq α]
    (marked : Finset α) (ψ : Amplitude α) (x : α) :
    groverStep marked ψ x =
      2 * meanAmplitude (phaseOracle marked ψ) - phaseOracle marked ψ x := rfl

@[simp]
theorem amplitudeNormSq_groverStep {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (marked : Finset α) (ψ : Amplitude α) :
    amplitudeNormSq (groverStep marked ψ) = amplitudeNormSq ψ := by
  simp [groverStep]

end Cslib.Grover
