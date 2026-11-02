/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Process.Stopping

/-!
# Bounded optional stopping, expectation form, for supermartingales and martingales

For a supermartingale `f` and stopping times `τ ≤ π` with `π` bounded, the
expected stopped values decrease along the stopping times:
`E[f_π] ≤ E[f_τ]`. For a martingale they are equal: `E[f_τ] = E[f_π]`.

## Source

This formalizes `Supermartingale.expected_stoppedValue_le` of
`v1/Atlas/TheoryOfProbability/code/OptionalStoppingExpectation.lean`
(Lecture 29, "General form of optional stopping" in
`v1/Atlas/TheoryOfProbability/targets.yaml`): for a supermartingale `f` and
a bounded stopping time `τ`, `E[f_τ] ≤ E[f_0]`. That file also contains the
submartingale version `Submartingale.expected_stoppedValue_mono_real`,
which is **not** re-proved here: it is already in Mathlib as
`Submartingale.expected_stoppedValue_mono`.

The supermartingale and martingale statements here are the duals of that
Mathlib theorem, obtained by negating the process. The general two-stopping-
time form `Supermartingale.expected_stoppedValue_anti_mono` is proved first;
v1's one-stopping-time form is its special case `τ₀ = 0`, and the martingale
equality follows from the sub- and supermartingale inequalities.

## Scope

Only the bounded-stopping-time, expectation form is claimed. The
conditional form (`E[f_M | ℱ_L]`) is batch 15's
`Supermartingale.condExp_stoppedValue_le_stoppedValue`, and the
unbounded / uniformly-integrable form (`general_optional_stopping` in
v1) is left unproved there and is not claimed here.

## Main results

* `MeasureTheory.Supermartingale.expected_stoppedValue_anti_mono`:
  for a supermartingale `f` and stopping times `τ ≤ π` with `π` bounded,
  `E[f_π] ≤ E[f_τ]`.
* `MeasureTheory.Supermartingale.expected_stoppedValue_le`:
  v1's statement, for a bounded stopping time `τ`,
  `E[f_τ] ≤ E[f_0]`.
* `MeasureTheory.Martingale.expected_stoppedValue_eq`:
  for a martingale `f` and stopping times `τ ≤ π` with `π` bounded,
  `E[f_τ] = E[f_π]`.
* `MeasureTheory.Martingale.expected_stoppedValue_eq_zero`:
  for a martingale `f` and a bounded stopping time `τ`,
  `E[f_τ] = E[f_0]`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {f : ℕ → Ω → ℝ} {τ π : Ω → WithTop ℕ}

/-- **Optional stopping for supermartingales at two bounded stopping times.** Let $\mu$ be a
measure on $\Omega$ and $(\mathcal G_n)_{n \ge 0}$ a filtration such that the restriction of $\mu$
to each $\mathcal G_n$ is σ-finite, and let $(f_n)_{n \ge 0}$ be a real-valued supermartingale
with respect to $(\mathcal G_n)$ and $\mu$. Let $\tau$ and $\pi$ be stopping times for
$(\mathcal G_n)$ with values in $\mathbb N \cup \{\infty\}$, and let $N$ be a natural number such
that $\tau(\omega) \le \pi(\omega) \le N$ for every $\omega \in \Omega$. Then
$\int f_\pi \, d\mu \le \int f_\tau \, d\mu$, where $f_\tau(\omega) = f_{\tau(\omega)}(\omega)$.

This is the dual of the submartingale form of bounded optional stopping, obtained by applying
it to $-f$. -/
theorem Supermartingale.expected_stoppedValue_anti_mono
    [SigmaFiniteFiltration μ 𝒢]
    (hf : Supermartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π)
    (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    μ[stoppedValue f π] ≤ μ[stoppedValue f τ] := by
  have h := hf.neg.expected_stoppedValue_mono hτ hπ hle hbdd
  rw [stoppedValue_neg, stoppedValue_neg] at h
  simp only [Pi.neg_apply, integral_neg] at h
  exact neg_le_neg_iff.mp h

/-- **Optional stopping for supermartingales at a bounded stopping time.** Let $\mu$ be a measure
on $\Omega$ and $(\mathcal G_n)_{n \ge 0}$ a filtration such that the restriction of $\mu$ to each
$\mathcal G_n$ is σ-finite, and let $(f_n)_{n \ge 0}$ be a real-valued supermartingale with
respect to $(\mathcal G_n)$ and $\mu$. Let $\tau$ be a stopping time for $(\mathcal G_n)$ with
values in $\mathbb N \cup \{\infty\}$, and let $N$ be a natural number such that
$\tau(\omega) \le N$ for every $\omega \in \Omega$. Then $\int f_\tau \, d\mu \le \int f_0 \, d\mu$,
where $f_\tau(\omega) = f_{\tau(\omega)}(\omega)$. -/
theorem Supermartingale.expected_stoppedValue_le
    [SigmaFiniteFiltration μ 𝒢]
    (hf : Supermartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ)
    {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    μ[stoppedValue f τ] ≤ μ[f 0] := by
  have h := hf.expected_stoppedValue_anti_mono
    (isStoppingTime_const 𝒢 (0 : ℕ)) hτ (fun _ => bot_le) hbdd
  rwa [stoppedValue_const] at h

/-- **Optional stopping for martingales at two bounded stopping times.** Let $\mu$ be a measure
on $\Omega$ and $(\mathcal G_n)_{n \ge 0}$ a filtration such that the restriction of $\mu$ to each
$\mathcal G_n$ is σ-finite, and let $(f_n)_{n \ge 0}$ be a real-valued martingale with respect to
$(\mathcal G_n)$ and $\mu$. Let $\tau$ and $\pi$ be stopping times for $(\mathcal G_n)$ with
values in $\mathbb N \cup \{\infty\}$, and let $N$ be a natural number such that
$\tau(\omega) \le \pi(\omega) \le N$ for every $\omega \in \Omega$. Then
$\int f_\tau \, d\mu = \int f_\pi \, d\mu$, where $f_\tau(\omega) = f_{\tau(\omega)}(\omega)$. -/
theorem Martingale.expected_stoppedValue_eq
    [SigmaFiniteFiltration μ 𝒢]
    (hf : Martingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π)
    (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    μ[stoppedValue f τ] = μ[stoppedValue f π] :=
  le_antisymm
    (hf.submartingale.expected_stoppedValue_mono hτ hπ hle hbdd)
    (hf.supermartingale.expected_stoppedValue_anti_mono hτ hπ hle hbdd)

/-- **Optional stopping for martingales at a bounded stopping time.** Let $\mu$ be a measure on
$\Omega$ and $(\mathcal G_n)_{n \ge 0}$ a filtration such that the restriction of $\mu$ to each
$\mathcal G_n$ is σ-finite, and let $(f_n)_{n \ge 0}$ be a real-valued martingale with respect to
$(\mathcal G_n)$ and $\mu$. Let $\tau$ be a stopping time for $(\mathcal G_n)$ with values in
$\mathbb N \cup \{\infty\}$, and let $N$ be a natural number such that $\tau(\omega) \le N$ for
every $\omega \in \Omega$. Then $\int f_\tau \, d\mu = \int f_0 \, d\mu$, where
$f_\tau(\omega) = f_{\tau(\omega)}(\omega)$. -/
theorem Martingale.expected_stoppedValue_eq_zero
    [SigmaFiniteFiltration μ 𝒢]
    (hf : Martingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ)
    {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    μ[stoppedValue f τ] = μ[f 0] := by
  have h := hf.expected_stoppedValue_eq
    (isStoppingTime_const 𝒢 (0 : ℕ)) hτ (fun _ => bot_le) hbdd
  rw [stoppedValue_const] at h
  exact h.symm

end MeasureTheory
