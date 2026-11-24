/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Synchronization of pulse-coupled oscillators (Mirollo–Strogatz)

Mirollo and Strogatz (1990) model `N` identical integrate-and-fire oscillators by phases
`φ_i ∈ [0, 1]` that advance at unit speed, and a state `x_i = f(φ_i)`, where
`f : [0, 1] → [0, 1]` is smooth, increasing and concave down (`f' > 0`, `f'' < 0`), with
`f(0) = 0`, `f(1) = 1` and inverse `g`. When an oscillator reaches `φ = 1` it fires and resets
to `0`, and every other oscillator's state jumps to `min (1, x_j + ε)`; oscillators brought to
threshold by a pulse are absorbed into the firing group (they reset with it and do not emit a
pulse of their own at that event), and a group fires with a single pulse of nonnegative
strength. Their main result (Section 3, Theorems 3.1–3.2): for every `N ≥ 2` and almost every
initial configuration of phases (Lebesgue measure), the population becomes fully synchronized
after finitely many firings. The pulse strength of a merged group need not be additive.

Here the system is observed at firing events (`fire`): all phases advance until the largest
reaches `1`, the oscillators at `1` (a group of size `k`) fire with strength `s k`, and each other
oscillator moves to `g(f(φ_j) + s k)` if `f(φ_j) + s k < 1` and is absorbed (reset to `0`)
otherwise; `g` is evaluated only on `[0, 1)`. Group strengths are given by any rule `s` with
`s k > 0` for every group size `k ≥ 1`; this includes the identical-strength rule `s k = ε` and
the additive rule `s k = k ε`, and every strength `≥ 1` (immediate absorption of all other
oscillators). Strength rules that depend on more than the group size are not stated.

Sources: R. E. Mirollo and S. H. Strogatz, "Synchronization of pulse-coupled biological
oscillators", SIAM J. Appl. Math. 50 (1990) 1645–1662, Sections 2.1 and 3.1–3.5,
Theorems 3.1–3.2.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

@[expose] public section

namespace WantedExt.Biology.Neuroscience.PulseCoupledSynchronyWanted

open MeasureTheory Finset

variable {N : ℕ}

/-- The hypotheses on the state function `f` and its inverse `g` (Mirollo and Strogatz 1990,
Section 2.1): `f` is smooth on `[0, 1]`, with `f(0) = 0`, `f(1) = 1`, `f' > 0` and `f'' < 0` on
`[0, 1]` (one-sided derivatives at the endpoints); `g` maps `[0, 1]` to `[0, 1]` and is the
inverse of `f` there. -/
structure StateFunction (f g : ℝ → ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ ⊤ f (Set.Icc 0 1)
  map_zero : f 0 = 0
  map_one : f 1 = 1
  deriv_pos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < derivWithin f (Set.Icc 0 1) x
  deriv2_neg : ∀ x ∈ Set.Icc (0 : ℝ) 1, iteratedDerivWithin 2 f (Set.Icc 0 1) x < 0
  inv_mem : ∀ y ∈ Set.Icc (0 : ℝ) 1, g y ∈ Set.Icc (0 : ℝ) 1
  f_g : ∀ y ∈ Set.Icc (0 : ℝ) 1, f (g y) = y
  g_f : ∀ x ∈ Set.Icc (0 : ℝ) 1, g (f x) = x

open Classical in
/-- One firing event of the population with phases `φ`: all phases advance by `1 - max φ`, the
`k` oscillators that reach phase `1` fire with strength `s k` and reset to `0`, and every other
oscillator `j` moves to phase `g(f(ψ_j) + s k)` if `f(ψ_j) + s k < 1`, and is absorbed (reset to
`0`) otherwise, where `ψ` are the advanced phases. -/
noncomputable def fire (f g : ℝ → ℝ) (s : ℕ → ℝ) (φ : Fin N → ℝ) : Fin N → ℝ :=
  let ψ : Fin N → ℝ := fun i => φ i + (1 - ⨆ j, φ j)
  let k := (univ.filter fun i => ψ i = 1).card
  fun i => if ψ i = 1 ∨ 1 ≤ f (ψ i) + s k then 0 else g (f (ψ i) + s k)

/-- The population is fully synchronized: all phases are equal. -/
def Synchronized (φ : Fin N → ℝ) : Prop :=
  ∀ i j, φ i = φ j

/-- **Mirollo–Strogatz theorem** (Mirollo and Strogatz 1990, Section 3, Theorems 3.1–3.2). Let
`N ≥ 2`, let `f` and `g` satisfy the hypotheses of Section 2.1 (`StateFunction`: `f` smooth on
`[0, 1]` with `f(0) = 0`, `f(1) = 1`, `f' > 0`, `f'' < 0`, and `g` its inverse), and let the
group strengths satisfy `s k > 0` for every group size `k ≥ 1`. Then for almost every initial
configuration `φ ∈ [0, 1)^N` (Lebesgue measure on the cube), some finite number `n` of firing
events (`fire`) leads to a fully synchronized population: all phases of `fire^[n] φ` are equal.

Source: Mirollo and Strogatz (1990), Theorems 3.1–3.2. -/
theorem_wanted ae_eventually_synchronized (hN : 2 ≤ N) (f g : ℝ → ℝ)
    (hfg : StateFunction f g) (s : ℕ → ℝ) (hs : ∀ k, 1 ≤ k → 0 < s k) :
    ∀ᵐ φ ∂(volume.restrict (Set.pi Set.univ fun _ : Fin N => Set.Ico (0 : ℝ) 1)),
      ∃ n : ℕ, Synchronized ((fire f g s)^[n] φ)

end WantedExt.Biology.Neuroscience.PulseCoupledSynchronyWanted
