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
strength. Their main result (Section 3.5, Theorems 3.1–3.2): for every `N ≥ 2` and almost every
initial state just after a firing (Section 3.1, (3.1): one phase `0` and the other `N - 1` phases
ordered in `(0, 1)`, measured by `(N - 1)`-dimensional Lebesgue measure on that section), the
population becomes fully synchronized after finitely many firings, a group formed by an absorption
firing with the sum of its members' strengths. The authors remark (pp. 1654–1655) that additivity
is not needed for their argument, but the iteration of Theorem 3.2 is defined with the sums, and
the planned pages follow it. The proof rests on a local expansion step (Sections 2.3–2.4,
Lemma 2.1): for two oscillators, the firing map `h(φ) = g(f(1 - φ) + ε)`, which sends the phase of
one oscillator just before the other fires to its phase just after (when no absorption occurs),
has `h'(φ) < -1`, because `f'` is strictly decreasing. Theorem 3.1 then shows, through the return
map of the firing dynamics (injective, with Jacobian determinant exceeding `1`), that the set of
initial states that never undergo an absorption has measure zero in that section, and Theorem 3.2
inducts on the number of groups, a merged group acting as a single oscillator.

This module states the expansion step, `hasDerivAt_firingMap_lt_neg_one`. The measure-zero statement
for never-absorbed configurations (Theorem 3.1, with return-map injectivity and volume expansion)
and full synchronization almost everywhere (`Synchronized` after finitely many firings, Theorem 3.2,
by induction on the number of groups with null sets pulled back through mergers; `IsAbsorbed`
records a merger) are tracked as planned results depending on it, and are not stated here as
`theorem_wanted`.

Here the system is observed at firing events (`fire`): all phases advance until the largest
reaches `1`, the oscillators at `1` (a group of size `k`) fire with strength `s k`, and each other
oscillator moves to `g(f(φ_j) + s k)` if `f(φ_j) + s k < 1` and is absorbed (reset to `0`)
otherwise; `g` is evaluated only on `[0, 1)`. Group strengths are given by any rule `s` with
`s k > 0` for every group size `k ≥ 1`; this includes the identical-strength rule `s k = ε`, the
additive rule `s k = k ε` (Theorem 3.2's summed strengths of oscillators that each fire with
strength `ε`), and every strength `≥ 1` (immediate absorption of all other oscillators). Strength
rules that depend on more than the group size are not stated.

Sources: R. E. Mirollo and S. H. Strogatz, "Synchronization of pulse-coupled biological
oscillators", SIAM J. Appl. Math. 50 (1990) 1645–1662, Sections 2.1, 2.3–2.4 and 3.1–3.5,
Theorems 3.1–3.2.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

@[expose] public section

namespace WantedExt.Biology.Neuroscience.PulseCoupledSynchronyWanted

open Finset
open scoped ContDiff

variable {N : ℕ}

/-- The hypotheses on the state function `f` and its inverse `g` (Mirollo and Strogatz 1990,
Section 2.1): `f` is smooth on `[0, 1]`, with `f(0) = 0`, `f(1) = 1`, `f' > 0` and `f'' < 0` on
`[0, 1]` (one-sided derivatives at the endpoints); `g` maps `[0, 1]` to `[0, 1]` and is the
inverse of `f` there. -/
structure StateFunction (f g : ℝ → ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ ∞ f (Set.Icc 0 1)
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

/-- Some two oscillators share a phase: an absorption has merged them into one group (or they
started together). -/
def IsAbsorbed (φ : Fin N → ℝ) : Prop :=
  ¬ Function.Injective φ

/-- The firing map of two oscillators (Mirollo and Strogatz 1990, Section 2.3, Eq. (2.1)):
`h(φ) = g(f(1 - φ) + ε)`. If one oscillator has just fired and the other is at phase `φ`, then
when the second reaches threshold the first is at phase `1 - φ`, and after the pulse of strength
`ε` it is at phase `h(φ)`, provided `f(1 - φ) + ε < 1` (no absorption). -/
noncomputable def firingMap (f g : ℝ → ℝ) (ε φ : ℝ) : ℝ :=
  g (f (1 - φ) + ε)

/-- **The firing map expands.** Let `f` and `g` satisfy the hypotheses of Section 2.1
(`StateFunction`: `f` smooth on `[0, 1]` with `f(0) = 0`, `f(1) = 1`, `f' > 0`, `f'' < 0`, and `g`
its inverse), let `ε > 0` and `0 < φ < 1`, and assume no absorption, `f(1 - φ) + ε < 1`. Then the
firing map `h = firingMap f g ε` has a derivative `d` at `φ` with `d < -1`.

The value of the derivative and the place of `h(φ)` are facts of the source's proof of Lemma 2.1,
not part of this statement: its Eq. (2.3) gives `h'(φ) = -g'(ε + f(1 - φ)) / g'(f(1 - φ))`, which
is `-f'(1 - φ) / f'(h(φ))` since `g' = 1 / (f' ∘ g)`, and there `h(φ) = g(ε + f(1 - φ))` lies in
`(1 - φ, 1)` because `g` is increasing, `ε > 0` and `ε + f(1 - φ) < 1`.

Source: R. E. Mirollo and S. H. Strogatz, "Synchronization of pulse-coupled biological
oscillators", SIAM J. Appl. Math. 50 (1990) 1645–1662, Section 2.4, Lemma 2.1. -/
theorem_wanted hasDerivAt_firingMap_lt_neg_one (f g : ℝ → ℝ) (hfg : StateFunction f g)
    (ε φ : ℝ) (hε : 0 < ε) (hφ0 : 0 < φ) (hφ1 : φ < 1) (hnoabs : f (1 - φ) + ε < 1) :
    ∃ d : ℝ, HasDerivAt (firingMap f g ε) d φ ∧ d < -1

end WantedExt.Biology.Neuroscience.PulseCoupledSynchronyWanted
