/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Topology.ScottishBook43Wanted

/-- A strategy in the Banach-Mazur game is valid if it always answers an
interval with a strictly smaller interval nested inside it. Strategies are
taken to depend only on the opponent's last move: the rest of the game depends
only on the current interval. -/
def BanachMazurStrategyValid (σ : (ℝ × ℝ) → ℝ × ℝ) : Prop :=
  ∀ I : ℝ × ℝ, I.1 < I.2 → (σ I).1 < (σ I).2 ∧
    Set.Ioo (σ I).1 (σ I).2 ⊆ Set.Ioo I.1 I.2

/-- A play `p` follows the first interval `first` and the strategies `σA`
for A and `σB` for B: A moves at even indices after the first, B at odd
indices. -/
def BanachMazurPlayConsistent (first : ℝ × ℝ) (σA σB : (ℝ × ℝ) → ℝ × ℝ)
    (p : ℕ → ℝ × ℝ) : Prop :=
  p 0 = first ∧ ∀ n : ℕ,
    (n % 2 = 0 → p (n + 1) = σB (p n)) ∧ (n % 2 = 1 → p (n + 1) = σA (p n))

/-- A has a winning strategy in the Banach-Mazur game for `E`: A chooses a
first interval and a strategy, and no matter how B plays, the intersection of
all chosen intervals meets `E`. -/
def BanachMazurAHasWinningStrategy (E : Set ℝ) : Prop :=
  ∃ first : ℝ × ℝ, ∃ σA : (ℝ × ℝ) → ℝ × ℝ, first.1 < first.2 ∧
    BanachMazurStrategyValid σA ∧
    ∀ σB : (ℝ × ℝ) → ℝ × ℝ, BanachMazurStrategyValid σB →
      ∀ p : ℕ → ℝ × ℝ, BanachMazurPlayConsistent first σA σB p →
        (⋂ n, Set.Ioo (p n).1 (p n).2) ∩ E ≠ ∅

/-- B has a winning strategy in the Banach-Mazur game for `E`: B has a
strategy such that, no matter how A opens and plays, the intersection of all
chosen intervals avoids `E`. -/
def BanachMazurBHasWinningStrategy (E : Set ℝ) : Prop :=
  ∃ σB : (ℝ × ℝ) → ℝ × ℝ, BanachMazurStrategyValid σB ∧
    ∀ first : ℝ × ℝ, ∀ σA : (ℝ × ℝ) → ℝ × ℝ, first.1 < first.2 →
      BanachMazurStrategyValid σA →
      ∀ p : ℕ → ℝ × ℝ, BanachMazurPlayConsistent first σA σB p →
        (⋂ n, Set.Ioo (p n).1 (p n).2) ∩ E = ∅

/--
Mazur, Problem 43 of the Scottish Book. Given a set `E` of real numbers, A
picks an interval `d₁`, B picks a subinterval `d₂` of `d₁`, A picks a
subinterval `d₃` of `d₂`, and so on. A wins if the intersection of all the
chosen intervals meets `E`; otherwise A loses. The problem asks whether A
has a winning method only for those `E` whose complement is of first
category in some interval, and whether B has a winning method when `E` is
of first category. The answer to both is affirmative, in the full
characterization form: A has a winning strategy exactly when `E` is
comeagre in some interval (its complement is meagre in that interval), and
B has a winning strategy exactly when `E` is meagre. This is the
Banach-Mazur game theorem (Oxtoby).
Source: S. Mazur, Problem 43 of the Scottish Book; addendum of S. Banach,
4 August 1935: "Mazur's conjecture is true"; J. C. Oxtoby, The Banach-Mazur
game and Banach category theorem; see the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted banach_mazur_winning_strategy_characterization :
    ∀ E : Set ℝ,
      (BanachMazurAHasWinningStrategy E ↔
        ∃ a b : ℝ, a < b ∧ IsMeagre (Set.Ioo a b \ E)) ∧
      (BanachMazurBHasWinningStrategy E ↔ IsMeagre E)

end MathlibExt.Topology.ScottishBook43Wanted
