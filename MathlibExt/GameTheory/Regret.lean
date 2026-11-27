/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.Basic
public import MathlibExt.Analysis.Convex.StdSimplexWeights
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# External and swap regret

This file is the canonical regret vocabulary for online learning in games. It has
two layers. The base layer is game-free: a finite action type `K`, loss vectors
over a horizon `T`, played weight functions (distributions when each round's
weights lie in the simplex, `IsSimplex`), and external, swap, and average
regret. Following `NoRegretDynamics` and `CorrelatedEquilibrium`, play is a
raw weight function and distribution facts are carried as `IsSimplex`
hypotheses; `IsSimplex.toStdSimplex` and `isSimplex_weights` bridge to
`Convexity.StdSimplex` points.
The game layer, which induces a player's loss vector from the opponents' mixed
play in a finite normal-form cost game, lives in
`MathlibExt/GameTheory/RegretInducedLoss.lean`, so this base module stays
below the equilibrium modules.

## Main results

Base definitions (C1):

* `IsSimplex`: the probability simplex on a finite type.
* `cumulativeLoss`: cumulative loss of a fixed action.
* `expectedLoss`: play-weighted loss; the expected loss when play is a
  distribution.
* `swapRegret`: expected loss minus the best action remapping's loss.
* `externalRegret`: expected loss minus the best fixed action's cumulative loss.
* `averageRegret`: external regret divided by the horizon.

Base lemmas (C2):

* `expectedLoss_sub_weightedCumulative_le_externalRegret`
* `externalRegret_le_swapRegret`
* `externalRegret_add_roundConst`

Game layer (C3, in `RegretInducedLoss`): the `pureCost` sum form and bounds.

## Non-goals

No learning algorithm and no regret bounds appear here, and no equilibrium
convergence theorem: this file only fixes the vocabulary the later stages build
on.

## References

* T. Roughgarden, CS364A lecture notes (no-regret definitions).
* Y. Freund and R. Schapire (1999) (the [0,1] loss normalization).
-/

@[expose] public section

namespace MathlibExt.GameTheory.Regret

open scoped BigOperators

variable {K : Type*} [Fintype K] [DecidableEq K] [Nonempty K]
variable {T : ℕ}

/-- The probability simplex on `K`: `p` is the weight function of a point
of the standard simplex `Convexity.StdSimplex ℝ K`. (C1 base defs) -/
def IsSimplex (p : K → ℝ) : Prop :=
  ∃ x : Convexity.StdSimplex ℝ K, ∀ a, x.weights a = p a

omit [DecidableEq K] [Nonempty K] in
/-- A weight function is in the simplex when it is nonnegative and sums
to one. -/
theorem isSimplex_iff (p : K → ℝ) :
    IsSimplex p ↔ (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1 := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun a => hx a ▸ x.nonneg a, ?_⟩
    have h := x.total
    rw [Finsupp.sum_fintype _ _ fun _ => rfl] at h
    rw [← h]
    exact Finset.sum_congr rfl fun a _ => (hx a).symm
  · rintro ⟨h0, h1⟩
    exact ⟨Convexity.StdSimplex.ofWeights p h0 h1,
      Convexity.StdSimplex.ofWeights_weights p h0 h1⟩

/-- The standard-simplex point whose weights are `p`. -/
noncomputable def IsSimplex.toStdSimplex (p : K → ℝ) (h : IsSimplex p) :
    Convexity.StdSimplex ℝ K :=
  Classical.choose h

omit [Fintype K] [DecidableEq K] [Nonempty K] in
/-- The weights of the standard-simplex point built from `p` are `p`. -/
theorem IsSimplex.toStdSimplex_weights (p : K → ℝ) (h : IsSimplex p) (a : K) :
    (IsSimplex.toStdSimplex p h).weights a = p a :=
  Classical.choose_spec h a

omit [Fintype K] [DecidableEq K] [Nonempty K] in
/-- The weights of a point of the standard simplex lie in the simplex. -/
theorem isSimplex_weights (x : Convexity.StdSimplex ℝ K) :
    IsSimplex x.weights :=
  ⟨x, fun _ => rfl⟩

/-- Cumulative loss of the fixed action `a` over the horizon. (C1 base defs) -/
def cumulativeLoss (loss : Fin T → K → ℝ) (a : K) : ℝ :=
  ∑ t, loss t a

/-- Play-weighted loss `∑ t, ∑ a, play t a * loss t a`; when each `play t`
is a distribution (`IsSimplex (play t)`), the expected loss of the played
distributions. (C1 base defs) -/
def expectedLoss (play loss : Fin T → K → ℝ) : ℝ :=
  ∑ t, ∑ a, play t a * loss t a

/-- External regret: expected loss minus the best fixed action's cumulative
loss. (C1 base defs) -/
def externalRegret (play loss : Fin T → K → ℝ) : ℝ :=
  expectedLoss play loss - Finset.univ.inf' Finset.univ_nonempty (cumulativeLoss loss)

/-- Swap regret: expected loss minus the best action remapping's loss.
(C1 base defs) -/
def swapRegret (play loss : Fin T → K → ℝ) : ℝ :=
  expectedLoss play loss -
    Finset.univ.inf' Finset.univ_nonempty
      (fun δ : K → K => ∑ t, ∑ a, play t a * loss t (δ a))

/-- Average regret: external regret divided by the horizon; for `T = 0` it is
`0`, as `x / 0 = 0`. (C1 base defs) -/
noncomputable def averageRegret (play loss : Fin T → K → ℝ) : ℝ :=
  externalRegret play loss / (T : ℝ)

omit [DecidableEq K] in
/-- Regret against any fixed distribution is at most external regret.
(C2 base lemmas) -/
theorem expectedLoss_sub_weightedCumulative_le_externalRegret
    (play loss : Fin T → K → ℝ) (q : K → ℝ) (hq : IsSimplex q) :
    expectedLoss play loss - ∑ a, q a * cumulativeLoss loss a ≤
      externalRegret play loss := by
  obtain ⟨hqnonneg, hqsum⟩ := (isSimplex_iff q).mp hq
  simp only [externalRegret]
  refine sub_le_sub_left ?_ _
  have hC : Finset.univ.inf' Finset.univ_nonempty (cumulativeLoss loss)
      = ∑ a, q a * Finset.univ.inf' Finset.univ_nonempty (cumulativeLoss loss) := by
    rw [← Finset.sum_mul, hqsum, one_mul]
  rw [hC]
  refine Finset.sum_le_sum fun a _ => ?_
  exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ a)) (hqnonneg a)

/-- External regret is at most swap regret: every fixed action is a constant
remapping. (C2 base lemmas) -/
theorem externalRegret_le_swapRegret (play loss : Fin T → K → ℝ)
    (hplay : ∀ t, IsSimplex (play t)) :
    externalRegret play loss ≤ swapRegret play loss := by
  simp only [externalRegret, swapRegret]
  refine sub_le_sub_left ?_ _
  obtain ⟨aStar, -, haStar⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty (cumulativeLoss loss)
  have hEq : (∑ t, ∑ a, play t a * loss t aStar)
      = cumulativeLoss loss aStar := by
    show (∑ t, ∑ a, play t a * loss t aStar) = ∑ t, loss t aStar
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨-, hpt⟩ := (isSimplex_iff _).mp (hplay t)
    rw [← Finset.sum_mul, hpt, one_mul]
  rw [haStar]
  exact le_trans (Finset.inf'_le _ (Finset.mem_univ (fun _ => aStar))) (le_of_eq hEq)

omit [DecidableEq K] in
/-- Adding a per-round constant to every action's loss does not change external
regret. (C2 base lemmas) -/
theorem externalRegret_add_roundConst (play loss : Fin T → K → ℝ)
    (hplay : ∀ t, IsSimplex (play t)) (c : Fin T → ℝ) :
    externalRegret play (fun t a => loss t a + c t) = externalRegret play loss := by
  simp only [externalRegret, expectedLoss]
  have hinner : ∀ t : Fin T, (∑ a, play t a * (loss t a + c t))
      = (∑ a, play t a * loss t a) + c t := by
    intro t
    obtain ⟨-, hpt⟩ := (isSimplex_iff _).mp (hplay t)
    have hsplit : (∑ a, play t a * (loss t a + c t))
        = ∑ a, (play t a * loss t a + play t a * c t) :=
      Finset.sum_congr rfl fun a _ => mul_add _ _ _
    rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul, hpt, one_mul]
  have hEL : (∑ t, ∑ a, play t a * (loss t a + c t))
      = (∑ t, ∑ a, play t a * loss t a) + ∑ t, c t := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => hinner t
  have hcum : ∀ a : K, cumulativeLoss (fun t a => loss t a + c t) a
      = cumulativeLoss loss a + ∑ t, c t := by
    intro a
    show (∑ t, (loss t a + c t)) = (∑ t, loss t a) + ∑ t, c t
    exact Finset.sum_add_distrib
  have hinf : Finset.univ.inf' Finset.univ_nonempty
        (cumulativeLoss (fun t a => loss t a + c t))
      = Finset.univ.inf' Finset.univ_nonempty (cumulativeLoss loss) + ∑ t, c t := by
    have hfun : cumulativeLoss (fun t a => loss t a + c t)
        = fun a => cumulativeLoss loss a + ∑ t, c t :=
      funext hcum
    rw [hfun]
    refine le_antisymm ?_ ?_
    · obtain ⟨aStar, -, haStar⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (cumulativeLoss loss)
      have h1 : Finset.univ.inf' Finset.univ_nonempty
            (fun a => cumulativeLoss loss a + ∑ t, c t)
          ≤ cumulativeLoss loss aStar + ∑ t, c t :=
        Finset.inf'_le _ (Finset.mem_univ aStar)
      rw [← haStar] at h1
      exact h1
    · refine Finset.le_inf' _ _ fun a _ => ?_
      exact add_le_add (Finset.inf'_le _ (Finset.mem_univ a)) le_rfl
  rw [hEL, hinf, add_sub_add_right_eq_sub]

end MathlibExt.GameTheory.Regret
