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
public import MathlibExt.GameTheory.CorrelatedEquilibrium
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# External and swap regret

This file is the canonical regret vocabulary for online learning in games. It has
two layers. The base layer is game-free: a finite action type `K`, loss vectors
over a horizon `T`, played distributions, and external, swap, and average regret.
The game layer induces a player's loss vector from the opponents' mixed play in
a finite normal-form cost game.

## Main results

Base definitions (C1):

* `IsSimplex`: the probability simplex on a finite type.
* `cumulativeLoss`: cumulative loss of a fixed action.
* `expectedLoss`: expected loss of the played distributions.
* `swapRegret`: expected loss minus the best action remapping's loss.
* `externalRegret`: expected loss minus the best fixed action's cumulative loss.
* `averageRegret`: external regret divided by the horizon.

Base lemmas (C2):

* `expectedLoss_sub_weightedCumulative_le_externalRegret`
* `externalRegret_le_swapRegret`
* `externalRegret_add_roundConst`

Game layer (C3):

* `inducedLoss`: expected cost of an action against mixed opponents.
* `inducedLoss_nonneg`
* `inducedLoss_le_one`

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

/-- Expected loss of the played distributions against the losses.
(C1 base defs) -/
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

/-- Average regret: external regret divided by the horizon. The horizon
must be positive. (C1 base defs) -/
noncomputable def averageRegret [NeZero T] (play loss : Fin T → K → ℝ) : ℝ :=
  externalRegret play loss / (T : ℝ)

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- Expected cost of playing `a` against the other players' independent mixed
strategies. This is `CorrelatedEquilibrium.pureCost`. (C3 game layer) -/
def inducedLoss (cost : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ) (i : ι)
    (a : S i) : ℝ :=
  MathlibExt.GameTheory.CorrelatedEquilibrium.pureCost cost σ i a

/-- The induced loss as the cost weighted by the opponents' mixed play,
summed over profiles where player `i` plays `a`. -/
theorem inducedLoss_eq_sum_filter (cost : ι → (∀ i, S i) → ℝ)
    (σ : ∀ i, S i → ℝ) (i : ι) (a : S i) :
    inducedLoss cost σ i a
      = ∑ s ∈ Finset.univ.filter (fun s : ∀ j, S j => s i = a),
        cost i s * ∏ j ∈ Finset.univ.erase i, σ j (s j) := by
  unfold inducedLoss MathlibExt.GameTheory.CorrelatedEquilibrium.pureCost
    MathlibExt.GameTheory.CorrelatedEquilibrium.othersWeight
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : s i = a
  · simp [h, mul_comm]
  · simp [h]

/-- Induced losses are nonnegative for nonnegative costs. (C3 game layer) -/
theorem inducedLoss_nonneg {cost : ι → (∀ i, S i) → ℝ} {σ : ∀ i, S i → ℝ}
    {i : ι} {a : S i} (hσ : ∀ j, j ≠ i → IsSimplex (σ j))
    (hcost : ∀ s, 0 ≤ cost i s) : 0 ≤ inducedLoss cost σ i a := by
  rw [inducedLoss_eq_sum_filter]
  refine Finset.sum_nonneg fun s _ => ?_
  refine mul_nonneg (hcost s) ?_
  refine Finset.prod_nonneg fun j hj => ?_
  obtain ⟨hjn, -⟩ := (isSimplex_iff _).mp (hσ j (Finset.mem_erase.mp hj).1)
  exact hjn _

/-- Induced losses are at most one for [0,1] costs. (C3 game layer) -/
theorem inducedLoss_le_one {cost : ι → (∀ i, S i) → ℝ} {σ : ∀ i, S i → ℝ}
    {i : ι} {a : S i} (hσ : ∀ j, j ≠ i → IsSimplex (σ j))
    (hcost : ∀ s, cost i s ≤ 1) : inducedLoss cost σ i a ≤ 1 := by
  have hW : ∀ s : ∀ j, S j, 0 ≤ ∏ j ∈ Finset.univ.erase i, σ j (s j) := by
    intro s
    refine Finset.prod_nonneg fun j hj => ?_
    obtain ⟨hjn, -⟩ := (isSimplex_iff _).mp (hσ j (Finset.mem_erase.mp hj).1)
    exact hjn _
  have hBridge : Finset.univ.filter (fun s : ∀ j, S j => s i = a)
      = Fintype.piFinset (Function.update (fun _ => Finset.univ) i {a}) := by
    have hmem : a ∈ (fun _ => Finset.univ) i := Finset.mem_univ a
    have h := Fintype.piFinset_update_singleton_eq_filter_piFinset_eq
      (fun _ => Finset.univ) i hmem
    rw [Fintype.piFinset_univ] at h
    exact h.symm
  have hfib : ∀ j : ι, ∑ b ∈ Function.update (fun _ => Finset.univ) i {a} j,
      Function.update (fun j b => σ j b) i (fun _ => 1) j b = 1 := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, Function.update_self, Finset.sum_singleton]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      obtain ⟨-, hjsum⟩ := (isSimplex_iff _).mp (hσ j hj)
      exact hjsum
  have hLHS : ∏ j, ∑ b ∈ Function.update (fun _ => Finset.univ) i {a} j,
      Function.update (fun j b => σ j b) i (fun _ => 1) j b = 1 :=
    Finset.prod_eq_one fun j _ => hfib j
  have hRHS : (∑ x ∈ Fintype.piFinset
        (Function.update (fun _ => Finset.univ) i {a}),
        ∏ j, Function.update (fun j b => σ j b) i (fun _ => 1) j (x j))
      = ∑ x ∈ Fintype.piFinset (Function.update (fun _ => Finset.univ) i {a}),
        ∏ j ∈ Finset.univ.erase i, σ j (x j) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have hfi : Function.update (fun j b => σ j b) i (fun _ => 1) i (x i) = 1 := by
      simp only [Function.update_self]
    have hrest : (∏ j ∈ Finset.univ.erase i,
          Function.update (fun j b => σ j b) i (fun _ => 1) j (x j))
        = ∏ j ∈ Finset.univ.erase i, σ j (x j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Finset.mem_erase] at hj
      simp only [Function.update_of_ne hj.1]
    have hsplit : (∏ j, Function.update (fun j b => σ j b) i (fun _ => 1) j (x j))
        = (∏ j ∈ Finset.univ.erase i,
            Function.update (fun j b => σ j b) i (fun _ => 1) j (x j))
          * Function.update (fun j b => σ j b) i (fun _ => 1) i (x i) :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    rw [hsplit, hrest, hfi, mul_one]
  have hkey := Finset.prod_univ_sum
    (Function.update (fun _ => Finset.univ) i {a})
    (Function.update (fun j b => σ j b) i (fun _ => 1))
  have hsum : ∑ x ∈ Fintype.piFinset
      (Function.update (fun _ => Finset.univ) i {a}),
      ∏ j ∈ Finset.univ.erase i, σ j (x j) = 1 := by
    rw [← hRHS, ← hkey]
    exact hLHS
  rw [inducedLoss_eq_sum_filter]
  rw [hBridge, ← hsum]
  refine Finset.sum_le_sum fun s _ => ?_
  calc cost i s * ∏ j ∈ Finset.univ.erase i, σ j (s j)
      ≤ 1 * ∏ j ∈ Finset.univ.erase i, σ j (s j) :=
        mul_le_mul_of_nonneg_right (hcost s) (hW s)
    _ = ∏ j ∈ Finset.univ.erase i, σ j (s j) := one_mul _

end MathlibExt.GameTheory.Regret
