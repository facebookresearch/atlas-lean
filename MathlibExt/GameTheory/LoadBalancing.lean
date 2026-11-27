/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# Selfish load balancing on identical machines

The load balancing game (the "KP model" of Koutsoupias and Papadimitriou, 1999): each task
`i` of weight `wᵢ ≥ 0` is a selfish agent that chooses one of `m` identical machines; an
assignment `A` gives machine `j` the load `ℓⱼ = ∑_{A(i) = j} wᵢ`, the cost of agent `i` is the
load of its machine, and the social cost is the makespan `maxⱼ ℓⱼ`. Koutsoupias and
Papadimitriou introduced the *coordination ratio*, now called the price of anarchy: the worst
ratio between the social cost of a Nash equilibrium and the optimum.

This module treats pure equilibria on identical machines, following B. Vöcking, "Selfish load
balancing", Chapter 20 of *Algorithmic Game Theory* (Nisan, Roughgarden, Tardos, Vazirani eds.,
Cambridge University Press 2007): the characterisation of pure Nash equilibria
(Proposition 20.2) and the price-of-anarchy bound `2 - 2/(m+1)` (Theorem 20.5). The mixed
equilibria studied in Koutsoupias and Papadimitriou's paper (expected makespan, the
`Θ(log m / log log m)` bounds of Theorems 20.12 and 20.13) are not formalised.

## References

* E. Koutsoupias, C. H. Papadimitriou, "Worst-case equilibria", Proc. 16th STACS (1999),
  404–413 (not consulted directly; content as reported in the chapter below, Section 20.7).
* B. Vöcking, "Selfish load balancing", in *Algorithmic Game Theory*, Cambridge University
  Press 2007, Chapter 20, Sections 20.1–20.2.
-/

@[expose] public section

namespace MathlibExt.GameTheory.LoadBalancing

open Finset

variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- **Load of a machine.** Under the assignment `A` of tasks of weights `w` to the machines
`Fin m`, the load of machine `j` is the total weight `∑_{A(i) = j} wᵢ` of the tasks placed on it
(identical machines of speed `1`; Vöcking, *Algorithmic Game Theory*, Chapter 20,
Section 20.1). -/
def load (w : ι → ℝ) (A : ι → Fin m) (j : Fin m) : ℝ :=
  ∑ i ∈ univ.filter (fun i => A i = j), w i

/-- **Makespan.** The social cost of an assignment: the maximum load over the (at least one)
machines (Vöcking, *Algorithmic Game Theory*, Chapter 20, Section 20.1.1). -/
def makespan [NeZero m] (w : ι → ℝ) (A : ι → Fin m) : ℝ :=
  univ.sup' univ_nonempty (load w A)

/-- **Pure Nash equilibrium of the load balancing game.** No task can lower its cost by moving
alone: for every task `i` and every other machine `k`, the load of `i`'s machine is at most the
load `ℓₖ + wᵢ` that `i` would experience on `k` (Vöcking, *Algorithmic Game Theory*,
Proposition 20.2, specialised to identical machines). -/
def IsPureNash (w : ι → ℝ) (A : ι → Fin m) : Prop :=
  ∀ i (k : Fin m), k ≠ A i → load w A (A i) ≤ load w A k + w i

/-- **Loads are nonnegative.** With nonnegative weights every machine load is nonnegative. -/
theorem load_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (A : ι → Fin m) (j : Fin m) :
    0 ≤ load w A j :=
  sum_nonneg (fun i _ => hw i)

/-- **Every load is at most the makespan.** The makespan is the maximum of the machine loads,
so it bounds each of them. -/
theorem load_le_makespan [NeZero m] (w : ι → ℝ) (A : ι → Fin m) (j : Fin m) :
    load w A j ≤ makespan w A :=
  le_sup' (load w A) (mem_univ j)

/-- **Loads add up to the total weight.** For every assignment, `∑ⱼ ℓⱼ = ∑ᵢ wᵢ`. -/
theorem sum_load (w : ι → ℝ) (A : ι → Fin m) : ∑ j, load w A j = ∑ i, w i := by
  unfold load
  exact sum_fiberwise univ A w

/-- **Average load bound.** Every assignment has makespan at least the average load:
`∑ᵢ wᵢ ≤ m · makespan(B)` (the lower bound on the optimum used in the proof of Vöcking,
*Algorithmic Game Theory*, Theorem 20.5). -/
theorem sum_weight_le_mul_makespan [NeZero m] (w : ι → ℝ) (B : ι → Fin m) :
    ∑ i, w i ≤ m * makespan w B := by
  rw [← sum_load]
  calc ∑ j, load w B j ≤ ∑ _j : Fin m, makespan w B :=
        sum_le_sum (fun j _ => load_le_makespan w B j)
    _ = m * makespan w B := by simp

/-- **A single task bounds every makespan.** For nonnegative weights, `wᵢ ≤ makespan(B)` for
every task `i` and assignment `B`. -/
theorem weight_le_makespan [NeZero m] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (B : ι → Fin m) (i : ι) :
    w i ≤ makespan w B := by
  refine le_trans ?_ (load_le_makespan w B (B i))
  exact single_le_sum (f := w) (fun k _ => hw k) (by simp)

/-- **Price of anarchy for pure equilibria on identical machines (multiplicative form).**
Let `m ≥ 1` identical machines and nonnegative task weights `w` be given. If `A` is a pure Nash
equilibrium and `B` is any assignment, then `(m + 1) · makespan(A) ≤ 2m · makespan(B)`.

Proof (Vöcking, *Algorithmic Game Theory*, Theorem 20.5): let `j*` carry the maximal load
`C`. If at most one task sits on `j*`, then `C` is at most one weight, hence at most
`makespan(B)`. Otherwise some task `i*` on `j*` has `wᵢ* ≤ C/2`, and the equilibrium condition
for `i*` forces every other machine to carry load at least `C - wᵢ* ≥ C/2`; so the total
weight is at least `(m + 1) C / 2`, while it is at most `m · makespan(B)`. -/
theorem succ_mul_makespan_le [NeZero m] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {A : ι → Fin m}
    (hA : IsPureNash w A) (B : ι → Fin m) :
    ((m : ℝ) + 1) * makespan w A ≤ 2 * m * makespan w B := by
  classical
  have hm : (1 : ℝ) ≤ m := by
    have := NeZero.pos m
    exact_mod_cast this
  obtain ⟨jstar, -, hjstar⟩ := exists_max_image univ (load w A) univ_nonempty
  have hC : makespan w A = load w A jstar :=
    le_antisymm (sup'_le _ _ (fun j _ => hjstar j (mem_univ j)))
      (load_le_makespan w A jstar)
  set C := load w A jstar with hCdef
  have hBnn : 0 ≤ makespan w B :=
    le_trans (load_nonneg hw B 0) (load_le_makespan w B 0)
  by_cases htwo : ∃ i₁ i₂, i₁ ≠ i₂ ∧ A i₁ = jstar ∧ A i₂ = jstar
  · obtain ⟨i₁, i₂, hne, h₁, h₂⟩ := htwo
    -- the lighter of the two tasks
    obtain ⟨istar, hiA, hiw⟩ : ∃ i, A i = jstar ∧ 2 * w i ≤ C := by
      have hpair : w i₁ + w i₂ ≤ C := by
        have hsub : ({i₁, i₂} : Finset ι) ⊆ univ.filter (fun i => A i = jstar) := by
          intro i hi
          simp only [mem_insert, mem_singleton] at hi
          rcases hi with rfl | rfl <;> simp [h₁, h₂]
        have := sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hw i)
        rwa [sum_pair hne] at this
      rcases le_total (w i₁) (w i₂) with h | h
      · exact ⟨i₁, h₁, by linarith⟩
      · exact ⟨i₂, h₂, by linarith⟩
    have hothers : ∀ j ∈ univ.erase jstar, C - w istar ≤ load w A j := by
      intro j hj
      have hj' : j ≠ A istar := by rw [hiA]; exact ne_of_mem_erase hj
      have := hA istar j hj'
      rw [hiA] at this
      linarith
    have htotal : C + ((m : ℝ) - 1) * (C - w istar) ≤ ∑ i, w i := by
      rw [← sum_load, ← add_sum_erase univ (load w A) (mem_univ jstar)]
      have hsum := sum_le_sum hothers
      rw [sum_const, card_erase_of_mem (mem_univ jstar), card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hsum
      have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (NeZero.one_le)]
        simp
      rw [hcast] at hsum
      linarith
    have hopt := sum_weight_le_mul_makespan w B
    rw [hC]
    nlinarith [mul_le_mul_of_nonneg_left (show C ≤ 2 * (C - w istar) by linarith)
      (show (0 : ℝ) ≤ (m : ℝ) - 1 by linarith)]
  · push Not at htwo
    have hCle : C ≤ makespan w B := by
      by_cases hex : ∃ i, A i = jstar
      · obtain ⟨i, hi⟩ := hex
        have hfib : univ.filter (fun k => A k = jstar) = {i} := by
          ext k
          simp only [mem_filter, mem_univ, true_and, mem_singleton]
          constructor
          · intro hk
            by_contra hki
            exact htwo k i hki hk hi
          · rintro rfl; exact hi
        have : C = w i := by rw [hCdef, load, hfib, sum_singleton]
        rw [this]
        exact weight_le_makespan hw B i
      · push Not at hex
        have : C = 0 := by
          rw [hCdef, load, filter_false_of_mem (fun k _ => hex k), sum_empty]
        rw [this]
        exact hBnn
    rw [hC]
    nlinarith [load_nonneg hw A jstar]

/-- **Price of anarchy for pure equilibria on identical machines.** For `m ≥ 1` identical
machines and nonnegative weights, every pure Nash equilibrium `A` has
`makespan(A) ≤ (2 - 2/(m + 1)) · makespan(B)` for every assignment `B`, in particular for an
optimal one.

Source: B. Vöcking, "Selfish load balancing", *Algorithmic Game Theory* (Cambridge University
Press 2007), Theorem 20.5. The bound is tight (Exercise 20.2 there; the two-machine instance of
Section 20.1.2 attains `4/3` and is checked in the test module). -/
theorem makespan_le_of_isPureNash [NeZero m] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {A : ι → Fin m} (hA : IsPureNash w A) (B : ι → Fin m) :
    makespan w A ≤ (2 - 2 / ((m : ℝ) + 1)) * makespan w B := by
  have h := succ_mul_makespan_le hw hA B
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hrw : (2 - 2 / ((m : ℝ) + 1)) = 2 * m / ((m : ℝ) + 1) := by
    field_simp
    ring
  rw [hrw, div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith

end MathlibExt.GameTheory.LoadBalancing
