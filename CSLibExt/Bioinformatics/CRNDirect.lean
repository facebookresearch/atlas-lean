/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.PolynomialNetworks.Deficiency
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section

namespace Cslib.Bioinformatics.CRN

open Classical

open Finset

open MathlibExt.Biology.Dynamics.ComplexBalanced

/-!
# Chemical reaction networks: Gillespie direct method (abstract)

Abstract formalization of the classical stochastic simulation algorithm (SSA)
direct method as a deterministic function of uniform inputs, following
Gillespie, D. T. "Exact stochastic simulation of coupled chemical reactions."
Journal of Physical Chemistry 81(25), 1977.

Reactions are indexed by a type `ρ` over a `ReactionNetwork` (reactant and
product stoichiometries `src`/`prod`) with a separate rate function
`k : ρ → ℝ`. This layer covers only the combinatorial core: mass-action
propensities, the firing update, and the direct-method step
`(waiting time, reaction, new state)` as a function of two uniform draws.
Explicit non-goals: measure theory, continuous-time Markov chain path laws,
and tau-leaping or other approximations.

The propensity and firing update below agree definitionally with
`MathlibExt.Biology.Dynamics.SystemsBiology.propensity` and
`MathlibExt.Biology.Dynamics.SystemsBiology.fire` (Anderson-Craciun-Kurtz
convention: the rate constant absorbs the factorial, so there is no division).
-/

/-- Mass-action stochastic propensity
`a(N, k, r, x) = k r * ∏ s, descFactorial (x s) (N.src r s)`
(Anderson-Craciun-Kurtz convention: no division by factorials). -/
noncomputable def propensity {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (r : ρ) (x : S → ℕ) : ℝ :=
  k r * ∏ s, ((x s).descFactorial (N.src r s) : ℝ)

/-- State update `fire N r x = x - src + prod`, componentwise. Subtraction is
truncated (`Nat`), which is harmless because `propensity_eq_zero_of_insufficient`
shows the propensity vanishes whenever some reactant count exceeds the state,
so firing is only ever applied where the subtraction is exact. -/
def fire {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (r : ρ) (x : S → ℕ) : S → ℕ :=
  fun s => x s - N.src r s + N.prod r s

theorem propensity_nonneg {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 ≤ k r)
    (r : ρ) (x : S → ℕ) : 0 ≤ propensity N k r x := by
  unfold propensity
  exact mul_nonneg (hk r)
    (Finset.prod_nonneg (fun s _ => Nat.cast_nonneg _))

theorem propensity_eq_zero_of_insufficient {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (r : ρ) (x : S → ℕ)
    (s : S) (h : x s < N.src r s) :
    propensity N k r x = 0 := by
  unfold propensity
  have hfactor : ((x s).descFactorial (N.src r s) : ℝ) = 0 := by
    rw [Nat.descFactorial_of_lt h, Nat.cast_zero]
  have hprod :
      (∏ t, ((x t).descFactorial (N.src r t) : ℝ)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ s) hfactor
  rw [hprod, mul_zero]

/-- Total propensity `a0`: sum of propensities over a finite reaction list. -/
noncomputable def totalPropensity {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (rs : List ρ)
    (x : S → ℕ) : ℝ :=
  (rs.map (fun r => propensity N k r x)).sum

theorem totalPropensity_nonneg {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 ≤ k r)
    (rs : List ρ) (x : S → ℕ) : 0 ≤ totalPropensity N k rs x := by
  unfold totalPropensity
  induction rs with
  | nil => simp
  | cons r rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (propensity_nonneg N k hk r x) ih

theorem totalPropensity_eq_zero_iff {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 ≤ k r)
    (rs : List ρ) (x : S → ℕ) :
    totalPropensity N k rs x = 0 ↔ ∀ r ∈ rs, propensity N k r x = 0 := by
  unfold totalPropensity
  constructor
  · intro h r hr
    have hnonneg : ∀ y ∈ rs.map (fun r => propensity N k r x), 0 ≤ y := by
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨a, _, rfl⟩ := hy
      exact propensity_nonneg N k hk a x
    have hmem : propensity N k r x ∈ rs.map (fun r => propensity N k r x) := by
      rw [List.mem_map]
      exact ⟨r, hr, rfl⟩
    exact List.all_zero_of_le_zero_le_of_sum_eq_zero hnonneg h hmem
  · intro h
    apply List.sum_eq_zero
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact h a ha

/-- First reaction whose cumulative propensity reaches `thresh`, by recursion
over the list (upper-inclusive inverse CDF, Gillespie 1977 direct method):
selects the first index with `thresh ≤ cumulative` and positive propensity.
Total: returns `none` on `[]` or when the threshold is never reached (in
particular when `u2 * a0 > a0`, i.e. `u2 > 1` with `a0 > 0`; a nonpositive
threshold selects the first positive-propensity reaction). -/
noncomputable def selectAux {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (rs : List ρ) (x : S → ℕ)
    (thresh : ℝ) : Option ρ :=
  match rs with
  | [] => none
  | r :: rest =>
    if thresh ≤ propensity N k r x ∧ 0 < propensity N k r x then some r
    else selectAux N k rest x (thresh - propensity N k r x)

theorem selectAux_nil {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (x : S → ℕ) (thresh : ℝ) :
    selectAux N k ([] : List ρ) x thresh = none := rfl

theorem selectAux_cons {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ)
    (r : ρ) (rest : List ρ) (x : S → ℕ) (thresh : ℝ) :
    selectAux N k (r :: rest) x thresh =
      (if thresh ≤ propensity N k r x ∧ 0 < propensity N k r x then some r
        else selectAux N k rest x (thresh - propensity N k r x)) := rfl

/-- Selection soundness: a selected reaction has positive propensity, for any
threshold (positivity follows from the selection condition alone). -/
theorem selectAux_some_pos {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ)
    (rs : List ρ) (x : S → ℕ) (thresh : ℝ) (r : ρ)
    (hsel : selectAux N k rs x thresh = some r) :
    0 < propensity N k r x := by
  induction rs generalizing thresh r with
  | nil =>
    rw [selectAux_nil] at hsel
    simp at hsel
  | cons head rest ih =>
    rw [selectAux_cons] at hsel
    by_cases hcond : thresh ≤ propensity N k head x ∧ 0 < propensity N k head x
    · rw [ite_eq_left hcond] at hsel
      have h_eq : head = r := Option.some_inj.mp hsel
      subst h_eq
      exact hcond.2
    · rw [ite_eq_right hcond] at hsel
      exact ih _ _ hsel

/-- A selected reaction comes from the reaction list. -/
theorem selectAux_mem {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ)
    (rs : List ρ) (x : S → ℕ) (thresh : ℝ) (r : ρ)
    (hsel : selectAux N k rs x thresh = some r) : r ∈ rs := by
  induction rs generalizing thresh with
  | nil =>
    rw [selectAux_nil] at hsel
    simp at hsel
  | cons head rest ih =>
    rw [selectAux_cons] at hsel
    by_cases hcond : thresh ≤ propensity N k head x ∧ 0 < propensity N k head x
    · rw [ite_eq_left hcond] at hsel
      have h_eq : head = r := Option.some_inj.mp hsel
      subst h_eq
      exact List.mem_cons_self
    · rw [ite_eq_right hcond] at hsel
      exact List.mem_cons_of_mem _ (ih _ hsel)

/-- Direct-method step as a function of uniforms `u1 u2`, with draw domains
`0 < u1 ≤ 1` and `0 < u2 ≤ 1`: `none` when `a0 = 0` (absorbing); otherwise
`(τ, r, fire N r x)` with `τ = log (1 / u1) / a0` and `r` the first reaction
whose cumulative propensity reaches `u2 * a0` (upper-inclusive inverse CDF).
Out-of-range `u2`: `u2 ≤ 0` selects the first positive-propensity reaction
(a threshold at or below zero is reached immediately); `u2 > 1` yields `none`
(a threshold above the total is never reached). -/
noncomputable def step {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (rs : List ρ) (x : S → ℕ)
    (u1 u2 : ℝ) : Option (ℝ × ρ × (S → ℕ)) :=
  let a0 := totalPropensity N k rs x
  if a0 = 0 then none
  else
    match selectAux N k rs x (u2 * a0) with
    | none => none
    | some r => some (Real.log (1 / u1) / a0, r, fire N r x)

theorem step_eq {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (rs : List ρ) (x : S → ℕ)
    (u1 u2 : ℝ) :
    step N k rs x u1 u2 =
      (if totalPropensity N k rs x = 0 then none
        else match selectAux N k rs x (u2 * totalPropensity N k rs x) with
          | none => none
          | some r =>
            some (Real.log (1 / u1) / totalPropensity N k rs x, r,
              fire N r x)) := rfl

/-- Soundness core: a successful step with `0 < u1 ≤ 1` and `0 < u2 ≤ 1`
yields a nonnegative waiting time and a reaction with positive propensity.
(The `u2` bounds are part of the interface, since `u2` is an upper-inclusive
inverse-CDF draw; soundness only needs selection to have succeeded.) -/
theorem step_some_sound {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 ≤ k r)
    (rs : List ρ) (x : S → ℕ) (u1 u2 τ : ℝ) (r : ρ) (x' : S → ℕ)
    (h1 : 0 < u1) (hu1 : u1 ≤ 1) (_h2a : 0 < u2) (_h2b : u2 ≤ 1)
    (hstep : step N k rs x u1 u2 = some (τ, r, x')) :
    0 ≤ τ ∧ 0 < propensity N k r x ∧ x' = fire N r x := by
  rw [step_eq] at hstep
  by_cases ha0 : totalPropensity N k rs x = 0
  · rw [ite_eq_left ha0] at hstep
    simp at hstep
  · rw [ite_eq_right ha0] at hstep
    cases hsel : selectAux N k rs x (u2 * totalPropensity N k rs x) with
    | none =>
      rw [hsel] at hstep
      simp at hstep
    | some r' =>
      rw [hsel] at hstep
      have htuple :
          (Real.log (1 / u1) / totalPropensity N k rs x, r', fire N r' x)
            = (τ, r, x') :=
        Option.some_inj.mp hstep
      rw [Prod.mk.injEq] at htuple
      obtain ⟨hτ, hmid⟩ := htuple
      rw [Prod.mk.injEq] at hmid
      obtain ⟨hr, hx⟩ := hmid
      rw [hr] at hsel
      rw [hr] at hx
      have ha0pos : 0 < totalPropensity N k rs x :=
        lt_of_le_of_ne (totalPropensity_nonneg N k hk rs x) (Ne.symm ha0)
      have hpos : 0 < propensity N k r x :=
        selectAux_some_pos N k rs x (u2 * totalPropensity N k rs x) r hsel
      have hlog : 0 ≤ Real.log (1 / u1) :=
        Real.log_nonneg (one_le_one_div h1 hu1)
      have hdiv : 0 ≤ Real.log (1 / u1) / totalPropensity N k rs x :=
        div_nonneg hlog (le_of_lt ha0pos)
      rw [← hτ]
      exact ⟨hdiv, hpos, hx.symm⟩

/-- Absorbing: the empty reaction list never fires. -/
theorem step_none_of_empty {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (x : S → ℕ) (u1 u2 : ℝ) :
    step N k ([] : List ρ) x u1 u2 = none := by
  rw [step_eq]
  simp [totalPropensity]

end Cslib.Bioinformatics.CRN
