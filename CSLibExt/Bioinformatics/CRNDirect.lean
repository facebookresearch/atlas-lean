/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.PolynomialNetworks.StochasticMassAction
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section

namespace Cslib.Bioinformatics.CRN

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

Propensities and firing updates are `ReactionNetwork.propensity` and
`ReactionNetwork.fire` from
`MathlibExt.Dynamics.PolynomialNetworks.StochasticMassAction` (the same
constants the SystemsBiology development uses; Anderson-Craciun-Kurtz
convention: the rate constant absorbs the factorial, so there is no division).
Their basic facts, `ReactionNetwork.propensity_nonneg` and
`ReactionNetwork.propensity_eq_zero_of_not_le`, come from the same shared module.
-/

/-- Total propensity `a0`: sum of propensities over a finite reaction list. -/
noncomputable def totalPropensity {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (rs : List ρ)
    (x : S → ℕ) : ℝ :=
  (rs.map (fun r => N.propensity k r x)).sum

theorem totalPropensity_nonneg {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 ≤ k r)
    (rs : List ρ) (x : S → ℕ) : 0 ≤ totalPropensity N k rs x := by
  unfold totalPropensity
  induction rs with
  | nil => simp
  | cons r rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (N.propensity_nonneg hk r x) ih

theorem totalPropensity_eq_zero_iff {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 ≤ k r)
    (rs : List ρ) (x : S → ℕ) :
    totalPropensity N k rs x = 0 ↔ ∀ r ∈ rs, N.propensity k r x = 0 := by
  unfold totalPropensity
  constructor
  · intro h r hr
    have hnonneg : ∀ y ∈ rs.map (fun r => N.propensity k r x), 0 ≤ y := by
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨a, _, rfl⟩ := hy
      exact N.propensity_nonneg hk a x
    have hmem : N.propensity k r x ∈ rs.map (fun r => N.propensity k r x) := by
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
Total: returns `none` on `[]`. For nonnegative rates (`0 ≤ k r` for all `r`),
a threshold above the total propensity is never reached (`none`; in
particular `u2 * a0 > a0`, i.e. `u2 > 1` with `a0 > 0`), while a positive
threshold at or below the total always selects a reaction. Neither threshold
claim holds for general (possibly negative) rates. -/
noncomputable def selectAux {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (rs : List ρ) (x : S → ℕ)
    (thresh : ℝ) : Option ρ :=
  match rs with
  | [] => none
  | r :: rest =>
    if thresh ≤ N.propensity k r x ∧ 0 < N.propensity k r x then some r
    else selectAux N k rest x (thresh - N.propensity k r x)

theorem selectAux_nil {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (x : S → ℕ) (thresh : ℝ) :
    selectAux N k ([] : List ρ) x thresh = none := rfl

theorem selectAux_cons {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ)
    (r : ρ) (rest : List ρ) (x : S → ℕ) (thresh : ℝ) :
    selectAux N k (r :: rest) x thresh =
      (if thresh ≤ N.propensity k r x ∧ 0 < N.propensity k r x then some r
        else selectAux N k rest x (thresh - N.propensity k r x)) := rfl

/-- Selection soundness: a selected reaction has positive propensity, for any
threshold (positivity follows from the selection condition alone). -/
theorem selectAux_some_pos {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ)
    (rs : List ρ) (x : S → ℕ) (thresh : ℝ) (r : ρ)
    (hsel : selectAux N k rs x thresh = some r) :
    0 < N.propensity k r x := by
  induction rs generalizing thresh r with
  | nil =>
    rw [selectAux_nil] at hsel
    simp at hsel
  | cons head rest ih =>
    rw [selectAux_cons] at hsel
    by_cases hcond : thresh ≤ N.propensity k head x ∧ 0 < N.propensity k head x
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
    by_cases hcond : thresh ≤ N.propensity k head x ∧ 0 < N.propensity k head x
    · rw [ite_eq_left hcond] at hsel
      have h_eq : head = r := Option.some_inj.mp hsel
      subst h_eq
      exact List.mem_cons_self
    · rw [ite_eq_right hcond] at hsel
      exact List.mem_cons_of_mem _ (ih _ hsel)

/-- For nonnegative rates, a threshold above the total propensity is never
reached: selection returns `none`. -/
theorem selectAux_none_of_total_lt {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 ≤ k r)
    (rs : List ρ) (x : S → ℕ) (thresh : ℝ)
    (h : totalPropensity N k rs x < thresh) :
    selectAux N k rs x thresh = none := by
  induction rs generalizing thresh with
  | nil => rw [selectAux_nil]
  | cons head rest ih =>
    rw [selectAux_cons]
    have hrest : 0 ≤ totalPropensity N k rest x :=
      totalPropensity_nonneg N k hk rest x
    have htotal : totalPropensity N k (head :: rest) x
        = N.propensity k head x + totalPropensity N k rest x := by
      simp [totalPropensity]
    rw [htotal] at h
    by_cases hcond :
      thresh ≤ N.propensity k head x ∧ 0 < N.propensity k head x
    · exfalso
      have h2 : N.propensity k head x + totalPropensity N k rest x
          < N.propensity k head x + 0 := by
        rw [add_zero]
        exact lt_of_lt_of_le h hcond.1
      have h3 : totalPropensity N k rest x < 0 :=
        lt_of_add_lt_add_left h2
      exact (not_lt_of_ge hrest) h3
    · rw [ite_eq_right hcond]
      apply ih
      have h4 : totalPropensity N k rest x + N.propensity k head x
          < thresh := by
        rwa [add_comm (totalPropensity N k rest x)
          (N.propensity k head x)]
      exact lt_sub_iff_add_lt.mpr h4

/-- For nonnegative rates, a positive threshold at or below the total
propensity always selects a reaction. -/
theorem selectAux_some_of_le_total {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 ≤ k r)
    (rs : List ρ) (x : S → ℕ) (thresh : ℝ)
    (hpos : 0 < thresh) (hle : thresh ≤ totalPropensity N k rs x) :
    ∃ r, selectAux N k rs x thresh = some r := by
  induction rs generalizing thresh with
  | nil =>
    exfalso
    have h0 : totalPropensity N k ([] : List ρ) x = 0 := by simp [totalPropensity]
    rw [h0] at hle
    exact (not_lt_of_ge hle) hpos
  | cons head rest ih =>
    rw [selectAux_cons]
    by_cases hcond :
      thresh ≤ N.propensity k head x ∧ 0 < N.propensity k head x
    · rw [ite_eq_left hcond]
      exact ⟨head, rfl⟩
    · rw [ite_eq_right hcond]
      have htotal : totalPropensity N k (head :: rest) x
          = N.propensity k head x + totalPropensity N k rest x := by
        simp [totalPropensity]
      rw [htotal] at hle
      have hle2 : thresh - N.propensity k head x
          ≤ totalPropensity N k rest x := by
        rw [sub_le_iff_le_add]
        calc thresh
            ≤ N.propensity k head x + totalPropensity N k rest x := hle
          _ = totalPropensity N k rest x + N.propensity k head x :=
            add_comm _ _
      have hpos2 : 0 < thresh - N.propensity k head x := by
        by_cases ha : 0 < N.propensity k head x
        · have hnge : ¬ thresh ≤ N.propensity k head x :=
            fun hle'' => hcond ⟨hle'', ha⟩
          have hlt : N.propensity k head x < thresh :=
            lt_of_not_ge hnge
          rw [sub_pos]
          exact hlt
        · have hale : N.propensity k head x ≤ 0 := le_of_not_gt ha
          have h0 : N.propensity k head x = 0 :=
            le_antisymm hale (N.propensity_nonneg hk head x)
          rw [h0, sub_zero]
          exact hpos
      exact ih _ hpos2 hle2

/-- Direct-method step as a function of uniforms `u1 u2`, with draw domains
`0 < u1 ≤ 1` and `0 < u2 ≤ 1`: `step` is `none` when the total weight `a0` is
zero. For nonnegative rates (`0 ≤ k r` for all `r`), a zero total means every
listed reaction has zero propensity (`totalPropensity_eq_zero_iff`), an
absorbing state; with in-range draws `none` happens exactly there
(`step_eq_none_iff`). For signed rates the total can cancel to zero while a
listed reaction has positive propensity, so `none` then records only the zero
total. For nonnegative rates (`0 ≤ k r` for all `r`), a positive total gives
`(τ, r, N.fire r x)` with `τ = log (1 / u1) / a0` and `r` the first reaction
whose cumulative propensity reaches `u2 * a0` (upper-inclusive inverse CDF).
Out-of-range `u2` (nonnegative rates, positive total): `u2 ≤ 0` selects the
first positive-propensity reaction (a threshold at or below zero is reached
immediately); `u2 > 1` yields `none` (a threshold above the total is never
reached). -/
noncomputable def step {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (rs : List ρ) (x : S → ℕ)
    (u1 u2 : ℝ) : Option (ℝ × ρ × (S → ℕ)) :=
  let a0 := totalPropensity N k rs x
  if a0 = 0 then none
  else
    match selectAux N k rs x (u2 * a0) with
    | none => none
    | some r => some (Real.log (1 / u1) / a0, r, N.fire r x)

theorem step_eq {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (rs : List ρ) (x : S → ℕ)
    (u1 u2 : ℝ) :
    step N k rs x u1 u2 =
      (if totalPropensity N k rs x = 0 then none
        else match selectAux N k rs x (u2 * totalPropensity N k rs x) with
          | none => none
          | some r =>
            some (Real.log (1 / u1) / totalPropensity N k rs x, r,
              N.fire r x)) := rfl

/-- Soundness core: a successful step with `0 < u1 ≤ 1` and `0 < u2 ≤ 1`
yields a nonnegative waiting time and a reaction with positive propensity.
(The `u2` bounds are part of the interface, since `u2` is an upper-inclusive
inverse-CDF draw; soundness only needs selection to have succeeded.) -/
theorem step_some_sound {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 ≤ k r)
    (rs : List ρ) (x : S → ℕ) (u1 u2 τ : ℝ) (r : ρ) (x' : S → ℕ)
    (h1 : 0 < u1) (hu1 : u1 ≤ 1) (_h2a : 0 < u2) (_h2b : u2 ≤ 1)
    (hstep : step N k rs x u1 u2 = some (τ, r, x')) :
    0 ≤ τ ∧ 0 < N.propensity k r x ∧ x' = N.fire r x := by
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
          (Real.log (1 / u1) / totalPropensity N k rs x, r', N.fire r' x)
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
      have hpos : 0 < N.propensity k r x :=
        selectAux_some_pos N k rs x (u2 * totalPropensity N k rs x) r hsel
      have hlog : 0 ≤ Real.log (1 / u1) :=
        Real.log_nonneg (one_le_one_div h1 hu1)
      have hdiv : 0 ≤ Real.log (1 / u1) / totalPropensity N k rs x :=
        div_nonneg hlog (le_of_lt ha0pos)
      rw [← hτ]
      exact ⟨hdiv, hpos, hx.symm⟩

/-- For nonnegative rates, in-range uniforms with a positive total always
step: some waiting time, reaction, and fired state. -/
theorem step_some_of_pos {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 ≤ k r)
    (rs : List ρ) (x : S → ℕ) (u1 u2 : ℝ)
    (_h1 : 0 < u1) (_hu1 : u1 ≤ 1) (h2a : 0 < u2) (h2b : u2 ≤ 1)
    (ha0 : 0 < totalPropensity N k rs x) :
    ∃ τ r, step N k rs x u1 u2 = some (τ, r, N.fire r x) := by
  rw [step_eq]
  have ha0ne : totalPropensity N k rs x ≠ 0 := ne_of_gt ha0
  rw [ite_eq_right ha0ne]
  have hthresh_pos : 0 < u2 * totalPropensity N k rs x :=
    mul_pos h2a ha0
  have hthresh_le : u2 * totalPropensity N k rs x
      ≤ totalPropensity N k rs x := by
    have hmul : u2 * totalPropensity N k rs x
        ≤ 1 * totalPropensity N k rs x :=
      mul_le_mul_of_nonneg_right h2b (le_of_lt ha0)
    rwa [one_mul] at hmul
  obtain ⟨r, hsel⟩ :=
    selectAux_some_of_le_total N k hk rs x _ hthresh_pos hthresh_le
  rw [hsel]
  exact ⟨_, _, rfl⟩

/-- For nonnegative rates and `0 < u2 ≤ 1`, `step` is `none` exactly when
every listed reaction has zero propensity, an absorbing state. -/
theorem step_eq_none_iff {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 ≤ k r)
    (rs : List ρ) (x : S → ℕ) (u1 u2 : ℝ) (h2a : 0 < u2) (h2b : u2 ≤ 1) :
    step N k rs x u1 u2 = none ↔ ∀ r ∈ rs, N.propensity k r x = 0 := by
  rw [step_eq]
  constructor
  · intro h
    by_cases htotal : totalPropensity N k rs x = 0
    · exact (totalPropensity_eq_zero_iff N k hk rs x).mp htotal
    · have hpos : 0 < totalPropensity N k rs x :=
        lt_of_le_of_ne (totalPropensity_nonneg N k hk rs x) (Ne.symm htotal)
      have hle : u2 * totalPropensity N k rs x ≤ totalPropensity N k rs x :=
        mul_le_of_le_one_left hpos.le h2b
      obtain ⟨r, hr⟩ := selectAux_some_of_le_total N k hk rs x _
        (mul_pos h2a hpos) hle
      rw [ite_eq_right htotal] at h
      simp [hr] at h
  · intro h
    have htotal : totalPropensity N k rs x = 0 :=
      (totalPropensity_eq_zero_iff N k hk rs x).mpr h
    rw [htotal, ite_eq_left rfl]

/-- Absorbing: the empty reaction list never fires. -/
theorem step_none_of_empty {S ρ : Type*} [Fintype S]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (x : S → ℕ) (u1 u2 : ℝ) :
    step N k ([] : List ρ) x u1 u2 = none := by
  rw [step_eq]
  simp [totalPropensity]

end Cslib.Bioinformatics.CRN
