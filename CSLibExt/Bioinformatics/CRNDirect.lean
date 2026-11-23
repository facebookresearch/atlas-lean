/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Cslib.Bioinformatics.CRN

open Classical

/-!
# Chemical reaction networks: Gillespie direct method (abstract)

Abstract formalization of the classical stochastic simulation algorithm (SSA)
direct method as a deterministic function of uniform inputs, following
Gillespie, D. T. "Exact stochastic simulation of coupled chemical reactions."
Journal of Physical Chemistry 81(25), 1977.

This layer covers only the combinatorial core: mass-action propensities, the
firing update, and the direct-method step `(waiting time, reaction, new state)`
as a function of two uniform draws. Explicit non-goals: measure theory,
continuous-time Markov chain path laws, and tau-leaping or other approximations.
-/

/-- A chemical reaction over species `S`: reactant and product stoichiometries
(`reactants`, `products`) and a nonnegative stochastic rate constant `k`. -/
structure Reaction (S : Type*) [Fintype S] where
  reactants : S → ℕ
  products : S → ℕ
  k : ℝ
  k_nonneg : 0 ≤ k

/-- Stochastic mass-action combinatorial factor for one species:
`C(n, m) = descFactorial n m / m!`, the number of ways to choose the `m`
reactant molecules from the `n` present. This equals `Nat.choose n m`. -/
noncomputable def combFactor (n m : ℕ) : ℝ :=
  (Nat.descFactorial n m : ℝ) / (Nat.factorial m : ℝ)

theorem combFactor_nonneg (n m : ℕ) : 0 ≤ combFactor n m := by
  unfold combFactor
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem combFactor_eq_zero_of_lt (n m : ℕ) (h : n < m) :
    combFactor n m = 0 := by
  unfold combFactor
  rw [Nat.descFactorial_of_lt h, Nat.cast_zero, zero_div]

/-- Mass-action stochastic propensity `a(r, x) = k * ∏ s, C(x s, ν⁻ s)`. -/
noncomputable def propensity {S : Type*} [Fintype S] (r : Reaction S) (x : S → ℕ) : ℝ :=
  r.k * Finset.prod Finset.univ (fun s => combFactor (x s) (r.reactants s))

/-- State update `fire r x = x - ν⁻ + ν⁺`, componentwise. Subtraction is
truncated (`Nat`), which is harmless because `propensity_eq_zero_of_insufficient`
shows the propensity vanishes whenever some reactant count exceeds the state,
so firing is only ever applied where the subtraction is exact. -/
def fire {S : Type*} [Fintype S] (r : Reaction S) (x : S → ℕ) : S → ℕ :=
  fun s => x s - r.reactants s + r.products s

theorem propensity_nonneg {S : Type*} [Fintype S] (r : Reaction S)
    (x : S → ℕ) : 0 ≤ propensity r x := by
  unfold propensity
  exact mul_nonneg r.k_nonneg
    (Finset.prod_nonneg (fun s _ => combFactor_nonneg _ _))

theorem propensity_eq_zero_of_insufficient {S : Type*} [Fintype S]
    (r : Reaction S) (x : S → ℕ) (s : S) (h : x s < r.reactants s) :
    propensity r x = 0 := by
  unfold propensity
  have hfactor : combFactor (x s) (r.reactants s) = 0 :=
    combFactor_eq_zero_of_lt _ _ h
  have hprod :
      Finset.prod Finset.univ (fun s => combFactor (x s) (r.reactants s)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ s) hfactor
  rw [hprod, mul_zero]

/-- Total propensity `a0`: sum of propensities over a finite reaction list. -/
noncomputable def totalPropensity {S : Type*} [Fintype S] (rs : List (Reaction S))
    (x : S → ℕ) : ℝ :=
  (rs.map (fun r => propensity r x)).sum

theorem totalPropensity_nonneg {S : Type*} [Fintype S] (rs : List (Reaction S))
    (x : S → ℕ) : 0 ≤ totalPropensity rs x := by
  unfold totalPropensity
  induction rs with
  | nil => simp
  | cons r rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (propensity_nonneg r x) ih

theorem totalPropensity_eq_zero_iff {S : Type*} [Fintype S]
    (rs : List (Reaction S)) (x : S → ℕ) :
    totalPropensity rs x = 0 ↔ ∀ r ∈ rs, propensity r x = 0 := by
  unfold totalPropensity
  constructor
  · intro h r hr
    have hnonneg : ∀ y ∈ rs.map (fun r => propensity r x), 0 ≤ y := by
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨a, _, rfl⟩ := hy
      exact propensity_nonneg a x
    have hmem : propensity r x ∈ rs.map (fun r => propensity r x) := by
      rw [List.mem_map]
      exact ⟨r, hr, rfl⟩
    exact List.all_zero_of_le_zero_le_of_sum_eq_zero hnonneg h hmem
  · intro h
    apply List.sum_eq_zero
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact h a ha

/-- First reaction whose cumulative propensity exceeds `thresh`, by recursion
over the list. Total: returns `none` on `[]` or when the threshold is never
exceeded (in particular when `u2 * a0 ≥ a0`, i.e. `u2 ≥ 1` with `a0 > 0`;
a negative threshold selects the head reaction). -/
noncomputable def selectAux {S : Type*} [Fintype S] (rs : List (Reaction S)) (x : S → ℕ)
    (thresh : ℝ) : Option (Reaction S) :=
  match rs with
  | [] => none
  | r :: rest =>
    if thresh < propensity r x then some r
    else selectAux rest x (thresh - propensity r x)

theorem selectAux_nil {S : Type*} [Fintype S] (x : S → ℕ) (thresh : ℝ) :
    selectAux ([] : List (Reaction S)) x thresh = none := rfl

theorem selectAux_cons {S : Type*} [Fintype S] (r : Reaction S)
    (rest : List (Reaction S)) (x : S → ℕ) (thresh : ℝ) :
    selectAux (r :: rest) x thresh =
      (if thresh < propensity r x then some r
        else selectAux rest x (thresh - propensity r x)) := rfl

/-- Selection soundness: a selected reaction has positive propensity whenever
the threshold is nonnegative. -/
theorem selectAux_some_pos {S : Type*} [Fintype S] (rs : List (Reaction S))
    (x : S → ℕ) (thresh : ℝ) (r : Reaction S) (hthresh : 0 ≤ thresh)
    (hsel : selectAux rs x thresh = some r) : 0 < propensity r x := by
  induction rs generalizing thresh r with
  | nil =>
    rw [selectAux_nil] at hsel
    simp at hsel
  | cons head rest ih =>
    rw [selectAux_cons] at hsel
    by_cases hcond : thresh < propensity head x
    · rw [ite_eq_left hcond] at hsel
      have h_eq : head = r := Option.some_inj.mp hsel
      subst h_eq
      exact lt_of_le_of_lt hthresh hcond
    · rw [ite_eq_right hcond] at hsel
      have hle : propensity head x ≤ thresh := not_lt.mp hcond
      have hthresh' : 0 ≤ thresh - propensity head x :=
        sub_nonneg.mpr hle
      exact ih _ _ hthresh' hsel

/-- Direct-method step as a function of uniforms `u1 u2`: `none` when `a0 = 0`
(absorbing); otherwise `(τ, r, fire r x)` with `τ = log (1 / u1) / a0` and `r`
the first reaction whose cumulative propensity exceeds `u2 * a0`.
Out-of-range `u2`: negative `u2` selects the head reaction (a threshold below
zero is exceeded immediately); `u2 ≥ 1` yields `none` (a threshold at or above
the total is never exceeded). -/
noncomputable def step {S : Type*} [Fintype S] (rs : List (Reaction S)) (x : S → ℕ)
    (u1 u2 : ℝ) : Option (ℝ × Reaction S × (S → ℕ)) :=
  let a0 := totalPropensity rs x
  if a0 = 0 then none
  else
    match selectAux rs x (u2 * a0) with
    | none => none
    | some r => some (Real.log (1 / u1) / a0, r, fire r x)

theorem step_eq {S : Type*} [Fintype S] (rs : List (Reaction S)) (x : S → ℕ)
    (u1 u2 : ℝ) :
    step rs x u1 u2 =
      (if totalPropensity rs x = 0 then none
        else match selectAux rs x (u2 * totalPropensity rs x) with
          | none => none
          | some r =>
            some (Real.log (1 / u1) / totalPropensity rs x, r, fire r x)) := rfl

/-- Soundness core: a successful step with `0 < u1 ≤ 1` and `0 ≤ u2 < 1`
yields a nonnegative waiting time and a reaction with positive propensity.
(`u2 < 1` is part of the interface; soundness only needs `0 ≤ u2`.) -/
theorem step_some_sound {S : Type*} [Fintype S] (rs : List (Reaction S))
    (x : S → ℕ) (u1 u2 τ : ℝ) (r : Reaction S) (x' : S → ℕ)
    (h1 : 0 < u1) (hu1 : u1 ≤ 1) (h2a : 0 ≤ u2) (_h2b : u2 < 1)
    (hstep : step rs x u1 u2 = some (τ, r, x')) :
    0 ≤ τ ∧ 0 < propensity r x := by
  rw [step_eq] at hstep
  by_cases ha0 : totalPropensity rs x = 0
  · rw [ite_eq_left ha0] at hstep
    simp at hstep
  · rw [ite_eq_right ha0] at hstep
    cases hsel : selectAux rs x (u2 * totalPropensity rs x) with
    | none =>
      rw [hsel] at hstep
      simp at hstep
    | some r' =>
      rw [hsel] at hstep
      have htuple :
          (Real.log (1 / u1) / totalPropensity rs x, r', fire r' x)
            = (τ, r, x') :=
        Option.some_inj.mp hstep
      rw [Prod.mk.injEq] at htuple
      obtain ⟨hτ, hmid⟩ := htuple
      rw [Prod.mk.injEq] at hmid
      obtain ⟨hr, _hx⟩ := hmid
      rw [hr] at hsel
      have ha0pos : 0 < totalPropensity rs x :=
        lt_of_le_of_ne (totalPropensity_nonneg rs x) (Ne.symm ha0)
      have hthresh : 0 ≤ u2 * totalPropensity rs x :=
        mul_nonneg h2a (le_of_lt ha0pos)
      have hpos : 0 < propensity r x :=
        selectAux_some_pos rs x (u2 * totalPropensity rs x) r hthresh hsel
      have hlog : 0 ≤ Real.log (1 / u1) :=
        Real.log_nonneg (one_le_one_div h1 hu1)
      have hdiv : 0 ≤ Real.log (1 / u1) / totalPropensity rs x :=
        div_nonneg hlog (le_of_lt ha0pos)
      rw [← hτ]
      exact ⟨hdiv, hpos⟩

/-- Absorbing: the empty reaction list never fires. -/
theorem step_none_of_empty {S : Type*} [Fintype S] (x : S → ℕ) (u1 u2 : ℝ) :
    step ([] : List (Reaction S)) x u1 u2 = none := by
  rw [step_eq]
  simp [totalPropensity]

#print axioms propensity_nonneg
#print axioms propensity_eq_zero_of_insufficient
#print axioms totalPropensity_eq_zero_iff
#print axioms selectAux_some_pos
#print axioms step_some_sound
#print axioms step_none_of_empty

end Cslib.Bioinformatics.CRN
