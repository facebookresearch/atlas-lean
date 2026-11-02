/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The straight-line fragment is decidable
-/
module

public import CSLibExt.AutomatedReasoning.StringConstraints.Syntax
public import Mathlib.Tactic.Ring

/-!
# The straight-line fragment is decidable

A **straight-line** (SSA) string-constraint system defines each
variable once, by a term that mentions only earlier variables, and then
asserts a formula over the defined variables. Every *defined*
variable's value is forced by the earlier ones, so there is at most
one assignment on defined variables; it is computed by a left fold
over the definitions, and satisfiability is then a single check on
that candidate. (Variables past the end of the definition list are
unconstrained; only the defined ones are forced.) In particular,
straight-line satisfiability is decidable even though string lengths
are unbounded — unlike the bounded fragment, no length bound is
needed.

This is the straight-line fragment of the string-solving literature:
each assignment in the program defines one variable from earlier ones
(SSA form), and the assertions are checked on the resulting values.
Modern string solvers decide SSA-form programs this way.

## Main results

- `SLSys`, `Acyclic`, `SLSat`: straight-line systems and their
  semantics.
- `sol_satisfies_defs`: the folded assignment satisfies the definitions.
- `eq_sol_of_sat`: any satisfying assignment agrees with the folded one.
- `decidable_exists_sat_of_acyclic`: satisfiability of an acyclic
  straight-line system is decidable.

## References

* *A Survey on String Constraint Solving*, arXiv:2002.02376, for the
  straight-line fragment and the solver landscape.
* J. D. Day, V. Ganesh, P. He, F. Manea, D. Nowotka, *The Satisfiability
  of Word Equations: Decidable and Undecidable Theories*, Reachability
  Problems (RP 2018), LNCS 11123, pp. 15–29, for the surrounding
  decidability landscape.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.AutomatedReasoning.StringConstraints

variable {α : Type*}

/-- A **straight-line system**: one defining term per variable, plus a
query formula. The definition at position `k` is the definition of
variable `k`. -/
structure SLSys (α : Type*) where
  /-- The defining terms, in variable order. -/
  defs : List (Term α ℕ)
  /-- The query formula. -/
  query : Formula α ℕ

/-- A straight-line system is **acyclic** when every defining term
mentions only earlier variables, and the query mentions only defined
variables. -/
def Acyclic (S : SLSys α) : Prop :=
  (∀ k (h : k < S.defs.length), ∀ j ∈ varsOf (S.defs[k]'h), j < k) ∧
    ∀ j ∈ varsOfFormula S.query, j < S.defs.length

/-- Satisfaction of a straight-line system: the assignment obeys every
definition and satisfies the query. -/
def SLSat (S : SLSys α) (σ : ℕ → List α) : Prop :=
  (∀ k (h : k < S.defs.length), σ k = eval σ (S.defs[k]'h)) ∧ Sat σ S.query

/-- One fold step: evaluate the next defining term under the values
computed so far and append the result. -/
def slStep (acc : List (List α)) (t : Term α ℕ) : List (List α) :=
  acc ++ [eval (fun j => acc.getD j []) t]

/-- The folded assignment values, in variable order. -/
def values (S : SLSys α) : List (List α) :=
  S.defs.foldl slStep []

/-- The candidate assignment of a straight-line system. -/
def sol (S : SLSys α) : ℕ → List α :=
  fun i => (values S).getD i []

/-- Lookup with a proof of the bound is the `getElem` value. -/
theorem getD_eq_of_lt {l : List (List α)} {n : ℕ} (h : n < l.length) :
    l.getD n [] = l[n]'h := by
  rw [List.getD_eq_getElem]

/-- The fold preserves its initial segment. -/
theorem foldl_take (defs : List (Term α ℕ)) (acc : List (List α)) :
    (defs.foldl slStep acc).take acc.length = acc := by
  induction defs generalizing acc with
  | nil => simp [List.take_length]
  | cons t defs ih =>
    have h1 := ih (acc := slStep acc t)
    have hlen : (slStep acc t).length = acc.length + 1 := by
      simp [slStep, List.length_append]
    rw [hlen] at h1
    rw [List.foldl_cons]
    have htake : (defs.foldl slStep (slStep acc t)).take acc.length
        = ((defs.foldl slStep (slStep acc t)).take (acc.length + 1)).take acc.length := by
      rw [List.take_take]
      congr 1
      exact (Nat.min_eq_left (Nat.le_succ _)).symm
    rw [htake, h1]
    simp [slStep]

/-- The fold appends exactly one value per definition. -/
theorem foldl_length (defs : List (Term α ℕ)) (acc : List (List α)) :
    (defs.foldl slStep acc).length = acc.length + defs.length := by
  induction defs generalizing acc with
  | nil => simp
  | cons t defs ih =>
    have h1 := ih (acc := slStep acc t)
    have h2 : (slStep acc t).length = acc.length + 1 := by
      simp [slStep, List.length_append]
    rw [List.foldl_cons, List.length_cons]
    omega

/-- Length of the folded values: one per definition. -/
theorem values_length (S : SLSys α) :
    (values S).length = S.defs.length := by
  simp [values, foldl_length]

/-- Lookup in a taken prefix agrees with lookup in the whole list. -/
theorem getD_take_of_lt {l : List (List α)} {n m : ℕ} (h : n < m) (hl : n < l.length) :
    (l.take m).getD n [] = l.getD n [] := by
  rw [getD_eq_of_lt (by rw [List.length_take]; exact Nat.lt_min.mpr ⟨h, hl⟩),
    getD_eq_of_lt hl]
  exact List.getElem_take (h := by rw [List.length_take]; exact Nat.lt_min.mpr ⟨h, hl⟩)

/-- Lookup in an appended list agrees with lookup below the prefix length. -/
theorem getD_append_of_lt {acc : List (List α)} {x : List α} {j : ℕ}
    (hj : j < acc.length) :
    (acc ++ [x]).getD j [] = acc.getD j [] := by
  rw [getD_eq_of_lt (by rw [List.length_append]; omega), getD_eq_of_lt hj]
  exact List.getElem_append_left hj

/-- Lookup in a folded list agrees with lookup in the starting list
below its length. -/
theorem getD_foldl_of_lt (defs : List (Term α ℕ)) (acc : List (List α)) {j : ℕ}
    (hj : j < acc.length) :
    (defs.foldl slStep acc).getD j [] = acc.getD j [] := by
  induction defs generalizing acc with
  | nil => rfl
  | cons t defs ih =>
    rw [List.foldl_cons]
    rw [ih (acc := slStep acc t) (by
      have hlen : (slStep acc t).length = acc.length + 1 := by
        simp [slStep, List.length_append]
      omega)]
    exact getD_append_of_lt hj

/-- The defining equation for the folded values: the value at position
`acc.length + k` is the `k`-th defining term evaluated under the
folded values. The variable condition says the term only looks at
positions below `acc.length + k`. -/
theorem foldl_getD (defs : List (Term α ℕ)) (acc : List (List α)) (k : ℕ)
    (hk : k < defs.length)
    (hvars : ∀ j ∈ varsOf (defs[k]'hk), j < acc.length + k) :
    (defs.foldl slStep acc).getD (acc.length + k) []
      = eval (fun j => (defs.foldl slStep acc).getD j []) (defs[k]'hk) := by
  induction defs generalizing acc k with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons t defs ih =>
    cases k with
    | zero =>
      have hk0 : (t :: defs)[0]'(by simp) = t := rfl
      rw [List.foldl_cons]
      change (defs.foldl slStep (slStep acc t)).getD (acc.length + 0) []
        = eval (fun j => (defs.foldl slStep (slStep acc t)).getD j []) t
      rw [Nat.add_zero]
      have hget : (defs.foldl slStep (slStep acc t)).getD acc.length []
          = eval (fun j => acc.getD j []) t := by
        have hlen : (slStep acc t).length = acc.length + 1 := by
          simp only [slStep, List.length_append, List.length_singleton]
        have hlt : acc.length < (defs.foldl slStep (slStep acc t)).length := by
          rw [foldl_length]; omega
        have htake := foldl_take defs (slStep acc t)
        rw [hlen] at htake
        have hlast : (slStep acc t).getD acc.length []
            = eval (fun j => acc.getD j []) t := by
          rw [show slStep acc t = acc ++ [eval (fun j => acc.getD j []) t] from rfl]
          rw [getD_eq_of_lt (by rw [List.length_append, List.length_singleton]; omega)]
          rw [List.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self, List.getElem_cons_zero]
        rw [← getD_take_of_lt (show acc.length < acc.length + 1 by omega) hlt, htake]
        exact hlast
      rw [hget]
      apply eval_eq_of_agree_on_vars
      intro j hj
      have hjlt : j < acc.length := by
        have := hvars j (by simpa [hk0] using hj)
        simpa using this
      have h1 : (defs.foldl slStep (slStep acc t)).getD j []
          = (slStep acc t).getD j [] :=
        getD_foldl_of_lt defs (slStep acc t) (by
          have hlen2 : (slStep acc t).length = acc.length + 1 := by
            simp only [slStep, List.length_append, List.length_singleton]
          omega)
      rw [h1]
      exact (getD_append_of_lt hjlt).symm
    | succ k' =>
      have hk' : k' < defs.length := by
        have : k' + 1 < (t :: defs).length := hk
        simpa using this
      have hvars' : ∀ j ∈ varsOf (defs[k']'hk'), j < (slStep acc t).length + k' := by
        intro j hj
        have hlen : (slStep acc t).length = acc.length + 1 := by
          simp only [slStep, List.length_append, List.length_singleton]
        have h := hvars j (by change j ∈ varsOf (defs[k']'hk'); exact hj)
        omega
      rw [List.foldl_cons]
      change (defs.foldl slStep (slStep acc t)).getD (acc.length + (k' + 1)) []
        = eval (fun j => (defs.foldl slStep (slStep acc t)).getD j []) (defs[k']'hk')
      have hidx : acc.length + (k' + 1) = (slStep acc t).length + k' := by
        have hlen : (slStep acc t).length = acc.length + 1 := by
          simp only [slStep, List.length_append, List.length_singleton]
        omega
      rw [hidx]
      exact ih (slStep acc t) k' hk' hvars'

/-- The candidate assignment satisfies every definition. -/
theorem sol_satisfies_defs (S : SLSys α) (hacy : Acyclic S) (k : ℕ)
    (hk : k < S.defs.length) :
    sol S k = eval (sol S) (S.defs[k]'hk) := by
  have h := foldl_getD S.defs [] k hk (by
    intro j hj
    have := hacy.1 k hk j hj
    simpa using this)
  simp only [List.length_nil, Nat.zero_add] at h
  exact h

/-- Any satisfying assignment agrees with the candidate on defined
variables. -/
theorem eq_sol_of_sat {S : SLSys α} {σ : ℕ → List α} (hacy : Acyclic S)
    (hSat : SLSat S σ) (k : ℕ) (hk : k < S.defs.length) :
    σ k = sol S k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [hSat.1 k hk, sol_satisfies_defs S hacy k hk]
    apply eval_eq_of_agree_on_vars
    intro j hj
    have hjk : j < k := hacy.1 k hk j hj
    exact ih j hjk (by
      have : j < S.defs.length := by omega
      exact this)

/-- Satisfiability of a straight-line system is equivalent to the query
holding on the candidate assignment. -/
theorem exists_sat_iff_sat_sol (S : SLSys α) (hacy : Acyclic S) :
    (∃ σ, SLSat S σ) ↔ Sat (sol S) S.query := by
  constructor
  · rintro ⟨σ, hSat⟩
    apply (sat_congr (σ := σ) (τ := sol S) ?_).mp hSat.2
    intro j hj
    have hjlt : j < S.defs.length := hacy.2 j hj
    exact eq_sol_of_sat hacy hSat j hjlt
  · intro hq
    refine ⟨sol S, ?_, hq⟩
    intro k hk
    exact sol_satisfies_defs S hacy k hk

/-- **Satisfiability of an acyclic straight-line system is decidable.** -/
def decidableExistsSatOfAcyclic (S : SLSys α) (hacy : Acyclic S) [DecidableEq α] :
    Decidable (∃ σ, SLSat S σ) := by
  haveI : Decidable (Sat (sol S) S.query) := by
    exact decidable_of_decidable_of_iff satB_iff
  exact decidable_of_decidable_of_iff (exists_sat_iff_sat_sol S hacy).symm

end Cslib.AutomatedReasoning.StringConstraints
