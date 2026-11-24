/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Function.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Prescribed-grid reduction preserving an actual minor

The coordinate scan tests the actual selected determinant and takes the first
passing value in a prescribed ordered grid. Its tested-index trace is constructed
by the same branches as its output. The algebraic guarantee uses the native
degree bound for an affine determinant and the finite distinct-root bound.

Reference: Ivanyos, Qiao and Subrahmanyam, *Constructive noncommutative rank
computation in deterministic polynomial time over fields of arbitrary
characteristics*, January 20, 2016 addendum, Lemma 6.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators Matrix
open Polynomial

namespace Matrix

variable {F : Type u} [Field F] [DecidableEq F] {k l m r N : ℕ}

/-- Determinant of the actual selected minor of the combination. -/
def selectedMinor (A : Fin m → Matrix (Fin k) (Fin l) F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (theta : Fin m → F) : F :=
  ((Fintype.linearCombination F A theta).submatrix rows cols).det

/-- Search the given indices, returning the first passing point and the indices
whose actual determinant predicates were evaluated. -/
def minorGridSearch (A : Fin m → Matrix (Fin k) (Fin l) F) (grid : Fin N → F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (theta : Fin m → F) (i : Fin m) :
    List (Fin N) → Option (Fin N) × List (Fin N)
  | [] => (none, [])
  | t :: ts =>
      if selectedMinor A rows cols (Function.update theta i (grid t)) ≠ 0 then
        (some t, [t])
      else
        let rest := minorGridSearch A grid rows cols theta i ts
        (rest.1, t :: rest.2)

/-- Reduce exactly the listed coefficient coordinates, retaining the actual
coordinate/grid-index trace of determinant tests. -/
def minorGridReduceOn (A : Fin m → Matrix (Fin k) (Fin l) F) (grid : Fin N → F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) :
    List (Fin m) → (Fin m → F) → Option (Fin m → F) × List (Fin m × Fin N)
  | [], theta => (some theta, [])
  | i :: is, theta =>
      let trial := minorGridSearch A grid rows cols theta i (List.finRange N)
      match trial.1 with
      | none => (none, trial.2.map (fun t => (i, t)))
      | some t =>
          let rest := minorGridReduceOn A grid rows cols is (Function.update theta i (grid t))
          (rest.1, trial.2.map (fun t => (i, t)) ++ rest.2)

/-- Scan every coefficient once, with the actual determinant-test trace. -/
def reduceMinorGridWithTrace (A : Fin m → Matrix (Fin k) (Fin l) F) (grid : Fin N → F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (beta : Fin m → F) :
    Option (Fin m → F) × List (Fin m × Fin N) :=
  minorGridReduceOn A grid rows cols (List.finRange m) beta

/-- The Option output of the actual prescribed-grid coordinate scan. -/
def reduceMinorGrid (A : Fin m → Matrix (Fin k) (Fin l) F) (grid : Fin N → F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (beta : Fin m → F) : Option (Fin m → F) :=
  (reduceMinorGridWithTrace A grid rows cols beta).1

theorem minorGridSearch_fst (A : Fin m → Matrix (Fin k) (Fin l) F) (grid : Fin N → F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (theta : Fin m → F)
    (i : Fin m) (ts : List (Fin N)) :
    (minorGridSearch A grid rows cols theta i ts).1 =
      ts.find? (fun t => decide (selectedMinor A rows cols (Function.update theta i (grid t)) ≠ 0)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      by_cases h : selectedMinor A rows cols (Function.update theta i (grid t)) ≠ 0
      · simp [minorGridSearch, h]
      · simp [minorGridSearch, h, ih]

/-- Every trace entry corresponds to a visited predicate branch, and the search
visits no more indices than were supplied. -/
theorem minorGridSearch_trace_length_le (A : Fin m → Matrix (Fin k) (Fin l) F) (grid : Fin N → F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (theta : Fin m → F)
    (i : Fin m) (ts : List (Fin N)) :
    (minorGridSearch A grid rows cols theta i ts).2.length ≤ ts.length := by
  induction ts with
  | nil => simp [minorGridSearch]
  | cons t ts ih =>
      by_cases h : selectedMinor A rows cols (Function.update theta i (grid t)) ≠ 0
      · simp [minorGridSearch, h]
      · simpa [minorGridSearch, h] using Nat.succ_le_succ ih

/-- The actual affine polynomial used by one coordinate's determinant test. -/
noncomputable def coordinateMinorPolynomial (A : Fin m → Matrix (Fin k) (Fin l) F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (theta : Fin m → F) (i : Fin m) : F[X] :=
  ((Polynomial.X : F[X]) • ((A i).submatrix rows cols).map Polynomial.C +
    ((Fintype.linearCombination F A (Function.update theta i 0)).submatrix rows cols).map Polynomial.C).det

omit [DecidableEq F] in
theorem coordinateMinorPolynomial_natDegree_le (A : Fin m → Matrix (Fin k) (Fin l) F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (theta : Fin m → F) (i : Fin m) :
    (coordinateMinorPolynomial A rows cols theta i).natDegree ≤ r := by
  simpa only [coordinateMinorPolynomial, Fintype.card_fin] using
    Polynomial.natDegree_det_X_add_C_le ((A i).submatrix rows cols)
      ((Fintype.linearCombination F A (Function.update theta i 0)).submatrix rows cols)

omit [DecidableEq F] in
theorem coordinateMinorPolynomial_eval (A : Fin m → Matrix (Fin k) (Fin l) F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (theta : Fin m → F) (i : Fin m) (x : F) :
    (coordinateMinorPolynomial A rows cols theta i).eval x =
      selectedMinor A rows cols (Function.update theta i x) := by
  unfold coordinateMinorPolynomial
  change (Polynomial.evalRingHom x) _ = _
  rw [RingHom.map_det]
  unfold selectedMinor
  have hupdate : Function.update theta i x = Function.update theta i 0 + Pi.single i x := by
    simp only [Pi.update_eq_sub_add_single, Pi.single_zero, add_zero]
  rw [hupdate, (Fintype.linearCombination F A).map_add, Fintype.linearCombination_apply_single]
  congr 1
  ext a b
  change ((Polynomial.X * Polynomial.C (A i (rows a) (cols b)) +
      Polynomial.C (Fintype.linearCombination F A (Function.update theta i 0) (rows a) (cols b))).eval x) =
    Fintype.linearCombination F A (Function.update theta i 0) (rows a) (cols b) + x * A i (rows a) (cols b)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  exact add_comm _ _

omit [DecidableEq F] in
theorem exists_grid_selectedMinor_ne_zero (A : Fin m → Matrix (Fin k) (Fin l) F)
    (grid : Fin N → F) (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l)
    (theta : Fin m → F) (i : Fin m) (hgrid : Function.Injective grid) (hsize : r < N)
    (hminor : selectedMinor A rows cols theta ≠ 0) :
    ∃ t : Fin N, selectedMinor A rows cols (Function.update theta i (grid t)) ≠ 0 := by
  classical
  let p := coordinateMinorPolynomial A rows cols theta i
  have hp : p ≠ 0 := by
    intro hz
    have heval := coordinateMinorPolynomial_eval A rows cols theta i (theta i)
    rw [Function.update_eq_self] at heval
    have : selectedMinor A rows cols theta = 0 := by simpa [p, hz] using heval.symm
    exact hminor this
  by_contra h
  push Not at h
  apply hp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hgrid
  · intro t
    simpa [p, coordinateMinorPolynomial_eval] using h t
  · exact (coordinateMinorPolynomial_natDegree_le A rows cols theta i).trans_lt
      (by simpa using hsize)

/-- A nonzero current minor guarantees a computed passing grid point. -/
theorem minorGridSearch_success (A : Fin m → Matrix (Fin k) (Fin l) F) (grid : Fin N → F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (theta : Fin m → F) (i : Fin m)
    (hgrid : Function.Injective grid) (hsize : r < N)
    (hminor : selectedMinor A rows cols theta ≠ 0) :
    ∃ t : Fin N,
      (minorGridSearch A grid rows cols theta i (List.finRange N)).1 = some t ∧
      selectedMinor A rows cols (Function.update theta i (grid t)) ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_grid_selectedMinor_ne_zero A grid rows cols theta i hgrid hsize hminor
  cases hs : (minorGridSearch A grid rows cols theta i (List.finRange N)).1 with
  | none =>
      rw [minorGridSearch_fst] at hs
      have hn := List.find?_eq_none.mp hs t (by simp)
      exact False.elim (hn (by simpa using ht))
  | some u =>
      refine ⟨u, rfl, ?_⟩
      rw [minorGridSearch_fst] at hs
      simpa using List.find?_some hs

/-- The reducer preserves the actual minor and records exactly which coordinates
have been processed; coordinates outside the scan remain unchanged. -/
theorem minorGridReduceOn_success (A : Fin m → Matrix (Fin k) (Fin l) F) (grid : Fin N → F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (xs : List (Fin m))
    (theta : Fin m → F) (hgrid : Function.Injective grid) (hsize : r < N)
    (hminor : selectedMinor A rows cols theta ≠ 0) :
    ∃ alpha : Fin m → F,
      (minorGridReduceOn A grid rows cols xs theta).1 = some alpha ∧
      selectedMinor A rows cols alpha ≠ 0 ∧
      (∀ j ∈ xs, alpha j ∈ Set.range grid) ∧
      (∀ j, j ∉ xs → alpha j = theta j) := by
  induction xs generalizing theta with
  | nil =>
      refine ⟨theta, rfl, hminor, ?_, ?_⟩
      · simp
      · intro j _
        rfl
  | cons i xs ih =>
      obtain ⟨t, ht, hnew⟩ := minorGridSearch_success A grid rows cols theta i hgrid hsize hminor
      let next := Function.update theta i (grid t)
      obtain ⟨alpha, halpha, hdet, hprocessed, hunprocessed⟩ := ih next hnew
      refine ⟨alpha, ?_, hdet, ?_, ?_⟩
      · simpa only [minorGridReduceOn, ht] using halpha
      · intro j hj
        rcases List.mem_cons.mp hj with hji | hj
        · subst j
          by_cases hi : i ∈ xs
          · exact hprocessed i hi
          · rw [hunprocessed i hi]
            exact ⟨t, (Function.update_self i (grid t) theta).symm⟩
        · exact hprocessed j hj
      · intro j hj
        have hji : j ≠ i := by
          intro heq
          subst j
          exact hj List.mem_cons_self
        have hjxs : j ∉ xs := fun h => hj (List.mem_cons_of_mem i h)
        rw [hunprocessed j hjxs]
        exact Function.update_of_ne hji (grid t) theta

/-- The actual full scan returns grid coefficients while preserving its selected
nonzero minor. No successful tuple is supplied to the computation. -/
theorem reduceMinorGrid_success (A : Fin m → Matrix (Fin k) (Fin l) F) (grid : Fin N → F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (beta : Fin m → F)
    (hgrid : Function.Injective grid) (hsize : r < N)
    (hminor : selectedMinor A rows cols beta ≠ 0) :
    ∃ alpha : Fin m → F,
      reduceMinorGrid A grid rows cols beta = some alpha ∧
      (∀ i, alpha i ∈ Set.range grid) ∧ selectedMinor A rows cols alpha ≠ 0 := by
  obtain ⟨alpha, houtput, hdet, hprocessed, _⟩ :=
    minorGridReduceOn_success A grid rows cols (List.finRange m) beta hgrid hsize hminor
  exact ⟨alpha, houtput, fun i => hprocessed i (by simp), hdet⟩

/-- The unconditional count follows the actual test trace, including failed scans. -/
theorem minorGridReduceOn_trace_length_le (A : Fin m → Matrix (Fin k) (Fin l) F)
    (grid : Fin N → F) (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l)
    (xs : List (Fin m)) (theta : Fin m → F) :
    (minorGridReduceOn A grid rows cols xs theta).2.length ≤ xs.length * N := by
  induction xs generalizing theta with
  | nil => simp [minorGridReduceOn]
  | cons i xs ih =>
      have hs := minorGridSearch_trace_length_le A grid rows cols theta i (List.finRange N)
      simp only [List.length_finRange] at hs
      cases hc : (minorGridSearch A grid rows cols theta i (List.finRange N)).1 with
      | none =>
          simp only [minorGridReduceOn, hc, List.length_map, List.length_cons]
          calc
            _ ≤ N := hs
            _ ≤ N + xs.length * N := Nat.le_add_right _ _
            _ = (xs.length + 1) * N := by simp [Nat.add_mul, Nat.add_comm]
      | some t =>
          simp only [minorGridReduceOn, hc, List.length_append, List.length_map, List.length_cons]
          calc
            _ ≤ N + xs.length * N := Nat.add_le_add hs (ih (Function.update theta i (grid t)))
            _ = (xs.length + 1) * N := by simp [Nat.add_mul, Nat.add_comm]

/-- At most `m*N` actual minor predicates occur in the coupled full-scan trace. -/
theorem reduceMinorGridWithTrace_length_le (A : Fin m → Matrix (Fin k) (Fin l) F)
    (grid : Fin N → F) (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (beta : Fin m → F) :
    (reduceMinorGridWithTrace A grid rows cols beta).2.length ≤ m * N := by
  simpa only [reduceMinorGridWithTrace, List.length_finRange] using
    minorGridReduceOn_trace_length_le A grid rows cols (List.finRange m) beta

end Matrix
