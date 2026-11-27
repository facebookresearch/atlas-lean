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
# Grid reduction preserving a nonzero matrix minor

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. Starting from M(β) ≠ 0, a scan replaces coefficients one at a time by the first
grid value retaining a nonzero minor. If g is injective and N > r, the scan returns α with
every αᵢ in the grid and M(α) ≠ 0. It performs at most mN minor tests; this bound also applies
when a scan fails.

Reference: Ivanyos, Qiao and Subrahmanyam, *Constructive noncommutative rank computation in
deterministic polynomial time over fields of arbitrary characteristics*, January 20, 2016
addendum, Lemma 6.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators Matrix
open Polynomial

namespace Matrix

variable {F : Type u} [Field F] [DecidableEq F] {k l m r N : ℕ}

/-- **A selected minor of a matrix combination.**

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. The scalar function θ ↦ M(θ) is
the selected determinant, with value 1 for the empty r = 0 minor.
-/
def selectedMinor (A : Fin m → Matrix (Fin k) (Fin l) F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (theta : Fin m → F) : F :=
  ((Fintype.linearCombination F A theta).submatrix rows cols).det

/-- **The first grid value preserving a minor.**

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. For a coordinate i, coefficient tuple θ and a list L of grid indices, search L in
order for t with M(θ[i ↦ g(t)]) ≠ 0. Return the first such index, or none if it does not
exist, together with the list of indices tested up to success or exhaustion.
-/
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

/-- **Reducing a list of coefficient coordinates.**

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. Given a list of coordinates and an initial θ, replace each listed coordinate by
the first grid value preserving M ≠ 0, in grid-index order. Return the final tuple if all
searches succeed, or none at the first failure, together with the sequence of tested
coordinate/index pairs.
-/
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

/-- **The full coefficient scan and its test sequence.**

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. Starting from β, scan coordinates 0,…,m−1, replacing each by the first grid value
retaining a nonzero selected minor. The output is an optional coefficient tuple paired with
the sequence of tested coordinate/grid-index pairs.
-/
def reduceMinorGridWithTrace (A : Fin m → Matrix (Fin k) (Fin l) F) (grid : Fin N → F)
    (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (beta : Fin m → F) :
    Option (Fin m → F) × List (Fin m × Fin N) :=
  minorGridReduceOn A grid rows cols (List.finRange m) beta

/-- **The output of grid reduction.**

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. The reduction map returns the optional tuple produced by scanning all m
coordinates in order and selecting the first grid value at each coordinate for which the
selected determinant stays nonzero.
-/
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

/-- **The number of tests in a single coordinate search.**

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. For any coefficient tuple θ, coordinate i and list L of grid indices, the
sequence of indices tested while searching for M(θ[i ↦ g(t)]) ≠ 0 has length at most |L|.
-/
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

/-- **The determinant polynomial for one coordinate.**

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Fix θ and i. Define pᵢ(X) =
det(X Aᵢ|minor + (∑ⱼ θ[i ↦ 0]ⱼ Aⱼ)|minor). Its evaluation at t equals M(θ[i ↦ t]); this is the
determinant of an affine r × r matrix pencil.
-/
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

/-- **A nonzero minor survives one grid search.**

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. Assume g is injective, N > r and M(θ) ≠ 0. For every coordinate i, searching
indices 0,…,N−1 returns some t and M(θ[i ↦ g(t)]) ≠ 0.
-/
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

/-- **A partial coefficient scan preserves its minor.**

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. Assume g is injective, N > r and M(θ) ≠ 0. Scanning any list L of coordinates
succeeds with α satisfying M(α) ≠ 0. Every coordinate occurring in L has αᵢ in the grid, and
every coordinate outside L has αᵢ = θᵢ.
-/
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

/-- **Grid coefficients with the selected minor nonzero.**

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. Assume g is injective, N > r and M(β) ≠ 0. The full scan returns α such that
every αᵢ belongs to the range of g and M(α) ≠ 0.
-/
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

/-- **A test bound for a partial coefficient scan.**

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. For any list L of coefficient coordinates and any starting tuple θ, the sequence
of minor tests in its grid scan has length at most |L|N, whether the scan succeeds or fails.
-/
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

/-- **A test bound for the full coefficient scan.**

Let F be a field, A₀,…,Aₘ₋₁ ∈ Mat(k,l;F), and fix injections selecting r rows and r columns.
Write M(θ) for the determinant of that r × r minor of ∑ᵢ θᵢAᵢ. Let g : Fin N → F be an ordered
scalar grid. For every initial tuple β, the full ordered scan of m coordinates has at most mN
recorded minor tests, whether it succeeds or fails.
-/
theorem reduceMinorGridWithTrace_length_le (A : Fin m → Matrix (Fin k) (Fin l) F)
    (grid : Fin N → F) (rows : Fin r ↪ Fin k) (cols : Fin r ↪ Fin l) (beta : Fin m → F) :
    (reduceMinorGridWithTrace A grid rows cols beta).2.length ≤ m * N := by
  simpa only [reduceMinorGridWithTrace, List.length_finRange] using
    minorGridReduceOn_trace_length_le A grid rows cols (List.finRange m) beta

end Matrix
