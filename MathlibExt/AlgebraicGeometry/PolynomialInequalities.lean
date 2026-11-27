/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.Algebra.Ring.SumsOfSquares
public import MathlibExt.AlgebraicGeometry.SemialgebraicSets

/-!
# Polynomial identity soundness on basic closed sets

A finite polynomial identity with sums-of-squares inequality multipliers and
arbitrary equality multipliers proves nonnegativity on its basic closed set.
An identity representing `-1` proves that the set is empty.

This is the elementary soundness argument in Pablo A. Parrilo, *Sum of Squares
Programs and Polynomial Inequalities*, §§2–3, and the easy direction of
Theorem 5:
https://ocw.mit.edu/courses/6-972-algebraic-techniques-and-semidefinite-optimization-spring-2006/63d6e45650205ceef6701971a9b4621c_lecture_22.pdf.
The source's full preordering includes products of inequality generators.
Here only the displayed finite single-generator identity is used; no converse,
completeness theorem, or procedure for finding identities is asserted.
-/

@[expose] public section

namespace MvPolynomial

variable {σ ι κ : Type*}

/-- The basic closed set defined by finitely many real polynomial inequalities
`g i ≥ 0` and equalities `h j = 0`. Only indices in `I` and `J` impose constraints;
the variable type may be arbitrary and either constraint family may be empty. -/
def basicClosedSet (I : Finset ι) (J : Finset κ)
    (g : ι → MvPolynomial σ ℝ) (h : κ → MvPolynomial σ ℝ) : Set (σ → ℝ) :=
  {x | (∀ i ∈ I, 0 ≤ eval x (g i)) ∧ ∀ j ∈ J, eval x (h j) = 0}

/-- Membership in a finite basic closed set is exactly the conjunction of
its indexed inequality and equality conditions. -/
@[simp]
theorem mem_basicClosedSet {I : Finset ι} {J : Finset κ}
    {g : ι → MvPolynomial σ ℝ} {h : κ → MvPolynomial σ ℝ} {x : σ → ℝ} :
    x ∈ basicClosedSet I J g h ↔
      (∀ i ∈ I, 0 ≤ eval x (g i)) ∧ ∀ j ∈ J, eval x (h j) = 0 := Iff.rfl

/-- A finite basic closed set of real polynomial constraints is semialgebraic
in the intrinsic algebra-of-sets definition. No finite-variable assumption
or projection theorem is needed. -/
theorem isSemialgebraic_basicClosedSet (I : Finset ι) (J : Finset κ)
    (g : ι → MvPolynomial σ ℝ) (h : κ → MvPolynomial σ ℝ) :
    TauCeti.IsSemialgebraic (basicClosedSet I J g h) := by
  have hg := TauCeti.IsSemialgebraic.biInter I.finite_toSet
    (fun i _ => TauCeti.isSemialgebraic_eval_nonneg (g i))
  have hh := TauCeti.IsSemialgebraic.biInter J.finite_toSet
    (fun j _ => TauCeti.isSemialgebraic_eval_eq_zero (h j))
  convert hg.inter hh using 1
  ext x
  simp [basicClosedSet]

/-- If `p = s₀ + (∑ i ∈ I, s i * g i) + ∑ j ∈ J, r j * h j`, where `s₀`
and each valid `s i` are sums of squares, then `p` evaluates nonnegatively
at every point of the basic closed set `g i ≥ 0`, `h j = 0`. Equality
multipliers `r j` are unrestricted, and only the finite listed constraints
and inequality multipliers are used. -/
theorem eval_nonneg_of_sos_identity {I : Finset ι} {J : Finset κ}
    {g : ι → MvPolynomial σ ℝ} {h : κ → MvPolynomial σ ℝ}
    {p s₀ : MvPolynomial σ ℝ} {s : ι → MvPolynomial σ ℝ}
    {r : κ → MvPolynomial σ ℝ} (hs₀ : IsSumSq s₀)
    (hs : ∀ i ∈ I, IsSumSq (s i))
    (hid : p = s₀ + (∑ i ∈ I, s i * g i) + ∑ j ∈ J, r j * h j)
    {x : σ → ℝ} (hx : x ∈ basicClosedSet I J g h) : 0 ≤ eval x p := by
  rw [hid, map_add, map_add, map_sum, map_sum]
  have hzero : ∑ j ∈ J, eval x (r j * h j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [map_mul, hx.2 j hj, mul_zero]
  rw [hzero, add_zero]
  apply add_nonneg (hs₀.map (eval x)).nonneg
  apply Finset.sum_nonneg
  intro i hi
  rw [map_mul]
  exact mul_nonneg ((hs i hi).map (eval x)).nonneg (hx.1 i hi)

/-- For real polynomials, an identity
`-1 = s₀ + (∑ i ∈ I, s i * g i) + ∑ j ∈ J, r j * h j` implies that the
basic closed set `g i ≥ 0`, `h j = 0` is empty, provided `s₀` and every
listed inequality multiplier `s i` are sums of squares. Equality multipliers
`r j` are unrestricted. Both constraint families are finite; variables may
be arbitrary. This is a sufficient infeasibility criterion, not a converse
or a completeness statement. -/
theorem basicClosedSet_eq_empty_of_sos_identity {I : Finset ι} {J : Finset κ}
    {g : ι → MvPolynomial σ ℝ} {h : κ → MvPolynomial σ ℝ}
    {s₀ : MvPolynomial σ ℝ} {s : ι → MvPolynomial σ ℝ}
    {r : κ → MvPolynomial σ ℝ} (hs₀ : IsSumSq s₀)
    (hs : ∀ i ∈ I, IsSumSq (s i))
    (hid : -1 = s₀ + (∑ i ∈ I, s i * g i) + ∑ j ∈ J, r j * h j) :
    basicClosedSet I J g h = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hn := eval_nonneg_of_sos_identity hs₀ hs hid hx
  exact (not_le_of_gt (neg_one_lt_zero : (-1 : ℝ) < 0))
    (by simpa only [map_neg, map_one] using hn)

end MvPolynomial
