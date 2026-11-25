/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import MathlibExt.AlgebraicGeometry.PolynomialInequalities
public import MathlibExt.RingTheory.MvPolynomial.BernsteinBounds

/-!
# Bernstein boxes for basic closed sets

Coefficient bounds give sufficient conditions for a closed box to be contained
in, or disjoint from, a finite basic closed set. Each constraint may use its own
coordinate degrees. Strict signs are essential for exclusion at the boundary.
Finite covers combine these statements using ordinary set unions; there is no
claim that every box is classified by these tests.

These are finite-constraint consequences of the Bernstein range enclosure in
A. P. Smith, *Enclosure Methods for Systems of Polynomial Equations and
Inequalities* (2012), §3.2.4, equation (3.17): https://d-nb.info/1028327854/34.
-/

@[expose] public section

namespace MvPolynomial

variable {σ ι κ : Type*} [Fintype σ]

private theorem eval_neg_of_coeff {n : σ → ℕ} {p : MvPolynomial σ ℝ}
    (hp : ∀ v, p.degreeOf v ≤ n v) {a b x : σ → ℝ} (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b)
    (hc : ∀ k : (v : σ) → Fin (n v + 1),
      bernsteinCoeff n (boxPullback a b p) (fun v => k v) < 0) : eval x p < 0 := by
  have hn := eval_pos_of_bernsteinCoeff_box (p := -p)
    (by simpa only [degreeOf_neg] using hp) hab (fun v => ⟨hx.1 v, hx.2 v⟩)
    (by simpa only [boxPullback, map_neg, bernsteinCoeff_neg, neg_pos] using hc)
  simpa only [map_neg, neg_pos] using hn

/-- A closed real box is contained in a finite basic closed set if every listed
inequality has nonnegative Bernstein pullback coefficients and every listed
equality has zero coefficients. The variables are finite, endpoints are ordered,
and each constraint has its own coordinate-degree bound. Collapsed coordinates,
zero degrees and empty constraint families are allowed. -/
theorem Icc_subset_basicClosedSet_of_bernsteinCoeff
    {I : Finset ι} {J : Finset κ} {g : ι → MvPolynomial σ ℝ}
    {h : κ → MvPolynomial σ ℝ} {ng : ι → σ → ℕ} {nh : κ → σ → ℕ}
    {a b : σ → ℝ} (hab : a ≤ b)
    (hg : ∀ i ∈ I, ∀ v, (g i).degreeOf v ≤ ng i v)
    (hh : ∀ j ∈ J, ∀ v, (h j).degreeOf v ≤ nh j v)
    (cg : ∀ i ∈ I, ∀ k : (v : σ) → Fin (ng i v + 1),
      0 ≤ bernsteinCoeff (ng i) (boxPullback a b (g i)) (fun v => k v))
    (ch : ∀ j ∈ J, ∀ k : (v : σ) → Fin (nh j v + 1),
      bernsteinCoeff (nh j) (boxPullback a b (h j)) (fun v => k v) = 0) :
    Set.Icc a b ⊆ basicClosedSet I J g h := by
  classical
  intro x hx
  have hx' : ∀ v, x v ∈ Set.Icc (a v) (b v) := fun v => ⟨hx.1 v, hx.2 v⟩
  constructor
  · intro i hi
    exact le_trans (Finset.le_inf' _ _ (fun k _ => cg i hi k))
      (eval_mem_Icc_bernsteinCoeff_box (hg i hi) hab hx').1
  · intro j hj
    exact le_antisymm
      (eval_mem_Icc_of_bernsteinCoeff_box (hh j hj) hab hx'
        (fun k => (ch j hj k).ge) (fun k => (ch j hj k).le)).2
      (eval_mem_Icc_of_bernsteinCoeff_box (hh j hj) hab hx'
        (fun k => (ch j hj k).ge) (fun k => (ch j hj k).le)).1

/-- A closed real box is disjoint from a finite basic closed set if one listed
inequality has strictly negative Bernstein pullback coefficients. Variables are
finite, endpoints ordered and the polynomial's coordinate degrees bounded by
`n`. Nonpositive coefficients do not suffice: a zero on the boundary is feasible. -/
theorem disjoint_Icc_basicClosedSet_of_bernsteinCoeff_neg
    {I : Finset ι} {J : Finset κ} {g : ι → MvPolynomial σ ℝ}
    {h : κ → MvPolynomial σ ℝ} {i : ι} (hi : i ∈ I) {n : σ → ℕ}
    (hg : ∀ v, (g i).degreeOf v ≤ n v) {a b : σ → ℝ} (hab : a ≤ b)
    (hc : ∀ k : (v : σ) → Fin (n v + 1),
      bernsteinCoeff n (boxPullback a b (g i)) (fun v => k v) < 0) :
    Disjoint (Set.Icc a b) (basicClosedSet I J g h) := by
  rw [Set.disjoint_left]
  intro x hx hs
  exact (not_lt_of_ge (hs.1 i hi)) (eval_neg_of_coeff hg hab hx hc)

/-- A closed real box is disjoint from a finite basic closed set if one listed
equality has strictly positive Bernstein pullback coefficients. Variables are
finite, endpoints ordered and this equality polynomial has coordinate degrees
bounded by `n`. Zero-width coordinates are allowed. -/
theorem disjoint_Icc_basicClosedSet_of_bernsteinCoeff_eq_pos
    {I : Finset ι} {J : Finset κ} {g : ι → MvPolynomial σ ℝ}
    {h : κ → MvPolynomial σ ℝ} {j : κ} (hj : j ∈ J) {n : σ → ℕ}
    (hh : ∀ v, (h j).degreeOf v ≤ n v) {a b : σ → ℝ} (hab : a ≤ b)
    (hc : ∀ k : (v : σ) → Fin (n v + 1),
      0 < bernsteinCoeff n (boxPullback a b (h j)) (fun v => k v)) :
    Disjoint (Set.Icc a b) (basicClosedSet I J g h) := by
  rw [Set.disjoint_left]
  intro x hx hs
  exact (ne_of_gt (eval_pos_of_bernsteinCoeff_box hh hab
    (fun v => ⟨hx.1 v, hx.2 v⟩) hc)) (hs.2 j hj)

/-- A closed real box is disjoint from a finite basic closed set if one listed
equality has strictly negative Bernstein pullback coefficients. Variables are
finite, endpoints ordered and this equality polynomial has coordinate degrees
bounded by `n`. Zero-width coordinates are allowed. -/
theorem disjoint_Icc_basicClosedSet_of_bernsteinCoeff_eq_neg
    {I : Finset ι} {J : Finset κ} {g : ι → MvPolynomial σ ℝ}
    {h : κ → MvPolynomial σ ℝ} {j : κ} (hj : j ∈ J) {n : σ → ℕ}
    (hh : ∀ v, (h j).degreeOf v ≤ n v) {a b : σ → ℝ} (hab : a ≤ b)
    (hc : ∀ k : (v : σ) → Fin (n v + 1),
      bernsteinCoeff n (boxPullback a b (h j)) (fun v => k v) < 0) :
    Disjoint (Set.Icc a b) (basicClosedSet I J g h) := by
  rw [Set.disjoint_left]
  intro x hx hs
  exact (ne_of_lt (eval_neg_of_coeff hh hab hx hc)) (hs.2 j hj)

end MvPolynomial

namespace TauCeti

/-- A coordinatewise closed box in a finite real function space is intrinsically
semialgebraic. No ordering of endpoints is required. In particular, collapsed
coordinates and empty boxes are allowed; the empty variable type is allowed too. -/
theorem isSemialgebraic_Icc {σ : Type*} [Finite σ] (a b : σ → ℝ) :
    IsSemialgebraic (Set.Icc a b) := by
  have hl := IsSemialgebraic.iInter (fun v : σ =>
    isSemialgebraic_eval_le (MvPolynomial.C (a v)) (MvPolynomial.X v))
  have hu := IsSemialgebraic.iInter (fun v : σ =>
    isSemialgebraic_eval_le (MvPolynomial.X v) (MvPolynomial.C (b v)))
  convert hl.inter hu using 1
  ext x
  simp only [Set.mem_Icc, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  rfl

end TauCeti
