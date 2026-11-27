/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import MathlibExt.RingTheory.MvPolynomial.BernsteinBounds

/-!
# Bernstein bounds for polynomial matrices

A common coordinate-degree vector gives a shared Bernstein expansion of all
entries of a real polynomial matrix. Nonnegative weights summing to one
preserve positive semidefiniteness and fixed matrix lower bounds. For arbitrary
matrix index types, Mathlib's positivity predicates test finitely supported
vectors. The unrestricted-vector quadratic-form statements assume finite
matrix indices; no infinite-dimensional operator claim is made.

This is a matrix consequence of scalar Bernstein reconstruction in Garloff
and Hamadneh (2016), §2, https://d-nb.info/1163536172/34, and convexity of
the positive-semidefinite cone in Boyd and Vandenberghe, *Convex Optimization*,
§2.2.5, https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf.
-/

@[expose] public section

namespace Matrix

open Finset MvPolynomial

variable {ι m r : Type*}

/-- A finite convex combination of real square matrices preserves a fixed
matrix lower bound: if each difference `B k - L` is positive semidefinite,
so is the difference between the combination and `L`. No positivity or
symmetry assumption on `L` itself is needed for this difference statement. -/
theorem posSemidef_sum_smul_sub {κ : Type*} (s : Finset κ)
    {w : κ → ℝ} {B : κ → Matrix m m ℝ} {L : Matrix m m ℝ}
    (hw : ∀ k ∈ s, 0 ≤ w k) (hs : ∑ k ∈ s, w k = 1)
    (hB : ∀ k ∈ s, (B k - L).PosSemidef) :
    ((∑ k ∈ s, w k • B k) - L).PosSemidef := by
  have h := Matrix.posSemidef_sum s (fun k hk => (hB k hk).smul (hw k hk))
  simpa only [smul_sub, sum_sub_distrib, ← sum_smul, hs, one_smul] using h

variable [Fintype ι]

/-- Apply the canonical tensor Bernstein coefficient map entrywise to a real
polynomial matrix, using one coordinate-degree vector for all entries. -/
noncomputable def bernsteinCoeff (n : ι → ℕ) (P : Matrix m r (MvPolynomial ι ℝ))
    (k : ι → ℕ) : Matrix m r ℝ :=
  P.map (fun p => MvPolynomial.bernsteinCoeff n p k)

/-- Matrix Bernstein coefficients are the scalar coefficients of each entry. -/
@[simp] theorem bernsteinCoeff_apply (n : ι → ℕ) (P : Matrix m r (MvPolynomial ι ℝ))
    (k : ι → ℕ) (a : m) (b : r) :
    bernsteinCoeff n P k a b = MvPolynomial.bernsteinCoeff n (P a b) k := rfl

/-- If every entry of a real polynomial matrix has each coordinate degree at
most `n i`, its evaluation is the Bernstein-weighted sum of its coefficient
matrices. The variable type is finite; the degree vector is shared by all
entries and may be heterogeneous or have zero coordinates. -/
theorem map_eval_eq_sum_bernstein [DecidableEq ι] {n : ι → ℕ} {P : Matrix m r (MvPolynomial ι ℝ)}
    (hp : ∀ a b i, (P a b).degreeOf i ≤ n i) (x : ι → ℝ) :
    P.map (eval x) = ∑ k : (i : ι) → Fin (n i + 1),
      eval x (MvPolynomial.bernstein n (fun i => k i)) •
        bernsteinCoeff n P (fun i => k i) := by
  classical
  ext a b
  simpa only [map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    bernsteinCoeff_apply, mul_comm]
    using MvPolynomial.eval_eq_sum_bernstein (hp a b) x

/-- On the closed unit cube, a fixed real matrix lower bound for every valid
Bernstein coefficient matrix is a lower bound for the evaluated polynomial
matrix. Every entry must satisfy the same coordinate-degree bound `n`.
The conclusion expresses the bound by a positive-semidefinite difference. -/
theorem posSemidef_map_eval_sub_of_bernsteinCoeff {n : ι → ℕ}
    {P : Matrix m m (MvPolynomial ι ℝ)} (hp : ∀ a b i, (P a b).degreeOf i ≤ n i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Icc 0 1) {L : Matrix m m ℝ}
    (hc : ∀ k : (i : ι) → Fin (n i + 1),
      (bernsteinCoeff n P (fun i => k i) - L).PosSemidef) :
    (P.map (eval x) - L).PosSemidef := by
  classical
  rw [map_eval_eq_sum_bernstein hp]
  exact posSemidef_sum_smul_sub univ (fun k _ => eval_bernstein_nonneg _ _ hx)
    (sum_eval_bernstein n x) (fun k _ => hc k)

/-- Positive-semidefinite valid Bernstein coefficient matrices imply
positive-semidefinite evaluation throughout the closed unit cube, provided
every polynomial entry satisfies the common coordinate-degree bound. -/
theorem posSemidef_map_eval_of_bernsteinCoeff {n : ι → ℕ}
    {P : Matrix m m (MvPolynomial ι ℝ)} (hp : ∀ a b i, (P a b).degreeOf i ≤ n i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Icc 0 1)
    (hc : ∀ k : (i : ι) → Fin (n i + 1),
      (bernsteinCoeff n P (fun i => k i)).PosSemidef) :
    (P.map (eval x)).PosSemidef := by
  simpa only [sub_zero] using posSemidef_map_eval_sub_of_bernsteinCoeff hp hx
    (L := 0) (fun k => by simpa only [sub_zero] using hc k)

/-- Suppose every valid Bernstein coefficient matrix exceeds `δ` times the
identity by a positive-semidefinite matrix, with a common coordinate-degree
bound for all entries and a finite matrix index type. On the closed unit cube
its quadratic form is at least
`δ` times the sum of squared vector components, uniformly in the point and
vector. No positivity assumption on `δ` is needed for this lower bound. -/
theorem quadraticForm_lower_bound_of_bernsteinCoeff [Fintype m] [DecidableEq m]
    {n : ι → ℕ} {P : Matrix m m (MvPolynomial ι ℝ)}
    (hp : ∀ a b i, (P a b).degreeOf i ≤ n i) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc 0 1) {δ : ℝ}
    (hc : ∀ k : (i : ι) → Fin (n i + 1),
      (bernsteinCoeff n P (fun i => k i) - δ • 1).PosSemidef) (v : m → ℝ) :
    δ * ∑ a, (v a)^2 ≤ v ⬝ᵥ (P.map (eval x) *ᵥ v) := by
  have h := (posSemidef_map_eval_sub_of_bernsteinCoeff hp hx hc).dotProduct_mulVec_nonneg v
  simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul] at h
  simpa only [dotProduct, ← pow_two] using sub_nonneg.mp h

/-- A strictly positive uniform identity margin on all valid Bernstein
coefficient matrices makes the evaluated real polynomial matrix positive
definite throughout the closed unit cube. Every entry satisfies the common
coordinate-degree bound; no nonempty matrix-index assumption is needed. -/
theorem posDef_map_eval_of_bernsteinCoeff [DecidableEq m]
    {n : ι → ℕ} {P : Matrix m m (MvPolynomial ι ℝ)}
    (hp : ∀ a b i, (P a b).degreeOf i ≤ n i) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc 0 1) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ k : (i : ι) → Fin (n i + 1),
      (bernsteinCoeff n P (fun i => k i) - δ • 1).PosSemidef) :
    (P.map (eval x)).PosDef := by
  have h := (PosDef.one.smul hδ).add_posSemidef
    (posSemidef_map_eval_sub_of_bernsteinCoeff hp hx hc)
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

/-- Suppose every entry of a real polynomial matrix has coordinate degrees
bounded by the same vector `n`. On an ordered closed box `[a,b]`, a fixed
matrix lower bound for all valid Bernstein coefficient matrices of the
entrywise affine pullback is a lower bound for the original evaluation.
Zero-width coordinates, empty variable types and arbitrary fixed `L` are
allowed; the bound means that the matrix difference is positive semidefinite. -/
theorem posSemidef_map_eval_sub_of_bernsteinCoeff_box {n : ι → ℕ}
    {P : Matrix m m (MvPolynomial ι ℝ)} (hp : ∀ r c i, (P r c).degreeOf i ≤ n i)
    {a b : ι → ℝ} (hab : ∀ i, a i ≤ b i) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc (a i) (b i)) {L : Matrix m m ℝ}
    (hc : ∀ k : (i : ι) → Fin (n i + 1),
      (bernsteinCoeff n (P.map (boxPullback a b)) (fun i => k i) - L).PosSemidef) :
    (P.map (eval x) - L).PosSemidef := by
  classical
  choose t ht heq using fun i => exists_unit_parameter (hab i) (hx i)
  have h := posSemidef_map_eval_sub_of_bernsteinCoeff
    (P := P.map (boxPullback a b))
    (fun r c i => (degreeOf_boxPullback_le a b (P r c) i).trans (hp r c i)) ht hc
  have hmap : (P.map (boxPullback a b)).map (eval t) = P.map (eval x) := by
    ext r c
    change eval t (boxPullback a b (P r c)) = eval x (P r c)
    simp only [eval_boxPullback, heq]
  rwa [hmap] at h

/-- Positive-semidefinite Bernstein coefficient matrices of the entrywise
box pullback imply positive-semidefinite evaluation throughout an ordered
closed box. Every entry satisfies the same coordinate-degree bound; zero
widths and empty variable types are allowed. -/
theorem posSemidef_map_eval_of_bernsteinCoeff_box {n : ι → ℕ}
    {P : Matrix m m (MvPolynomial ι ℝ)} (hp : ∀ r c i, (P r c).degreeOf i ≤ n i)
    {a b : ι → ℝ} (hab : ∀ i, a i ≤ b i) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc (a i) (b i))
    (hc : ∀ k : (i : ι) → Fin (n i + 1),
      (bernsteinCoeff n (P.map (boxPullback a b)) (fun i => k i)).PosSemidef) :
    (P.map (eval x)).PosSemidef := by
  simpa only [sub_zero] using posSemidef_map_eval_sub_of_bernsteinCoeff_box hp hab hx
    (L := 0) (fun k => by simpa only [sub_zero] using hc k)

/-- A uniform identity margin `δ` on the Bernstein coefficient matrices of
the entrywise pullback gives the quadratic-form lower bound `δ * ∑ i, v i²`
for every vector and every point of the ordered closed box, with a finite
matrix index type. All entries share the coordinate-degree bound, and
zero-width coordinates are allowed.
The scalar margin need not be positive for this lower-bound statement. -/
theorem quadraticForm_lower_bound_of_bernsteinCoeff_box [Fintype m] [DecidableEq m]
    {n : ι → ℕ} {P : Matrix m m (MvPolynomial ι ℝ)}
    (hp : ∀ r c i, (P r c).degreeOf i ≤ n i)
    {a b : ι → ℝ} (hab : ∀ i, a i ≤ b i) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc (a i) (b i)) {δ : ℝ}
    (hc : ∀ k : (i : ι) → Fin (n i + 1),
      (bernsteinCoeff n (P.map (boxPullback a b)) (fun i => k i) - δ • 1).PosSemidef)
    (v : m → ℝ) : δ * ∑ r, (v r)^2 ≤ v ⬝ᵥ (P.map (eval x) *ᵥ v) := by
  have h := (posSemidef_map_eval_sub_of_bernsteinCoeff_box hp hab hx hc).dotProduct_mulVec_nonneg v
  simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul] at h
  simpa only [dotProduct, ← pow_two] using sub_nonneg.mp h

/-- A strictly positive identity margin on every Bernstein coefficient
matrix of the box pullback makes the evaluated polynomial matrix positive
definite throughout the ordered closed box. All entries share the degree
bound; zero-width coordinates and zero-size matrices are allowed. -/
theorem posDef_map_eval_of_bernsteinCoeff_box [DecidableEq m]
    {n : ι → ℕ} {P : Matrix m m (MvPolynomial ι ℝ)}
    (hp : ∀ r c i, (P r c).degreeOf i ≤ n i)
    {a b : ι → ℝ} (hab : ∀ i, a i ≤ b i) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc (a i) (b i)) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ k : (i : ι) → Fin (n i + 1),
      (bernsteinCoeff n (P.map (boxPullback a b)) (fun i => k i) - δ • 1).PosSemidef) :
    (P.map (eval x)).PosDef := by
  have h := (PosDef.one.smul hδ).add_posSemidef
    (posSemidef_map_eval_sub_of_bernsteinCoeff_box hp hab hx hc)
  simpa only [← add_sub_assoc, add_sub_cancel_left] using h

end Matrix
