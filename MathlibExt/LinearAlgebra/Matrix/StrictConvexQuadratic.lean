/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Convexity and minimization of real matrix quadratics

For a real symmetric matrix `A`, the Jensen gap of `q(x) = x ⬝ᵥ (A *ᵥ x)` is
`a * b * q(x - y)` for weights `a + b = 1`. This gives convexity for positive semidefinite
matrices and strict convexity for positive definite ones.

For positive semidefinite `A`, the minimizers of `q(x) - 2 * (b ⬝ᵥ x)` are the solutions of
`A *ᵥ x = b`. A nonempty solution set is a translate of the kernel. Off the range, the
objective tends to minus infinity along a ray in the kernel.

## Reference

S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§3.1.4, Example 3.2 (<https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf>) treats
convexity and strict convexity of `½ xᵀ P x + qᵀ x + r`; the pure quadratic here has
`P = 2A`, `q = 0`, and `r = 0`. The gap and minimizer results below are derived directly.
-/

@[expose] public section

open Matrix Filter

namespace MetaMathlibExt.Matrix

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ}

private lemma dotProduct_mulVec_comm (hA : A.IsHermitian) (x y : n → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  simpa only [star_trivial] using hA.star_dotProduct_mulVec_comm x y

/-- For a real symmetric matrix and weights `a + b = 1`, the Jensen gap of the quadratic
form `q` is `a * b * q (x - y)`. The identity does not require nonnegative weights. -/
theorem quadratic_jensen_gap (hA : A.IsSymm) (x y : n → ℝ) (a b : ℝ) (hab : a + b = 1) :
    a * (x ⬝ᵥ (A *ᵥ x)) + b * (y ⬝ᵥ (A *ᵥ y)) -
        ((a • x + b • y) ⬝ᵥ (A *ᵥ (a • x + b • y))) =
      a * b * ((x - y) ⬝ᵥ (A *ᵥ (x - y))) := by
  have hb : b = 1 - a := by linarith only [hab]
  subst b
  simp only [mulVec_add, mulVec_sub, mulVec_smul, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_mulVec_comm (isHermitian_iff_isSymm.mpr hA) y x]
  ring

/-- The quadratic form `x ↦ xᵀ A x` of a real positive definite matrix is strictly convex. -/
theorem strictConvexOn_quadratic_of_posDef (hA : A.PosDef) :
    StrictConvexOn ℝ Set.univ (fun x ↦ x ⬝ᵥ (A *ᵥ x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hq : 0 < (x - y) ⬝ᵥ (A *ᵥ (x - y)) := by
    simpa only [star_trivial] using hA.dotProduct_mulVec_pos (sub_ne_zero.mpr hxy)
  simpa only [smul_eq_mul] using sub_pos.mp
    ((quadratic_jensen_gap hA.isHermitian.isSymm x y a b hab).symm ▸
      mul_pos (mul_pos ha hb) hq)

/-- The quadratic form of a real positive semidefinite matrix is convex. -/
theorem convexOn_quadratic_of_posSemidef (hA : A.PosSemidef) :
    ConvexOn ℝ Set.univ (fun x ↦ x ⬝ᵥ (A *ᵥ x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hq : 0 ≤ (x - y) ⬝ᵥ (A *ᵥ (x - y)) := by
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg (x - y)
  simpa only [smul_eq_mul] using sub_nonneg.mp
    ((quadratic_jensen_gap hA.isHermitian.isSymm x y a b hab).symm ▸
      mul_nonneg (mul_nonneg ha hb) hq)

/-- For strictly positive weights, the Jensen gap of a positive semidefinite quadratic
vanishes exactly when the difference of the two points belongs to the kernel. -/
theorem quadratic_jensen_gap_eq_zero_iff (hA : A.PosSemidef) (x y : n → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * (x ⬝ᵥ (A *ᵥ x)) + b * (y ⬝ᵥ (A *ᵥ y)) -
        ((a • x + b • y) ⬝ᵥ (A *ᵥ (a • x + b • y))) = 0 ↔
      A *ᵥ (x - y) = 0 := by
  rw [quadratic_jensen_gap hA.isHermitian.isSymm x y a b hab,
    mul_eq_zero, or_iff_right (mul_pos ha hb).ne']
  simpa only [star_trivial] using hA.dotProduct_mulVec_zero_iff (x := x - y)

/-- The quadratic form of a real symmetric matrix is constant on each translate of its kernel. -/
theorem quadratic_add_of_mulVec_eq_zero (hA : A.IsSymm) {v : n → ℝ}
    (hv : A *ᵥ v = 0) (x : n → ℝ) :
    (x + v) ⬝ᵥ (A *ᵥ (x + v)) = x ⬝ᵥ (A *ᵥ x) := by
  simp only [mulVec_add, hv, add_zero, add_dotProduct]
  rw [dotProduct_mulVec_comm (isHermitian_iff_isSymm.mpr hA) v x, hv, dotProduct_zero, add_zero]

private lemma exists_ne_zero_mulVec_eq_zero_of_det_eq_zero [DecidableEq n] (hd : A.det = 0) :
    ∃ v : n → ℝ, v ≠ 0 ∧ A *ᵥ v = 0 := by
  have h : ¬ Function.Injective A.mulVec := by
    rw [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact not_not_intro hd
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp h
  exact ⟨x - y, sub_ne_zero.mpr hne, by rw [mulVec_sub, hxy, sub_self]⟩

/-- A real singular matrix does not define a strictly convex quadratic form. -/
theorem not_strictConvexOn_quadratic_of_det_eq_zero [DecidableEq n] (hd : A.det = 0) :
    ¬ StrictConvexOn ℝ Set.univ (fun x ↦ x ⬝ᵥ (A *ᵥ x)) := by
  obtain ⟨v, hne, hv⟩ := exists_ne_zero_mulVec_eq_zero_of_det_eq_zero hd
  rintro ⟨_, hstrict⟩
  have hmid := hstrict (x := v) (y := 0) (Set.mem_univ _) (Set.mem_univ _) hne
    (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  simp only [mulVec_smul, mulVec_zero, hv, dotProduct_zero, smul_zero, add_zero, lt_irrefl] at hmid

private lemma exists_mulVec_eq_zero_dotProduct_pos (hA : A.IsHermitian) {b : n → ℝ}
    (hb : b ∉ Set.range A.mulVec) : ∃ v : n → ℝ, A *ᵥ v = 0 ∧ 0 < b ⬝ᵥ v := by
  classical
  let L := A.toEuclideanLin
  have hAdj : L.adjoint = L := by
    change A.toEuclideanLin.adjoint = A.toEuclideanLin
    rw [← toEuclideanLin_conjTranspose_eq_adjoint, hA.eq]
  have horth : L.kerᗮ = L.range := by rw [LinearMap.orthogonal_ker, hAdj]
  have hbr : WithLp.toLp 2 b ∉ L.kerᗮ := by
    rw [horth]
    rintro ⟨x, hx⟩
    exact hb ⟨WithLp.ofLp x, congrArg WithLp.ofLp hx⟩
  rw [Submodule.mem_orthogonal'] at hbr
  push Not at hbr
  obtain ⟨u, hu, hbu⟩ := hbr
  let v := WithLp.ofLp u
  have hv : A *ᵥ v = 0 := congrArg WithLp.ofLp (LinearMap.mem_ker.mp hu)
  have hne : b ⬝ᵥ v ≠ 0 := by
    rw [dotProduct_comm b v]
    simpa only [v, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial]
      using hbu
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact ⟨-v, by rw [mulVec_neg, hv, neg_zero], by rwa [dotProduct_neg, neg_pos]⟩
  · exact ⟨v, hv, hpos⟩

/-- If `b` is outside the range of a real symmetric `A`, there is a kernel direction `v`
with `bᵀ v > 0`. Along `t • v`, the objective `xᵀ A x - 2 bᵀ x` tends to minus infinity
as `t` tends to plus infinity. -/
theorem exists_tendsto_quadratic_sub_linear_atBot_of_not_mem_range (hA : A.IsSymm)
    {b : n → ℝ} (hb : b ∉ Set.range A.mulVec) :
    ∃ v : n → ℝ, A *ᵥ v = 0 ∧ 0 < b ⬝ᵥ v ∧
      Tendsto (fun t : ℝ ↦ (t • v) ⬝ᵥ (A *ᵥ (t • v)) - 2 * (b ⬝ᵥ (t • v))) atTop atBot := by
  obtain ⟨v, hv, hbv⟩ := exists_mulVec_eq_zero_dotProduct_pos (isHermitian_iff_isSymm.mpr hA) hb
  refine ⟨v, hv, hbv, ?_⟩
  have heq (t : ℝ) : (t • v) ⬝ᵥ (A *ᵥ (t • v)) - 2 * (b ⬝ᵥ (t • v)) =
      (-(2 * (b ⬝ᵥ v))) * t := by
    simp only [mulVec_smul, hv, smul_zero, dotProduct_zero, dotProduct_smul, smul_eq_mul]
    ring
  simp_rw [heq]
  exact tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr (mul_pos zero_lt_two hbv))

private lemma quadratic_sub_linear_sub_of_mulVec_eq (hA : A.IsHermitian)
    {b y : n → ℝ} (hy : A *ᵥ y = b) (x : n → ℝ) :
    (x ⬝ᵥ (A *ᵥ x) - 2 * (b ⬝ᵥ x)) - (y ⬝ᵥ (A *ᵥ y) - 2 * (b ⬝ᵥ y)) =
      (x - y) ⬝ᵥ (A *ᵥ (x - y)) := by
  rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, dotProduct_mulVec_comm hA y x,
    hy, dotProduct_comm b x, dotProduct_comm b y]
  ring

/-- For a real positive semidefinite `A`, the minimizing set of `xᵀ A x - 2 bᵀ x` is
exactly the preimage of `b` under `x ↦ A *ᵥ x`. -/
theorem isMinOn_quadratic_sub_linear_iff (hA : A.PosSemidef) (b x : n → ℝ) :
    IsMinOn (fun y ↦ y ⬝ᵥ (A *ᵥ y) - 2 * (b ⬝ᵥ y)) Set.univ x ↔ A *ᵥ x = b := by
  rw [isMinOn_univ_iff]
  constructor
  · intro hx
    have hb : b ∈ Set.range A.mulVec := by
      by_contra h
      obtain ⟨v, _, _, hlim⟩ :=
        exists_tendsto_quadratic_sub_linear_atBot_of_not_mem_range hA.isHermitian.isSymm h
      obtain ⟨t, ht⟩ := (hlim.eventually_lt_atBot (x ⬝ᵥ (A *ᵥ x) - 2 * (b ⬝ᵥ x))).exists
      exact (not_lt_of_ge (hx (t • v))) ht
    obtain ⟨y, hy⟩ := hb
    have hq : (x - y) ⬝ᵥ (A *ᵥ (x - y)) = 0 := by
      refine le_antisymm ?_ ?_
      · rw [← quadratic_sub_linear_sub_of_mulVec_eq hA.isHermitian hy x]
        exact sub_nonpos.mpr (hx y)
      · simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg (x - y)
    have hk : A *ᵥ (x - y) = 0 := hA.dotProduct_mulVec_zero_iff.mp (by simpa only [star_trivial])
    rwa [mulVec_sub, sub_eq_zero, hy] at hk
  · intro hx y
    apply sub_nonneg.mp
    rw [quadratic_sub_linear_sub_of_mulVec_eq hA.isHermitian hx y]
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg (y - x)

/-- A positive semidefinite quadratic with linear term attains its minimum exactly when
the linear term's vector `b` is in the range of `A`. -/
theorem exists_isMinOn_quadratic_sub_linear_iff (hA : A.PosSemidef) (b : n → ℝ) :
    (∃ x, IsMinOn (fun y ↦ y ⬝ᵥ (A *ᵥ y) - 2 * (b ⬝ᵥ y)) Set.univ x) ↔
      b ∈ Set.range A.mulVec := by
  simp_rw [isMinOn_quadratic_sub_linear_iff hA]
  rfl

/-- Every minimizer of a singular positive semidefinite quadratic has another, distinct
minimizer, obtained by adding a nonzero vector in the kernel. -/
theorem exists_ne_isMinOn_quadratic_sub_linear_of_det_eq_zero [DecidableEq n]
    (hA : A.PosSemidef) (hd : A.det = 0) {b x : n → ℝ}
    (hx : IsMinOn (fun y ↦ y ⬝ᵥ (A *ᵥ y) - 2 * (b ⬝ᵥ y)) Set.univ x) :
    ∃ y, y ≠ x ∧ IsMinOn (fun z ↦ z ⬝ᵥ (A *ᵥ z) - 2 * (b ⬝ᵥ z)) Set.univ y := by
  obtain ⟨v, hne, hv⟩ := exists_ne_zero_mulVec_eq_zero_of_det_eq_zero hd
  rw [isMinOn_quadratic_sub_linear_iff hA] at hx
  refine ⟨x + v, by simpa using hne, (isMinOn_quadratic_sub_linear_iff hA b _).mpr ?_⟩
  rw [mulVec_add, hx, hv, add_zero]

end MetaMathlibExt.Matrix
