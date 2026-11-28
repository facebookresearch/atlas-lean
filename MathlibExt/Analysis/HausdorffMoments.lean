/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/HausdorffMoments.lean` (leanprover/lean-eval) at commit
38361be884302c7edce1908c4aef8296eb2cb27e, via `WantedExt/Analysis/HausdorffMomentsWanted.lean`.
Copyright 2026 Lean FRO, LLC. Authors: Kim Morrison.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The adapted portions are the moment and difference definitions and the statements of
`hausdorff_positivity` and `hausdorff_hildebrandt_schoenberg`.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Data.Pi.Interval
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import MathlibExt.RingTheory.MvPolynomial.Bernstein
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.Ring

/-!
# Hausdorff moment criteria on the unit cube

`hausdorff_positivity` characterizes the moments of finite positive measures on the cube by
nonnegativity of the iterated backward differences at all coordinatewise indices `k ≤ n`.
`hausdorff_hildebrandt_schoenberg` characterizes the signed moments by a uniform bound in `n`
on the sum of the absolute binomial-weighted backward differences for `k ≤ n`. The two finite
positive measures in the signed criterion represent their difference on the cube. The result
also covers dimension zero, where the cube is a point and the sole moment may be any real number.

The signed proof bounds the moment functional on polynomials in the supremum norm using the
Bernstein basis. It extends a positive functional on pairs of polynomial restrictions to
pairs of continuous functions and applies positive measure representation to each axis.

## References

* T. H. Hildebrandt and I. J. Schoenberg, *On Linear Functional Operations and the Moment Problem
  for a Finite Interval in One or Several Dimensions*, Annals of Mathematics **34** (1933),
  317–328, the multidimensional moment criterion, DOI 10.2307/1968205.
* Felix Hausdorff, *Summationsmethoden und Momentfolgen. I* and
  *Summationsmethoden und Momentfolgen. II*, Mathematische Zeitschrift **9** (1921), 74–109 and
  280–299; *Momentprobleme für ein endliches Intervall.*, Mathematische Zeitschrift **16**
  (1923), 220–248, for the interval.
* Oliver Knill, *Some Fundamental Theorems in Mathematics*, §115 ("Moments"), for the signed
  formulation with backward differences.

## Implementation notes

The signed proof reuses the Bernstein coefficient limit and Riesz representation argument of
`hausdorff_positivity`, and the basis expansion `MvPolynomial.eq_sum_bernstein` from
`MathlibExt.RingTheory.MvPolynomial.Bernstein`.
-/

@[expose] public section

namespace MathlibExt.Analysis.HausdorffMomentsWanted.Analysis

open MeasureTheory
open scoped BigOperators NNReal

set_option linter.dupNamespace false in
/-- **Unit cube of the Hausdorff moment problem.** For $d \in \mathbb{N}$, the closed unit cube
$I^d = [0,1]^d$ is the set of points $x \in \mathbb{R}^d$ with $0 \le x_i \le 1$ for every
coordinate $i$. -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

set_option linter.dupNamespace false in
/-- **Multi-index monomial.** For a multi-index $n \in \mathbb{N}^d$, the monomial $x^n$ is the
real function on $\mathbb{R}^d$ given by $x^n = \prod_i x_i^{n_i}$. -/
def monomial {d : ℕ} (n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := ∏ i, (x i) ^ (n i)

set_option linter.dupNamespace false in
/-- **Moments on the unit cube.** For a measure $\mu$ on $\mathbb{R}^d$ and a multi-index
$n \in \mathbb{N}^d$, the $n$-th moment of $\mu$ on the unit cube is the real number
$\int_{[0,1]^d} x^n \, d\mu(x)$, where $x^n = \prod_i x_i^{n_i}$.

When $x^n$ is not $\mu$-integrable on $[0,1]^d$, this integral is taken to be $0$. -/
noncomputable def momentOf {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (n : Fin d → ℕ) : ℝ :=
  ∫ x in cube d, monomial n x ∂μ

set_option linter.dupNamespace false in
/-- **Moment sequences of signed measures on the cube.** A real sequence $a$ indexed by
$\mathbb{N}^d$ is a moment configuration if there are finite measures $\mu$ and $\nu$ on
$\mathbb{R}^d$ such that for every multi-index $n \in \mathbb{N}^d$,
$$a_n = \int_{[0,1]^d} x^n \, d\mu(x) - \int_{[0,1]^d} x^n \, d\nu(x),$$
where $x^n = \prod_i x_i^{n_i}$.

This encodes a signed measure of bounded variation on the cube by its Jordan decomposition
$\mu - \nu$. -/
def IsMomentConfiguration {d : ℕ} (a : (Fin d → ℕ) → ℝ) : Prop :=
  ∃ μ ν : Measure (EuclideanSpace ℝ (Fin d)), IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧
    ∀ n, a n = momentOf μ n - momentOf ν n

set_option linter.dupNamespace false in
/-- **Multi-index binomial coefficient.** For multi-indices $n, k \in \mathbb{N}^d$, the binomial
coefficient $\binom{n}{k}$ is the natural number $\prod_i \binom{n_i}{k_i}$. -/
def multiChoose {d : ℕ} (n k : Fin d → ℕ) : ℕ := ∏ i, (n i).choose (k i)

set_option linter.dupNamespace false in
/-- **Iterated backward difference.** For a real sequence $a$ indexed by $\mathbb{N}^d$ and
multi-indices $k, n \in \mathbb{N}^d$, the iterated backward difference of $a$ is the real number
$$(\Delta^k a)_n = \sum_{j \le k} (-1)^{|k| - |j|} \binom{k}{j} a_{n - j},$$
where $j$ ranges over the multi-indices with $j \le k$ coordinatewise, $|j| = \sum_i j_i$,
$\binom{k}{j} = \prod_i \binom{k_i}{j_i}$, and $n - j$ is computed coordinatewise in $\mathbb{N}$,
with $n_i - j_i = 0$ when $j_i > n_i$.

For $k \le n$ no truncation occurs, and $\Delta^k a$ is the iterate of the backward partial
differences $(\Delta_i a)_n = a_{n - e_i} - a_n$, applied $k_i$ times in each coordinate $i$,
where $e_i \in \mathbb{N}^d$ is the $i$-th unit multi-index. -/
noncomputable def diff {d : ℕ} (a : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) : ℝ :=
  ∑ j ∈ Finset.Iic k,
    (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * a (n - j)

set_option linter.dupNamespace false in
/-- The iterated backward difference of a pointwise difference is the difference of the
iterated backward differences. -/
public theorem diff_sub {d : ℕ} (a b : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) :
    diff (fun m => a m - b m) k n = diff a k n - diff b k n := by
  simp only [diff, mul_sub, Finset.sum_sub_distrib]

set_option linter.dupNamespace false in
/-- **Hausdorff-bounded sequences.** A real sequence $a$ indexed by $\mathbb{N}^d$ is Hausdorff
bounded if there is a real constant $M$ such that for every multi-index $n \in \mathbb{N}^d$,
$$\sum_{k \le n} \left| \binom{n}{k} (\Delta^k a)_n \right| \le M,$$
where $k$ ranges over the multi-indices with $k \le n$ coordinatewise,
$\binom{n}{k} = \prod_i \binom{n_i}{k_i}$ is the multi-index binomial coefficient, and
$\Delta^k a$ is the iterated backward difference of $a$. -/
def HausdorffBounded {d : ℕ} (a : (Fin d → ℕ) → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : Fin d → ℕ,
    ∑ k ∈ Finset.Iic n, |(multiChoose n k : ℝ) * diff a k n| ≤ C

set_option linter.dupNamespace false in
/-- A sequence is Hausdorff bounded exactly when the absolute binomial-weighted differences
have a uniform sum bound over all degree boxes. -/
public theorem hausdorffBounded_iff {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    HausdorffBounded a ↔ ∃ C : ℝ, ∀ n : Fin d → ℕ,
      ∑ k ∈ Finset.Iic n, |(multiChoose n k : ℝ) * diff a k n| ≤ C :=
  Iff.rfl

set_option linter.dupNamespace false in
/-- **Moment sequences of positive measures on the cube.** A real sequence $a$ indexed by
$\mathbb{N}^d$ is a positive moment configuration if there is a finite measure $\mu$ on
$\mathbb{R}^d$ such that $a_n = \int_{[0,1]^d} x^n \, d\mu(x)$ for every multi-index
$n \in \mathbb{N}^d$, where $x^n = \prod_i x_i^{n_i}$. -/
def IsPositiveMomentConfiguration {d : ℕ} (a : (Fin d → ℕ) → ℝ) : Prop :=
  ∃ μ : Measure (EuclideanSpace ℝ (Fin d)), IsFiniteMeasure μ ∧ ∀ n, a n = momentOf μ n

open Finset Filter Topology
open scoped CompactlySupported

variable {d : ℕ}

set_option linter.dupNamespace false in
/-- In function coordinates, the closed unit cube is the interval from the zero vector
to the vector of ones. -/
lemma cube_eq_preimage_Icc :
    cube d = WithLp.ofLp ⁻¹' Set.Icc (0 : Fin d → ℝ) 1 := by
  ext x
  exact forall_and

set_option linter.dupNamespace false in
/-- The multivariate monomial evaluates to the product of the coordinate powers. -/
lemma monomial_apply (n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    monomial n x = ∏ i, (x i) ^ (n i) := rfl

set_option linter.dupNamespace false in
/-- The moment of a measure at a multi-index is the integral of its monomial over the cube. -/
lemma momentOf_eq_integral (μ : Measure (EuclideanSpace ℝ (Fin d))) (n : Fin d → ℕ) :
    momentOf μ n = ∫ x in cube d, monomial n x ∂μ := rfl

set_option linter.dupNamespace false in
/-- A positive moment configuration is witnessed by a finite measure with the prescribed moments
on the cube. -/
lemma isPositiveMomentConfiguration_iff (a : (Fin d → ℕ) → ℝ) :
    IsPositiveMomentConfiguration a ↔
      ∃ μ : Measure (EuclideanSpace ℝ (Fin d)), IsFiniteMeasure μ ∧ ∀ n, a n = momentOf μ n :=
  Iff.rfl

set_option linter.dupNamespace false in
/-- Backward differences distribute over a constant multiple of one sequence minus another. -/
lemma diff_const_mul_sub (c : ℝ) (a b : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) :
    diff (fun j => c * a j - b j) k n = c * diff a k n - diff b k n := by
  simp only [diff, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

set_option linter.dupNamespace false in
/-- The backward difference of order zero at the origin is the value at the origin. -/
lemma diff_zero_zero (a : (Fin d → ℕ) → ℝ) : diff a 0 0 = a 0 := by
  have hIic : Finset.Iic (0 : Fin d → ℕ) = {0} := Finset.Iic_bot
  have hsub : (0 : Fin d → ℕ) - 0 = 0 := funext fun _ => Nat.sub_zero 0
  simp [diff, multiChoose, hIic, hsub]

private abbrev Box (d : ℕ) := Fin d → Set.Icc (0 : ℝ) 1

private def embedBox (x : Box d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (x i : ℝ))

private theorem continuous_embedBox : Continuous (embedBox (d := d)) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_subtype_val.comp
    (continuous_apply i))

set_option linter.dupNamespace false in
/-- The closed unit cube is compact. -/
lemma isCompact_cube : IsCompact (cube d) := by
  have heq : cube d = Set.range (embedBox (d := d)) := by
    ext x
    constructor
    · intro hx
      exact ⟨fun i => ⟨x i, hx i⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact fun i => (y i).property
  rw [heq]
  exact isCompact_range continuous_embedBox

set_option linter.dupNamespace false in
/-- Every multivariate monomial is continuous on Euclidean space. -/
lemma continuous_monomial (n : Fin d → ℕ) : Continuous (monomial n) :=
  continuous_finsetProd _ fun i _ => (PiLp.continuous_apply 2 _ i).pow _

-- Expand each complementary power and collect the coordinate sums into the multi-index box.
private theorem kernel_expand {R : Type*} [CommRing R] [Algebra ℝ R] (x : Fin d → R)
    {k n : Fin d → ℕ} (h : k ≤ n) :
    (∏ i, x i ^ (n i - k i) * (1 - x i) ^ k i) =
      ∑ j ∈ Iic k, ((-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ)) •
        ∏ i, x i ^ (n i - j i) := by
  classical
  have coord (i : Fin d) :
      x i ^ (n i - k i) * (1 - x i) ^ k i =
        ∑ j ∈ Iic (k i), (-1 : R) ^ (k i - j) * ((k i).choose j : R) * x i ^ (n i - j) := by
    rw [sub_eq_add_neg, add_pow, mul_sum, ← Nat.range_succ_eq_Iic]
    apply sum_congr rfl
    intro j hj
    have hjk : j ≤ k i := by simpa using hj
    have he : n i - j = (n i - k i) + (k i - j) := by
      have hkn : k i ≤ n i := h i
      omega
    rw [he, pow_add, neg_eq_neg_one_mul (x i), mul_pow, one_pow]
    ring
  simp_rw [coord]
  rw [prod_univ_sum]
  apply sum_congr rfl
  intro j _
  simp [prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum, multiChoose, Algebra.smul_def]

set_option linter.dupNamespace false in
/-- For the monomial sequence of a point, the binomial-weighted backward difference at
`k ≤ n` is the product of the coordinate Bernstein weights at complementary indices. -/
public theorem weighted_diff_prod_pow (x : Fin d → ℝ) {k n : Fin d → ℕ} (h : k ≤ n) :
    (multiChoose n k : ℝ) * diff (fun m => ∏ i, x i ^ m i) k n =
      ∏ i, ((n i).choose (k i) : ℝ) * x i ^ (n i - k i) * (1 - x i) ^ k i := by
  have hd : diff (fun m => ∏ i, x i ^ m i) k n =
      ∏ i, x i ^ (n i - k i) * (1 - x i) ^ k i := by
    simpa only [diff, Pi.sub_apply, smul_eq_mul] using (kernel_expand x h).symm
  simp only [hd, multiChoose, Nat.cast_prod, ← Finset.prod_mul_distrib, mul_assoc]

private theorem diff_moment_nonneg {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure μ]
    {k n : Fin d → ℕ} (h : k ≤ n) : 0 ≤ diff (momentOf μ) k n := by
  let c (j : Fin d → ℕ) := (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ)
  change 0 ≤ ∑ j ∈ Iic k, c j * ∫ x in cube d, monomial (n - j) x ∂μ
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum]
  · apply setIntegral_nonneg isCompact_cube.measurableSet
    intro x hx
    change 0 ≤ ∑ j ∈ Iic k, c j • ∏ i, x i ^ (n i - j i)
    rw [← kernel_expand (fun i => x i) h]
    exact prod_nonneg fun i _ => mul_nonneg (pow_nonneg (hx i).1 _)
      (pow_nonneg (sub_nonneg.mpr (hx i).2) _)
  · exact fun j _ => ((continuous_monomial (n - j)).continuousOn.integrableOn_compact
      isCompact_cube).const_mul _

private abbrev Poly (d : ℕ) := MvPolynomial (Fin d) ℝ

private noncomputable def functional (a : (Fin d → ℕ) → ℝ) : Poly d →ₗ[ℝ] ℝ :=
  (MvPolynomial.basisMonomials (Fin d) ℝ).constr ℝ fun s => a s

private theorem functional_monomial (a : (Fin d → ℕ) → ℝ) (n : Fin d → ℕ) :
    functional a (∏ i, MvPolynomial.X i ^ n i) = a n := by
  rw [MvPolynomial.prod_X_pow]
  change (MvPolynomial.basisMonomials (Fin d) ℝ).constr ℝ _ ((MvPolynomial.basisMonomials
    (Fin d) ℝ) _) = _
  rw [Module.Basis.constr_basis]
  congr 1
  ext
  simp

private theorem functional_bernstein (a : (Fin d → ℕ) → ℝ) {k n : Fin d → ℕ} (h : k ≤ n) :
    functional a (MvPolynomial.bernstein n k) = (multiChoose n k : ℝ) * diff a (n - k) n := by
  classical
  have hk : n - k ≤ n := fun i => Nat.sub_le _ _
  have he (i : Fin d) : n i - (n i - k i) = k i := Nat.sub_sub_self (h i)
  have hb : MvPolynomial.bernstein n k = (multiChoose n k : ℝ) •
      ∏ i, MvPolynomial.X i ^ (n i - (n - k) i) * (1 - MvPolynomial.X i) ^ (n - k) i := by
    simp [MvPolynomial.bernstein, MvPolynomial.smul_eq_C_mul, multiChoose, prod_mul_distrib, he,
      Pi.sub_apply, mul_assoc]
  rw [hb, kernel_expand _ hk, map_smul, map_sum]
  simp only [map_smul, functional_monomial, smul_eq_mul, diff]
  rfl

-- At a grid point u/v, the Bernstein coefficient of a power is a ratio of falling
-- factorials. Dividing every factor by v gives its limit, including at the endpoints.
private theorem choose_ratio_tendsto {u v : ℕ → ℕ} {x : ℝ} (hv : Tendsto v atTop atTop)
    (hx : Tendsto (fun j => (u j : ℝ) / v j) atTop (𝓝 x)) (r : ℕ) :
    Tendsto (fun j => ((u j).choose r : ℝ) / (v j).choose r) atTop (𝓝 (x ^ r)) := by
  have scaled {w : ℕ → ℕ} {y : ℝ} (hw : Tendsto (fun j => (w j : ℝ) / v j) atTop (𝓝 y)) :
      Tendsto (fun j => ((w j).descFactorial r : ℝ) / (v j : ℝ) ^ r) atTop (𝓝 (y ^ r)) := by
    have ht (i : ℕ) := hw.sub ((tendsto_const_div_atTop_nhds_zero_nat (i : ℝ)).comp hv)
    have hp := tendsto_finsetProd (range r) fun i _ => ht i
    simpa only [Function.comp_def, sub_zero, prod_const, card_range, ← sub_div, prod_div_distrib,
      prod_range_natCast_sub, ← Nat.descFactorial_eq_prod_range] using hp
  have hone : Tendsto (fun j => (v j : ℝ) / v j) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hv.eventually_ge_atTop 1] with j hj
    simp [show v j ≠ 0 by omega]
  have ht := (scaled hx).div (scaled hone) (by simp)
  simp only [one_pow, div_one] at ht
  apply ht.congr'
  filter_upwards [hv.eventually_ge_atTop 1] with j hj
  have hvj : (v j : ℝ) ≠ 0 := by exact_mod_cast (show v j ≠ 0 by omega)
  simp only [Pi.div_apply, div_div_div_cancel_right₀ (pow_ne_zero r hvj),
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast Nat.factorial_ne_zero r)

private theorem exists_bernsteinCoeff_mem (p : Poly d) {s : Set ℝ} (hs : IsOpen s)
    (hp : ∀ x : Box d, MvPolynomial.eval (fun i => (x i : ℝ)) p ∈ s) :
    ∃ N : ℕ, (∀ i, p.degreeOf i ≤ N) ∧ ∀ k : Fin d → Fin (N + 1),
      MvPolynomial.bernsteinCoeff (fun _ => N) p (fun i => k i) ∈ s := by
  classical
  by_contra! h
  let v (j : ℕ) := j + p.totalDegree + 1
  have hv (j : ℕ) : 0 < v j := Nat.zero_lt_succ _
  choose k hk using fun j => h (v j) (fun i =>
    (MvPolynomial.degreeOf_le_totalDegree p i).trans (by dsimp [v]; omega))
  let grid (j : ℕ) : Box d := fun i => ⟨((k j i : ℕ) : ℝ) / v j,
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (by exact_mod_cast hv j)).2 (by exact_mod_cast Nat.le_of_lt_succ (k j i).isLt)⟩
  obtain ⟨x, φ, hφ, hx⟩ := CompactSpace.tendsto_subseq grid
  have htop : Tendsto (v ∘ φ) atTop atTop :=
    (tendsto_atTop_mono (fun j => by dsimp [v]; omega : ∀ j, j ≤ v j) tendsto_id).comp
      hφ.tendsto_atTop
  have hr (i : Fin d) := continuous_subtype_val.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mp hx i)
  have ht : Tendsto (fun j => MvPolynomial.bernsteinCoeff (fun _ => v (φ j)) p
      (fun i => (k (φ j) i : ℕ))) atTop (𝓝 (MvPolynomial.eval (fun i => (x i : ℝ)) p)) := by
    rw [MvPolynomial.eval_eq']
    unfold MvPolynomial.bernsteinCoeff Finsupp.sum
    apply tendsto_finsetSum
    intro s _
    apply Tendsto.const_mul
    exact tendsto_finsetProd _ fun i _ => choose_ratio_tendsto htop (hr i) (s i)
  obtain ⟨j, hj⟩ := (ht.eventually (hs.mem_nhds (hp x))).exists
  exact hk (φ j) hj

private theorem functional_nonneg {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) (p : Poly d)
    (hp : ∀ x : Box d, 0 ≤ MvPolynomial.eval (fun i => (x i : ℝ)) p) :
    0 ≤ functional a p := by
  have strict (q : Poly d) (hq : ∀ x : Box d, 0 < MvPolynomial.eval (fun i => (x i : ℝ)) q) :
      0 ≤ functional a q := by
    obtain ⟨N, hN, hcoeff⟩ := exists_bernsteinCoeff_mem q (s := Set.Ioi 0) isOpen_Ioi hq
    rw [MvPolynomial.eq_sum_bernstein hN, map_sum]
    apply sum_nonneg
    intro k _
    rw [← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul, functional_bernstein a
      (fun i => Nat.le_of_lt_succ (k i).isLt)]
    exact mul_nonneg (hcoeff k).le (mul_nonneg (Nat.cast_nonneg _) (ha _ _
      (fun i => Nat.sub_le _ _)))
  have ht : Tendsto (fun ε : ℝ => functional a p + ε * functional a 1) (𝓝[>] 0)
      (𝓝 (functional a p)) := by
    have hc : Continuous (fun ε : ℝ => functional a p + ε * functional a 1) := by fun_prop
    simpa using hc.continuousWithinAt (s := Set.Ioi 0) (x := 0) |>.tendsto
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simpa using strict (p + ε • 1) (fun x => by
    simpa [MvPolynomial.smul_eq_C_mul] using add_pos_of_nonneg_of_pos (hp x) hε)

private noncomputable def restrictPoly : Poly d →ₗ[ℝ] C(Box d, ℝ) where
  toFun p := ⟨fun x => MvPolynomial.eval (fun i => (x i : ℝ)) p,
    p.continuous_eval.comp (continuous_pi fun i =>
      continuous_subtype_val.comp (continuous_apply i))⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp [MvPolynomial.smul_eq_C_mul]

private theorem restrictPoly_injective : Function.Injective (restrictPoly (d := d)) := by
  intro p q h
  apply MvPolynomial.funext_set (fun _ => Set.Icc 0 1) (fun _ => Set.Icc_infinite zero_lt_one)
  intro x hx
  exact DFunLike.congr_fun h (fun i => ⟨x i, hx i (Set.mem_univ _)⟩ : Box d)

private def nonnegCone : PointedCone ℝ C(Box d, ℝ) :=
  (PointedCone.positive ℝ (Box d → ℝ)).comap (ContinuousMap.coeFnLinearMap ℝ)

-- Extend from restrictions of polynomials to all continuous functions. Constants in the
-- polynomial subspace dominate every continuous function on the compact cube.
private theorem exists_positive_extension {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) :
    ∃ L : C(Box d, ℝ) →ₗ[ℝ] ℝ, (∀ p, L (restrictPoly p) = functional a p) ∧
      ∀ f, 0 ≤ f → 0 ≤ L f := by
  let e := LinearEquiv.ofInjective (restrictPoly (d := d)) restrictPoly_injective
  let F : C(Box d, ℝ) →ₗ.[ℝ] ℝ := ⟨_, (functional a).comp e.symm.toLinearMap⟩
  obtain ⟨L, hagree, hpos⟩ := riesz_extension nonnegCone F
    (by
      intro f hf
      obtain ⟨p, rfl⟩ := e.surjective f
      change 0 ≤ functional a (e.symm (e p))
      rw [e.symm_apply_apply]
      exact functional_nonneg ha p hf)
    (by
      intro f
      refine ⟨e (MvPolynomial.C ‖f‖), ?_⟩
      intro x
      change 0 ≤ MvPolynomial.eval _ (MvPolynomial.C ‖f‖) + f x
      rw [MvPolynomial.eval_C]
      exact neg_le_iff_add_nonneg'.mp (f.neg_norm_le_apply x))
  refine ⟨L, fun p => (hagree (e p)).trans ?_, hpos⟩
  change functional a (e.symm (e p)) = functional a p
  rw [e.symm_apply_apply]

private theorem positive_functional_moments (L : C(Box d, ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ f, 0 ≤ f → 0 ≤ L f) :
    IsPositiveMomentConfiguration
      (fun n => L (restrictPoly (∏ i, MvPolynomial.X i ^ n i))) := by
  let Λ : C_c(Box d, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => L f.toContinuousMap
      map_add' := fun f g => L.map_add f.toContinuousMap g.toContinuousMap
      map_smul' := fun c f => L.map_smul c f.toContinuousMap
      monotone' := by
        intro f g hfg
        exact sub_nonneg.mp (L.map_sub g.toContinuousMap f.toContinuousMap ▸
          hpos (g.toContinuousMap - f.toContinuousMap) (fun x => sub_nonneg.mpr (hfg x))) }
  let μ := RealRMK.rieszMeasure Λ
  refine ⟨μ.map embedBox, inferInstance, fun n => ?_⟩
  let p : Poly d := ∏ i, MvPolynomial.X i ^ n i
  let f := CompactlySupportedContinuousMap.continuousMapEquiv (restrictPoly p)
  rw [momentOf, setIntegral_map isCompact_cube.measurableSet
    (continuous_monomial n).aestronglyMeasurable continuous_embedBox.aemeasurable,
    show embedBox ⁻¹' cube d = Set.univ from Set.eq_univ_of_forall fun x i => (x i).property,
    setIntegral_univ]
  calc
    L (restrictPoly p) = Λ f := rfl
    _ = ∫ x, f x ∂μ := (RealRMK.integral_rieszMeasure Λ f).symm
    _ = _ := by
      apply integral_congr_ae
      refine .of_forall fun x => ?_
      change MvPolynomial.eval _ (∏ i, MvPolynomial.X i ^ n i) = _
      simp [monomial, embedBox]

private theorem positive_moments {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) : IsPositiveMomentConfiguration a := by
  obtain ⟨L, hagree, hpos⟩ := exists_positive_extension ha
  obtain ⟨μ, hμ, h⟩ := positive_functional_moments L hpos
  exact ⟨μ, hμ, fun n => (functional_monomial a n).symm.trans ((hagree _).symm.trans (h n))⟩

set_option linter.dupNamespace false in
/-- **Hausdorff positivity criterion.** A real sequence $a$ indexed by $\mathbb{N}^d$ is a positive
moment configuration, that is, there is a finite measure $\mu$ on $\mathbb{R}^d$ with
$a_n = \int_{[0,1]^d} x^n \, d\mu(x)$ for every multi-index $n \in \mathbb{N}^d$, where
$x^n = \prod_i x_i^{n_i}$, if and only if $(\Delta^k a)_n \ge 0$ for all multi-indices $k, n$ with
$k \le n$ coordinatewise, where $\Delta^k a$ is the iterated backward difference of $a$.

Source: F. Hausdorff, *Summationsmethoden und Momentfolgen I, II*, Math. Z. 9 (1921). Knill, *Some
fundamental theorems in mathematics*, §115. Via leanprover/lean-eval@38361be, problem
`hausdorff_positivity_criterion`. -/
public theorem hausdorff_positivity {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    IsPositiveMomentConfiguration a ↔ ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n := by
  constructor
  · rintro ⟨μ, hμ, h⟩ k n hkn
    rw [show a = momentOf μ from funext h]
    exact diff_moment_nonneg hkn
  · exact positive_moments

-- The backward-difference index is the complement of the Bernstein index in the degree box.
private theorem sum_abs_bernstein_weights (a : (Fin d → ℕ) → ℝ) (n : Fin d → ℕ) :
    ∑ k : (i : Fin d) → Fin (n i + 1), |functional a (MvPolynomial.bernstein n (fun i => k i))| =
      ∑ k ∈ Iic n, |(multiChoose n k : ℝ) * diff a k n| := by
  classical
  let e : ((i : Fin d) → Fin (n i + 1)) ≃ ↥(Iic n) :=
    { toFun := fun k => ⟨n - fun i => (k i : ℕ), mem_Iic.mpr fun i => Nat.sub_le _ _⟩
      invFun := fun k i => ⟨n i - k.1 i, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
      left_inv := fun k => funext fun i => Fin.ext (Nat.sub_sub_self (Nat.le_of_lt_succ (k i).isLt))
      right_inv := fun k => Subtype.ext (funext fun i => Nat.sub_sub_self (mem_Iic.mp k.2 i)) }
  rw [← sum_attach (Iic n)]
  refine Fintype.sum_equiv e _ (fun k => |(multiChoose n k : ℝ) * diff a k n|) fun k => ?_
  have hk : (fun i => (k i : ℕ)) ≤ n := fun i => Nat.le_of_lt_succ (k i).isLt
  rw [functional_bernstein a hk]
  have hchoose : multiChoose n (e k) = multiChoose n (fun i => (k i : ℕ)) :=
    prod_congr rfl fun i _ => Nat.choose_symm (hk i)
  rw [hchoose]
  rfl

private theorem hausdorffBounded_of_moments {a : (Fin d → ℕ) → ℝ}
    (ha : IsMomentConfiguration a) : HausdorffBounded a := by
  classical
  obtain ⟨μ, ν, hμ, hν, ha⟩ := ha
  refine ⟨functional (momentOf μ) 1 + functional (momentOf ν) 1, fun n => ?_⟩
  rw [← sum_abs_bernstein_weights]
  have hsum : ∑ k : (i : Fin d) → Fin (n i + 1), MvPolynomial.bernstein n (fun i => k i) = 1 := by
    have h := (MvPolynomial.eq_sum_bernstein (p := MvPolynomial.C (1 : ℝ))
      (n := n) (fun i => by simp)).symm
    simp only [MvPolynomial.bernsteinCoeff_C] at h
    simpa only [map_one, one_mul] using h
  calc
    _ ≤ ∑ k : (i : Fin d) → Fin (n i + 1),
        (functional (momentOf μ) (MvPolynomial.bernstein n (fun i => k i)) +
          functional (momentOf ν) (MvPolynomial.bernstein n (fun i => k i))) := by
      apply sum_le_sum
      intro k _
      have hk : (fun i => (k i : ℕ)) ≤ n := fun i => Nat.le_of_lt_succ (k i).isLt
      simp only [functional_bernstein _ hk]
      have hkn : n - (fun i => (k i : ℕ)) ≤ n := fun i => Nat.sub_le _ _
      have hdiff : a = fun m => momentOf μ m - momentOf ν m := funext ha
      have hμk : 0 ≤ (multiChoose n (fun i => (k i : ℕ)) : ℝ) * diff (momentOf μ) _ n :=
        mul_nonneg (Nat.cast_nonneg _) (diff_moment_nonneg hkn)
      have hνk : 0 ≤ (multiChoose n (fun i => (k i : ℕ)) : ℝ) * diff (momentOf ν) _ n :=
        mul_nonneg (Nat.cast_nonneg _) (diff_moment_nonneg hkn)
      rw [hdiff, diff_sub, mul_sub, abs_le]
      exact ⟨by linarith, by linarith⟩
    _ = _ := by rw [sum_add_distrib, ← map_sum, ← map_sum, hsum]

private theorem abs_functional_le {a : (Fin d → ℕ) → ℝ} {C : ℝ}
    (hC : ∀ n : Fin d → ℕ, ∑ k ∈ Iic n, |(multiChoose n k : ℝ) * diff a k n| ≤ C)
    (p : Poly d) : |functional a p| ≤ C * ‖restrictPoly p‖ := by
  have hbound (ε : ℝ) (hε : 0 < ε) : |functional a p| ≤ (‖restrictPoly p‖ + ε) * C := by
    obtain ⟨N, hN, hcoeff⟩ := exists_bernsteinCoeff_mem p
      (s := {x | |x| < ‖restrictPoly p‖ + ε}) (isOpen_lt continuous_abs continuous_const)
      (fun x => by
        change |restrictPoly p x| < ‖restrictPoly p‖ + ε
        simpa only [Real.norm_eq_abs] using
          ((restrictPoly p).norm_coe_le_norm x).trans_lt (lt_add_of_pos_right _ hε))
    let n : Fin d → ℕ := fun _ => N
    let w (k : (i : Fin d) → Fin (n i + 1)) :=
      functional a (MvPolynomial.bernstein n (fun i => k i))
    let b (k : (i : Fin d) → Fin (n i + 1)) := MvPolynomial.bernsteinCoeff n p (fun i => k i)
    have he : functional a p = ∑ k, b k * w k := by
      conv_lhs => rw [MvPolynomial.eq_sum_bernstein hN]
      simp only [← MvPolynomial.smul_eq_C_mul, map_sum, map_smul, smul_eq_mul, b, w, n]
    calc
      |functional a p| = |∑ k, b k * w k| := congrArg abs he
      _ ≤ ∑ k, |b k * w k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, (‖restrictPoly p‖ + ε) * |w k| := by
        apply sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hcoeff k).le (abs_nonneg _)
      _ ≤ (‖restrictPoly p‖ + ε) * C := by
        rw [← mul_sum, sum_abs_bernstein_weights a n]
        exact mul_le_mul_of_nonneg_left (hC n) (by positivity)
  have hc : Continuous (fun ε : ℝ => (‖restrictPoly p‖ + ε) * C) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => (‖restrictPoly p‖ + ε) * C) (𝓝[>] 0)
      (𝓝 (C * ‖restrictPoly p‖)) := by
    simpa [mul_comm] using hc.continuousWithinAt (s := Set.Ioi 0) (x := 0) |>.tendsto
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε using hbound ε hε

-- On pairs `(t + p, t - p)`, positivity means `‖p‖ ≤ t`. Extend the functional
-- `C * t + functional a p` to the whole product and take its restrictions to the two axes.
private theorem exists_positive_pair {a : (Fin d → ℕ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ p : Poly d, |functional a p| ≤ C * ‖restrictPoly p‖) :
    ∃ L₁ L₂ : C(Box d, ℝ) →ₗ[ℝ] ℝ, (∀ f, 0 ≤ f → 0 ≤ L₁ f) ∧
      (∀ f, 0 ≤ f → 0 ≤ L₂ f) ∧
      ∀ p, L₁ (restrictPoly p) - L₂ (restrictPoly p) = functional a p := by
  let c := (LinearMap.fst ℝ ℝ (Poly d)).smulRight (1 : C(Box d, ℝ))
  let r := (restrictPoly (d := d)).comp (LinearMap.snd ℝ ℝ (Poly d))
  let J := (c + r).prod (c - r)
  have hJ (t : ℝ) (p : Poly d) (x : Box d) :
      (J (t, p)).1 x = t + restrictPoly p x ∧ (J (t, p)).2 x = t - restrictPoly p x := by
    simp [J, c, r]
  let z : Box d := fun _ => ⟨0, by simp⟩
  have hinj : Function.Injective J := by
    rintro ⟨t, p⟩ ⟨u, q⟩ h
    have h₁ (x : Box d) : t + restrictPoly p x = u + restrictPoly q x :=
      (hJ t p x).1.symm.trans ((congrArg (fun f => f.1 x) h).trans (hJ u q x).1)
    have h₂ (x : Box d) : t - restrictPoly p x = u - restrictPoly q x :=
      (hJ t p x).2.symm.trans ((congrArg (fun f => f.2 x) h).trans (hJ u q x).2)
    exact Prod.ext (by linarith [h₁ z, h₂ z])
      (restrictPoly_injective (ContinuousMap.ext fun x => by linarith [h₁ x, h₂ x]))
  let e := LinearEquiv.ofInjective J hinj
  let g := C • LinearMap.fst ℝ ℝ (Poly d) + (functional a).comp (LinearMap.snd ℝ ℝ (Poly d))
  let F : C(Box d, ℝ) × C(Box d, ℝ) →ₗ.[ℝ] ℝ := ⟨_, g.comp e.symm.toLinearMap⟩
  obtain ⟨L, hagree, hpos⟩ := riesz_extension ((nonnegCone (d := d)).prod nonnegCone) F (by
    intro f hf
    obtain ⟨⟨t, p⟩, rfl⟩ := e.surjective f
    change 0 ≤ J (t, p) at hf
    have hbound (x : Box d) : |restrictPoly p x| ≤ t := by
      have h₁ : 0 ≤ (J (t, p)).1 x := hf.1 x
      have h₂ : 0 ≤ (J (t, p)).2 x := hf.2 x
      rw [(hJ t p x).1] at h₁
      rw [(hJ t p x).2] at h₂
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have ht : ‖restrictPoly p‖ ≤ t :=
      ((restrictPoly p).norm_le ((abs_nonneg _).trans (hbound z))).2 fun x => by
        simpa only [Real.norm_eq_abs] using hbound x
    change 0 ≤ g (e.symm (e (t, p)))
    rw [e.symm_apply_apply]
    change 0 ≤ C * t + functional a p
    exact neg_le_iff_add_nonneg.mp
      ((neg_le_abs (functional a p)).trans ((ha p).trans (mul_le_mul_of_nonneg_left ht hC)))) (by
    intro f
    let t := max ‖f.1‖ ‖f.2‖
    refine ⟨e (t, 0), ?_⟩
    change 0 ≤ J (t, 0) + f
    constructor
    · intro x
      change 0 ≤ (J (t, 0)).1 x + f.1 x
      rw [(hJ t 0 x).1, map_zero, ContinuousMap.zero_apply, add_zero]
      exact neg_le_iff_add_nonneg'.mp
        ((neg_le_neg (le_max_left _ _)).trans (f.1.neg_norm_le_apply x))
    · intro x
      change 0 ≤ (J (t, 0)).2 x + f.2 x
      rw [(hJ t 0 x).2, map_zero, ContinuousMap.zero_apply, sub_zero]
      exact neg_le_iff_add_nonneg'.mp
        ((neg_le_neg (le_max_right _ _)).trans (f.2.neg_norm_le_apply x)))
  let L₁ := L.comp (LinearMap.inl ℝ C(Box d, ℝ) C(Box d, ℝ))
  let L₂ := L.comp (LinearMap.inr ℝ C(Box d, ℝ) C(Box d, ℝ))
  refine ⟨L₁, L₂, fun f hf => hpos (f, 0) ⟨hf, zero_mem nonnegCone⟩,
    fun f hf => hpos (0, f) ⟨zero_mem nonnegCone, hf⟩, fun p => ?_⟩
  have hp := hagree (e (0, p))
  change L (J (0, p)) = g (e.symm (e (0, p))) at hp
  rw [e.symm_apply_apply, show J (0, p) = (restrictPoly p, 0) - (0, restrictPoly p) by
    ext x <;> simp [(hJ 0 p x).1, (hJ 0 p x).2], map_sub] at hp
  simpa [L₁, L₂, g] using hp

set_option linter.dupNamespace false in
/-- **Hausdorff–Hildebrandt–Schoenberg moment theorem.** A real sequence $a$ indexed by
$\mathbb{N}^d$ is a moment configuration, that is, there are finite measures $\mu$ and $\nu$ on
$\mathbb{R}^d$ with $a_n = \int_{[0,1]^d} x^n \, d\mu(x) - \int_{[0,1]^d} x^n \, d\nu(x)$ for every
multi-index $n \in \mathbb{N}^d$, where $x^n = \prod_i x_i^{n_i}$, if and only if $a$ is Hausdorff
bounded.

Source: F. Hausdorff (1921, 1923); T. H. Hildebrandt and I. J. Schoenberg, *On Linear Functional
Operations and the Moment Problem for a Finite Interval in One or Several Dimensions*, Ann. of Math.
34 (1933), 317–328. The backward-difference formulation is in Oliver Knill,
*Some Fundamental Theorems in Mathematics*, §115. Via leanprover/lean-eval@38361be,
problem `hausdorff_hildebrandt_schoenberg`. -/
public theorem hausdorff_hildebrandt_schoenberg {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    IsMomentConfiguration a ↔ HausdorffBounded a := by
  refine ⟨hausdorffBounded_of_moments, ?_⟩
  rintro ⟨C, hC⟩
  have hC₀ : 0 ≤ C := (sum_nonneg fun _ _ => abs_nonneg _).trans (hC 0)
  obtain ⟨L₁, L₂, h₁, h₂, h⟩ := exists_positive_pair hC₀ (abs_functional_le hC)
  obtain ⟨μ, hμ, hμn⟩ := positive_functional_moments L₁ h₁
  obtain ⟨ν, hν, hνn⟩ := positive_functional_moments L₂ h₂
  refine ⟨μ, ν, hμ, hν, fun n => ?_⟩
  simpa only [functional_monomial, hμn n, hνn n] using
    (h (∏ i, MvPolynomial.X i ^ n i)).symm

end MathlibExt.Analysis.HausdorffMomentsWanted.Analysis
