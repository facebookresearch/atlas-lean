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
The adapted portions are the moment and difference definitions and the criterion's statement.
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
# Hausdorff positivity on the unit cube

`hausdorff_positivity` characterizes the moments of finite positive measures on the cube by
nonnegativity of all iterated backward differences. The converse uses the tensor-product
Bernstein basis to construct a positive polynomial functional, then represents it by a measure.

Hausdorff (1921) proved the criterion on the unit interval, and Hildebrandt and Schoenberg (1933)
treated the moment problem on the cube in several dimensions.
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

private theorem exists_positive_coeff (p : Poly d)
    (hp : ∀ x : Box d, 0 < MvPolynomial.eval (fun i => (x i : ℝ)) p) :
    ∃ N : ℕ, (∀ i, p.degreeOf i ≤ N) ∧ ∀ k : Fin d → Fin (N + 1),
      0 < MvPolynomial.bernsteinCoeff (fun _ => N) p (fun i => k i) := by
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
  exact (hp x).not_ge (le_of_tendsto ht (.of_forall fun j => hk (φ j)))

private theorem functional_nonneg {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) (p : Poly d)
    (hp : ∀ x : Box d, 0 ≤ MvPolynomial.eval (fun i => (x i : ℝ)) p) :
    0 ≤ functional a p := by
  have strict (q : Poly d) (hq : ∀ x : Box d, 0 < MvPolynomial.eval (fun i => (x i : ℝ)) q) :
      0 ≤ functional a q := by
    obtain ⟨N, hN, hcoeff⟩ := exists_positive_coeff q hq
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

-- Extend from restrictions of polynomials to all continuous functions. Constants in the
-- polynomial subspace dominate every continuous function on the compact cube.
private theorem exists_positive_extension {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) :
    ∃ L : C(Box d, ℝ) →ₗ[ℝ] ℝ, (∀ p, L (restrictPoly p) = functional a p) ∧
      ∀ f, 0 ≤ f → 0 ≤ L f := by
  let e := LinearEquiv.ofInjective (restrictPoly (d := d)) restrictPoly_injective
  let F : C(Box d, ℝ) →ₗ.[ℝ] ℝ := ⟨_, (functional a).comp e.symm.toLinearMap⟩
  let s : PointedCone ℝ C(Box d, ℝ) :=
    { carrier := {f | 0 ≤ f}
      zero_mem' := fun _ => le_rfl
      add_mem' hf hg x := add_nonneg (hf x) (hg x)
      smul_mem' c f hf x := mul_nonneg c.property (hf x) }
  obtain ⟨L, hagree, hpos⟩ := riesz_extension s F
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

private theorem positive_moments {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) : IsPositiveMomentConfiguration a := by
  obtain ⟨L, hagree, hpos⟩ := exists_positive_extension ha
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
    a n = functional a p := (functional_monomial a n).symm
    _ = Λ f := (hagree p).symm
    _ = ∫ x, f x ∂μ := (RealRMK.integral_rieszMeasure Λ f).symm
    _ = _ := by
      apply integral_congr_ae
      refine .of_forall fun x => ?_
      change MvPolynomial.eval _ (∏ i, MvPolynomial.X i ^ n i) = _
      simp [monomial, embedBox]

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

end MathlibExt.Analysis.HausdorffMomentsWanted.Analysis
