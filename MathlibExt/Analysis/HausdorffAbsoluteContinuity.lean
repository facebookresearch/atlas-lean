/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/HausdorffAbsoluteContinuity.lean` (leanprover/lean-eval):
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
The adapted portions are the definitions, theorem statement and their accompanying docstrings.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.HausdorffAbsoluteContinuity` —
hausdorff_absolute_continuity (manifest `manifests/problems/hausdorff_absolute_continuity.toml`, rev
1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted`
namespace. ATLAS later proved the criterion and moved these declarations from
`WantedExt/Analysis/HausdorffAbsoluteContinuityWanted.lean` and clarified the source of the
multidimensional criterion in the module documentation.
-/
module

public import Mathlib.Data.Pi.Interval
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Regular
import MathlibExt.RingTheory.MvPolynomial.BernsteinBounds

/-!
# Hausdorff moment problem: absolute-continuity criterion

A probability measure on the unit cube is dominated by a constant multiple of Lebesgue
measure if and only if its moment differences satisfy the corresponding bound
(`hausdorff_absolute_continuity`). This specializes the comparison of two probability
measures in O. Knill, *Some fundamental theorems in mathematics*, arXiv:1807.08416v4,
§115 “Moments”, p. 52 (the paragraph following the Hausdorff–Hildebrandt–Schoenberg theorem).
Taking the second measure to be Lebesgue measure on the cube expresses bounded density
as $\mu \le M\lambda$ for some $M \ge 0$.

For the interval moment problem, see F. Hausdorff, *Summationsmethoden und Momentfolgen I, II*
(1921) and *Momentprobleme für ein endliches Intervall* (1923), and Shohat–Tamarkin,
*The Problem of Moments*.
-/

@[expose] public section

namespace MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted
namespace Analysis.HausdorffAbsoluteContinuity

open MeasureTheory
open scoped BigOperators NNReal

set_option linter.dupNamespace false in
/-- **Closed unit cube.** For $d \in \mathbb{N}$, the closed unit cube $I^d = [0,1]^d$ is the
set of points $x \in \mathbb{R}^d$ with $0 \le x_i \le 1$ for every coordinate $i$. -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

set_option linter.dupNamespace false in
/-- **Multivariate monomial.** For a multi-index $n = (n_1, \dots, n_d) \in \mathbb{N}^d$ and a
point $x \in \mathbb{R}^d$, the monomial $x^n$ is the real number $\prod_{i=1}^{d} x_i^{n_i}$. -/
def monomial {d : ℕ} (n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, (x i) ^ (n i)

set_option linter.dupNamespace false in
/-- **Moments of a measure on the unit cube.** For a measure $\mu$ on $\mathbb{R}^d$ and a
multi-index $n \in \mathbb{N}^d$, the $n$-th moment of $\mu$ is the real number
$\int_{I^d} x^n \, d\mu(x)$, the integral over the closed unit cube $I^d = [0,1]^d$ of the
monomial $x^n = \prod_{i=1}^{d} x_i^{n_i}$, taken to be $0$ when the monomial is not
$\mu$-integrable on $I^d$. -/
noncomputable def momentOf {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (n : Fin d → ℕ) : ℝ :=
  ∫ x in cube d, monomial n x ∂μ

set_option linter.dupNamespace false in
/-- **Multi-index binomial coefficient.** For multi-indices $n, k \in \mathbb{N}^d$, the
binomial coefficient $\binom{n}{k}$ is the natural number $\prod_{i=1}^{d} \binom{n_i}{k_i}$. -/
def multiChoose {d : ℕ} (n k : Fin d → ℕ) : ℕ := ∏ i, (n i).choose (k i)

set_option linter.dupNamespace false in
/-- **Iterated backward difference of a multi-sequence.** For a function
$a : \mathbb{N}^d \to \mathbb{R}$ and multi-indices $k, n \in \mathbb{N}^d$,
$$(\Delta^k a)_n = \sum_{j \le k} (-1)^{|k| - |j|} \binom{k}{j} \, a_{n - j},$$
where $j$ runs over the multi-indices with $j_i \le k_i$ for every $i$, $|k| = \sum_i k_i$,
$\binom{k}{j} = \prod_i \binom{k_i}{j_i}$ is the multi-index binomial coefficient, and $n - j$
is taken coordinatewise, with $n_i - j_i$ replaced by $0$ when $j_i > n_i$.

When $k \le n$ coordinatewise, $\Delta^k$ is the composite of $k_i$ applications of
$(\Delta_i a)_n = a_{n - e_i} - a_n$ in each coordinate $i$, where $e_i$ is the $i$-th unit
multi-index. -/
noncomputable def diff {d : ℕ} (a : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) : ℝ :=
  ∑ j ∈ Finset.Iic k,
    (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * a (n - j)

set_option linter.dupNamespace false in
/-- **Uniformly absolutely continuous measures.** A measure $\mu$ on $\mathbb{R}^d$ is uniformly
absolutely continuous with respect to a measure $\nu$ on $\mathbb{R}^d$ if there is a real
constant $C \ge 0$ with $\mu(S) \le C \, \nu(S)$ for every measurable set $S$.

When $\nu$ is $\sigma$-finite, this says that $\mu$ has an essentially bounded Radon–Nikodym
density with respect to $\nu$. -/
def UniformlyAbsolutelyContinuous {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ C : ℝ≥0, μ ≤ C • ν

open Filter Finset
open scoped Topology unitInterval

private theorem isCompact_cube (d : ℕ) : IsCompact (cube d) := by
  have h := (isCompact_pi_infinite (X := fun _ : Fin d => ℝ)
    (s := fun _ => Set.Icc 0 1) fun _ => isCompact_Icc).image
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  convert h using 1
  ext x
  constructor
  · exact fun hx => ⟨x.ofLp, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

private noncomputable def momentKernel {d : ℕ} (k n : Fin d → ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, (x i) ^ (n i - k i) * (1 - x i) ^ k i

private theorem continuous_momentKernel {d : ℕ} (k n : Fin d → ℕ) :
    Continuous (momentKernel k n) :=
  continuous_finsetProd _ fun i _ => ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).pow _).mul
    ((continuous_const.sub (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)).pow _)

private theorem momentKernel_nonneg {d : ℕ} (k n : Fin d → ℕ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cube d) : 0 ≤ momentKernel k n x :=
  prod_nonneg fun i _ =>
    mul_nonneg (pow_nonneg (hx i).1 _) (pow_nonneg (sub_nonneg.mpr (hx i).2) _)

-- Expanding each factor produces the backward differences with the stated signs.
private theorem momentKernel_one_coord (x : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    x ^ (n - k) * (1 - x) ^ k =
      ∑ j ∈ Iic k, (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * x ^ (n - j) := by
  rw [sub_eq_add_neg, add_pow, mul_sum, Nat.range_succ_eq_Iic]
  apply sum_congr rfl
  intro j hj
  have hjk := mem_Iic.mp hj
  have hsub : (n - k) + (k - j) = n - j := by omega
  rw [one_pow, one_mul, neg_eq_neg_one_mul, mul_pow, ← hsub, pow_add]
  ring

private theorem momentKernel_eq_sum {d : ℕ} (x : EuclideanSpace ℝ (Fin d))
    {k n : Fin d → ℕ} (hkn : k ≤ n) :
    momentKernel k n x =
      ∑ j ∈ Iic k, (-1 : ℝ) ^ (∑ i, (k i - j i)) *
        (multiChoose k j : ℝ) * monomial (n - j) x := by
  classical
  unfold momentKernel
  simp_rw [momentKernel_one_coord _ (hkn _), prod_univ_sum]
  have hIic : Fintype.piFinset (fun i => Iic (k i)) = Iic k := by
    ext j
    simp [Pi.le_def]
  rw [hIic]
  apply sum_congr rfl
  intro j _
  simp only [monomial, multiChoose, Nat.cast_prod, ← prod_pow_eq_pow_sum,
    ← prod_mul_distrib, Pi.sub_apply]

private theorem diff_eq_integral {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasureOnCompacts μ] {k n : Fin d → ℕ} (hkn : k ≤ n) :
    diff (momentOf μ) k n = ∫ x in cube d, momentKernel k n x ∂μ := by
  classical
  simp only [diff, momentOf]
  have hcont (j : Fin d → ℕ) : Continuous (monomial (n - j)) :=
    continuous_finsetProd _ fun i _ => (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).pow _
  rw [show (momentKernel k n) =
    (fun x => ∑ j ∈ Iic k, (-1 : ℝ) ^ (∑ i, (k i - j i)) *
      (multiChoose k j : ℝ) * monomial (n - j) x) from
    funext fun x => momentKernel_eq_sum x hkn]
  rw [integral_finsetSum]
  · simp only [← integral_const_mul]
  · intro j _
    exact (hcont j).continuousOn.integrableOn_compact (isCompact_cube d) |>.const_mul _

private noncomputable def bernsteinWeight {d m : ℕ} (j : Fin d → Fin (m + 1))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  MvPolynomial.eval x.ofLp (MvPolynomial.bernstein (fun _ => m) fun i => (j i).val)

private theorem bernsteinWeight_eq_prod {d m : ℕ} (j : Fin d → Fin (m + 1))
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cube d) :
    bernsteinWeight j x = ∏ i, bernstein m (j i) ⟨x i, hx i⟩ := by
  simp [bernsteinWeight, MvPolynomial.eval_bernstein, bernstein_apply, bernsteinPolynomial]

private theorem bernsteinWeight_eq_kernel {d m : ℕ} (j : Fin d → Fin (m + 1))
    (x : EuclideanSpace ℝ (Fin d)) :
    bernsteinWeight j x =
      (multiChoose (fun _ => m) (fun i => (j i).val) : ℝ) *
        momentKernel (fun i => m - (j i).val) (fun _ => m) x := by
  simp only [bernsteinWeight, MvPolynomial.eval_bernstein, bernsteinPolynomial,
    Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, multiChoose, Nat.cast_prod, momentKernel,
    ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [Nat.sub_sub_self (j i).is_le, mul_assoc]

private theorem continuous_bernsteinWeight {d m : ℕ} (j : Fin d → Fin (m + 1)) :
    Continuous (bernsteinWeight j) := by
  convert continuous_const.mul (continuous_momentKernel (fun i => m - (j i).val) (fun _ => m))
    using 1
  exact funext (bernsteinWeight_eq_kernel j)

private theorem bernsteinWeight_nonneg {d m : ℕ} (j : Fin d → Fin (m + 1))
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cube d) : 0 ≤ bernsteinWeight j x :=
  MvPolynomial.eval_bernstein_nonneg _ _ hx

private theorem sum_bernsteinWeight {d m : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    ∑ j : Fin d → Fin (m + 1), bernsteinWeight j x = 1 :=
  MvPolynomial.sum_eval_bernstein (fun _ => m) x.ofLp

private noncomputable def gridPoint {d m : ℕ} (j : Fin d → Fin (m + 1)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => (bernstein.z (j i) : ℝ)

-- For a function of one coordinate, all the other coordinates sum out to one.
private theorem sum_mul_bernsteinWeight_coord {d m : ℕ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ cube d) (i : Fin d) (g : Fin (m + 1) → ℝ) :
    ∑ j : Fin d → Fin (m + 1), g (j i) * bernsteinWeight j x =
      ∑ a : Fin (m + 1), g a * bernstein m a ⟨x i, hx i⟩ := by
  classical
  let w (l : Fin d) (a : Fin (m + 1)) := bernstein m a ⟨x l, hx l⟩
  let v := Function.update w i (fun a => g a * w i a)
  have hv (j : Fin d → Fin (m + 1)) :
      g (j i) * bernsteinWeight j x = ∏ l, v l (j l) := by
    have he : (fun l => v l (j l)) =
        Function.update (fun l => w l (j l)) i (g (j i) * w i (j i)) := by
      ext l
      by_cases h : l = i
      · subst l
        simp [v]
      · simp [v, Function.update_of_ne h]
    rw [he, prod_update_of_mem (mem_univ i), bernsteinWeight_eq_prod j hx]
    change g (j i) * (∏ l, w l (j l)) = _
    rw [prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ i) (fun l => w l (j l)), mul_assoc]
  simp_rw [hv]
  rw [← Fintype.prod_sum,
    prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ i) (fun l => ∑ a, v l a)]
  have hv' : ∏ l ∈ univ \ {i}, ∑ a : Fin (m + 1), v l a = 1 := by
    apply prod_eq_one
    intro l hl
    have hli : l ≠ i := by simpa using hl
    simp [v, Function.update_of_ne hli, w]
  simp [hv', v, w]

private theorem sum_dist_sq_mul_bernsteinWeight {d m : ℕ} (hm : m ≠ 0)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cube d) :
    ∑ j : Fin d → Fin (m + 1), dist x (gridPoint j) ^ 2 * bernsteinWeight j x =
      (∑ i, x i * (1 - x i)) / (m : ℝ) := by
  simp only [EuclideanSpace.dist_sq_eq, Real.dist_eq, sq_abs, sum_mul]
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro i _
  change (∑ j : Fin d → Fin (m + 1),
    (x i - (bernstein.z (j i) : ℝ)) ^ 2 * bernsteinWeight j x) = _
  rw [sum_mul_bernsteinWeight_coord hx i (fun a => (x i - (bernstein.z a : ℝ)) ^ 2)]
  exact bernstein.variance hm ⟨x i, hx i⟩

private noncomputable def bernsteinApprox {d : ℕ} (m : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ j : Fin d → Fin (m + 1), f (gridPoint j) * bernsteinWeight j x

private theorem continuous_bernsteinApprox {d : ℕ} (m : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Continuous (bernsteinApprox m f) :=
  continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_bernsteinWeight j)

private theorem bernsteinApprox_mem_Icc {d m : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ∀ x, f x ∈ Set.Icc 0 1) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cube d) :
    bernsteinApprox m f x ∈ Set.Icc 0 1 := by
  unfold bernsteinApprox
  refine ⟨sum_nonneg fun j _ => mul_nonneg (hf _).1 (bernsteinWeight_nonneg j hx), ?_⟩
  calc
    _ ≤ ∑ j : Fin d → Fin (m + 1), bernsteinWeight j x :=
      sum_le_sum fun j _ => mul_le_of_le_one_left (bernsteinWeight_nonneg j hx) (hf _).2
    _ = 1 := sum_bernsteinWeight x

-- The weighted squared distance tends to zero by the univariate variance formula.
private theorem tendsto_bernsteinApprox {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Continuous f) (hfIcc : ∀ x, f x ∈ Set.Icc 0 1)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cube d) :
    Tendsto (fun m : ℕ => bernsteinApprox (m + 1) f x) atTop (𝓝 (f x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hf.continuousAt (ε / 2) (by positivity)
  have hpoint (y : EuclideanSpace ℝ (Fin d)) :
      |f y - f x| ≤ ε / 2 + dist x y ^ 2 / δ ^ 2 := by
    by_cases hy : dist y x < δ
    · have h := hnear hy
      rw [Real.dist_eq] at h
      exact h.le.trans (le_add_of_nonneg_right (by positivity))
    · have hsq : δ ^ 2 ≤ dist x y ^ 2 := by
        rw [dist_comm]
        exact pow_le_pow_left₀ hδ.le (le_of_not_gt hy) _
      have hfar : 1 ≤ dist x y ^ 2 / δ ^ 2 := (le_div_iff₀ (by positivity)).mpr (by simpa)
      have habs : |f y - f x| ≤ 1 := abs_le.mpr ⟨by linarith [(hfIcc x).2, (hfIcc y).1],
        by linarith [(hfIcc x).1, (hfIcc y).2]⟩
      linarith
  have herror (m : ℕ) (hm : m ≠ 0) :
      |bernsteinApprox m f x - f x| ≤ ε / 2 + ((∑ i, x i * (1 - x i)) / m) / δ ^ 2 := by
    have heq : bernsteinApprox m f x - f x =
        ∑ j : Fin d → Fin (m + 1), (f (gridPoint j) - f x) * bernsteinWeight j x := by
      simp only [sub_mul, sum_sub_distrib, ← mul_sum, sum_bernsteinWeight, mul_one,
        bernsteinApprox]
    rw [heq]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ j : Fin d → Fin (m + 1),
          (ε / 2 + dist x (gridPoint j) ^ 2 / δ ^ 2) * bernsteinWeight j x := by
        apply sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (bernsteinWeight_nonneg j hx)]
        exact mul_le_mul_of_nonneg_right (hpoint _) (bernsteinWeight_nonneg j hx)
      _ = _ := by
        simp only [add_mul, sum_add_distrib, ← mul_sum, sum_bernsteinWeight, mul_one,
          div_mul_eq_mul_div, ← sum_div, sum_dist_sq_mul_bernsteinWeight hm hx]
  have hzero : Tendsto
      (fun m : ℕ => ((∑ i, x i * (1 - x i)) / ((m : ℝ) + 1)) / δ ^ 2) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [mul_one_div, mul_zero, zero_div] using
      ((tendsto_const_nhds.mul h).div_const (δ ^ 2) :
        Tendsto (fun m : ℕ => (∑ i, x i * (1 - x i)) * (1 / ((m : ℝ) + 1)) / δ ^ 2)
          atTop (𝓝 (((∑ i, x i * (1 - x i)) * 0) / δ ^ 2)))
  filter_upwards [(tendsto_order.mp hzero).2 (ε / 2) (by positivity)] with m hm
  rw [Real.dist_eq]
  have h := herror (m + 1) (Nat.succ_ne_zero m)
  push_cast at h
  linarith

private theorem tendsto_integral_bernsteinApprox {d : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ cube d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) (hfIcc : ∀ x, f x ∈ Set.Icc 0 1) :
    Tendsto (fun m : ℕ => ∫ x, bernsteinApprox (m + 1) f x ∂μ) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => 1)
    (fun m => (continuous_bernsteinApprox (m + 1) f).aestronglyMeasurable)
    (integrable_const _) (fun m => ?_) ?_
  · filter_upwards [hμ] with x hx
    have h := bernsteinApprox_mem_Icc (m := m + 1) hfIcc hx
    rw [Real.norm_of_nonneg h.1]
    exact h.2
  · exact hμ.mono fun x hx => tendsto_bernsteinApprox hf hfIcc hx

private theorem integral_bernsteinWeight {d m : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ cube d)
    (j : Fin d → Fin (m + 1)) :
    ∫ x, bernsteinWeight j x ∂μ =
      (multiChoose (fun _ => m) (fun i => (j i).val) : ℝ) *
        diff (momentOf μ) (fun i => m - (j i).val) (fun _ => m) := by
  simp_rw [bernsteinWeight_eq_kernel, integral_const_mul]
  rw [diff_eq_integral μ (fun i => Nat.sub_le _ _), Measure.restrict_eq_self_of_ae_mem hμ]

private theorem integral_bernsteinApprox_le {d : ℕ}
    {μ ν : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ cube d) (hν : ∀ᵐ x ∂ν, x ∈ cube d)
    (hmom : ∀ k n : Fin d → ℕ, k ≤ n → diff (momentOf μ) k n ≤ diff (momentOf ν) k n)
    (m : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : 0 ≤ f) :
    ∫ x, bernsteinApprox m f x ∂μ ≤ ∫ x, bernsteinApprox m f x ∂ν := by
  have hint (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ]
      (hρ : ∀ᵐ x ∂ρ, x ∈ cube d) (j : Fin d → Fin (m + 1)) :
      Integrable (fun x => f (gridPoint j) * bernsteinWeight j x) ρ := by
    rw [← Measure.restrict_eq_self_of_ae_mem hρ]
    exact ((continuous_bernsteinWeight j).continuousOn.integrableOn_compact
      (isCompact_cube d)).const_mul _
  simp only [bernsteinApprox, integral_finsetSum _ (fun j _ => hint μ hμ j),
    integral_finsetSum _ (fun j _ => hint ν hν j), integral_const_mul,
    integral_bernsteinWeight hμ, integral_bernsteinWeight hν]
  apply sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (hmom _ _ fun i => Nat.sub_le _ _) (Nat.cast_nonneg _)) (hf _)

private theorem measure_le_of_moments {d : ℕ}
    {μ ν : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ cube d) (hν : ∀ᵐ x ∂ν, x ∈ cube d)
    (hmom : ∀ k n : Fin d → ℕ, k ≤ n → diff (momentOf μ) k n ≤ diff (momentOf ν) k n) :
    μ ≤ ν := by
  have hopen (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) : μ U ≤ ν U := by
    rw [hU.measure_eq_biSup_integral_continuous μ, hU.measure_eq_biSup_integral_continuous ν]
    simp only [iSup_le_iff]
    intro f hf hfU hf0 hf1
    refine (ENNReal.ofReal_le_ofReal ?_).trans
      (le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hfU
        (le_iSup_of_le hf0 (le_iSup_of_le hf1 le_rfl)))))
    have hIcc (x : EuclideanSpace ℝ (Fin d)) : f x ∈ Set.Icc 0 1 := ⟨hf0 x, hf1 x⟩
    exact le_of_tendsto_of_tendsto' (tendsto_integral_bernsteinApprox hμ hf hIcc)
      (tendsto_integral_bernsteinApprox hν hf hIcc)
      (fun m => integral_bernsteinApprox_le hμ hν hmom (m + 1) hf0)
  refine Measure.le_iff.mpr fun s _ => ?_
  rw [s.measure_eq_iInf_isOpen ν]
  exact le_iInf₂ fun U hU => le_iInf fun h => (measure_mono hU).trans (hopen U h)

/- **Absolute continuity criterion (Hausdorff moment problem).** A positive
probability measure `μ` on the cube is uniformly absolutely continuous w.r.t.
Lebesgue measure iff there is `C` with `(Δᵏμ)ₙ ≤ C·(Δᵏν)ₙ` for all `k ≤ n`. -/
set_option linter.dupNamespace false in
/-- **Hausdorff's absolute continuity criterion.** Let $\mu$ be a probability measure on
$\mathbb{R}^d$ with $\mu(\mathbb{R}^d \setminus I^d) = 0$, where $I^d = [0,1]^d$ is the closed
unit cube, and let $\lambda$ be Lebesgue measure restricted to $I^d$. For a measure $\rho$ write
$m_\rho(n) = \int_{I^d} x^n \, d\rho(x)$ for its moments, indexed by multi-indices
$n \in \mathbb{N}^d$. Then $\mu$ is uniformly absolutely continuous with respect to $\lambda$ if
and only if there is a real constant $C$ such that
$(\Delta^k m_\mu)_n \le C \, (\Delta^k m_\lambda)_n$ for all multi-indices $k \le n$
(coordinatewise), where $\Delta^k$ is the iterated backward difference.

Source: F. Hausdorff (1921–1923); see Shohat–Tamarkin, *The Problem of Moments*.
Knill, *Some fundamental theorems in mathematics*, §115. Via leanprover/lean-eval@38361be, problem
`hausdorff_absolute_continuity`. -/
public theorem hausdorff_absolute_continuity {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (hμ : μ ((cube d)ᶜ) = 0) :
    UniformlyAbsolutelyContinuous μ (volume.restrict (cube d)) ↔
      ∃ C : ℝ, ∀ k n : Fin d → ℕ, k ≤ n →
        diff (momentOf μ) k n ≤ C * diff (momentOf (volume.restrict (cube d))) k n := by
  let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (cube d)
  have hc : MeasurableSet (cube d) := (isCompact_cube d).measurableSet
  let _ : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (isCompact_cube d).measure_lt_top.ne
  have hμae : ∀ᵐ x ∂μ, x ∈ cube d := by rwa [ae_iff]
  have hνae : ∀ᵐ x ∂ν, x ∈ cube d := ae_restrict_mem hc
  change UniformlyAbsolutelyContinuous μ ν ↔
    ∃ C : ℝ, ∀ k n : Fin d → ℕ, k ≤ n → diff (momentOf μ) k n ≤ C * diff (momentOf ν) k n
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun k n hkn => ?_⟩
    rw [diff_eq_integral μ hkn, diff_eq_integral ν hkn,
      Measure.restrict_eq_self_of_ae_mem hμae, Measure.restrict_eq_self_of_ae_mem hνae]
    change (∫ x, momentKernel k n x ∂μ) ≤ C • ∫ x, momentKernel k n x ∂ν
    rw [← integral_smul_nnreal_measure]
    apply integral_mono_measure hC
    · exact (Measure.ae_smul_measure hνae C).mono fun x hx => momentKernel_nonneg k n hx
    · have h : Integrable (momentKernel k n) ν := by
        rw [← Measure.restrict_eq_self_of_ae_mem hνae]
        exact (continuous_momentKernel k n).continuousOn.integrableOn_compact (isCompact_cube d)
      exact h.smul_measure_nnreal
  · rintro ⟨C, hC⟩
    let C' : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
    have hC' : C ≤ (C' : ℝ) := le_max_left _ _
    have hν' : ∀ᵐ x ∂(C' • ν), x ∈ cube d := Measure.ae_smul_measure hνae C'
    refine ⟨C', measure_le_of_moments hμae hν' (fun k n hkn => ?_)⟩
    have hnonneg : 0 ≤ diff (momentOf ν) k n := by
      rw [diff_eq_integral ν hkn, Measure.restrict_eq_self_of_ae_mem hνae]
      exact integral_nonneg_of_ae (hνae.mono fun x hx => momentKernel_nonneg k n hx)
    calc
      diff (momentOf μ) k n ≤ C * diff (momentOf ν) k n := hC k n hkn
      _ ≤ (C' : ℝ) * diff (momentOf ν) k n := mul_le_mul_of_nonneg_right hC' hnonneg
      _ = _ := by
        rw [diff_eq_integral ν hkn, diff_eq_integral (C' • ν) hkn,
          Measure.restrict_eq_self_of_ae_mem hνae, Measure.restrict_eq_self_of_ae_mem hν',
          integral_smul_nnreal_measure]
        rfl

end Analysis.HausdorffAbsoluteContinuity

end MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted
