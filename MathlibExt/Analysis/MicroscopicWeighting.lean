/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Microscopic weightings of metric spaces

A 24-point space has constant distance row sums, so its uniform mass is a gauging. Its similarity
matrix preserves the two-dimensional space of vectors constant on each of two blocks. On that
space we construct a vector whose coordinates tend to `-6` and `3`. Its potential is constant
across all points and tends to zero. Near zero this vector equals the potential times the
weighting, which rules out convergence of the weighting.
-/

@[expose] public section

namespace MathlibExt.Analysis.MicroscopicWeightingWanted

open Filter Matrix

/-- The matrix of exponentiated negative distances at scale `t`. -/
noncomputable def similarityMatrix (X : Type*) [Fintype X] [MetricSpace X]
    (t : ℝ) : Matrix X X ℝ :=
  Matrix.of fun i j => Real.exp (-t * dist i j)

/-- The matrix of pairwise distances. -/
noncomputable def distanceMatrix (X : Type*) [Fintype X] [MetricSpace X] :
    Matrix X X ℝ :=
  Matrix.of fun i j => dist i j

/-- For a finite metric space $X$ and a real scale $t$, let $S_t$ be the similarity matrix.
The weighting is the vector $S_t^{-1}\mathbf{1}$, where $\mathbf{1}$ is the all-ones vector
and the matrix inverse is taken to be zero when $S_t$ is singular. -/
noncomputable def weighting (X : Type*) [Fintype X] [DecidableEq X] [MetricSpace X]
    (t : ℝ) : X → ℝ :=
  (similarityMatrix X t)⁻¹ *ᵥ 1

/-- The weighting has a finite limit as the scale tends to zero from above. -/
def HasMicroscopicWeighting (X : Type*) [Fintype X] [DecidableEq X]
    [MetricSpace X] : Prop :=
  ∃ w : X → ℝ, Filter.Tendsto (weighting X) (nhdsWithin 0 (Set.Ioi 0)) (nhds w)

/-- For a finite set $X$ and a real $X \times X$ matrix $M$, a vector $g : X \to \mathbb R$
is a gauging at potential $c \in \mathbb R$ if $\sum_{i\in X}g(i)=1$ and
$(Mg)(i)=c$ for every $i\in X$. -/
def IsGauging (X : Type*) [Fintype X] (M : Matrix X X ℝ) (g : X → ℝ)
    (c : ℝ) : Prop :=
  ∑ i, g i = 1 ∧ M *ᵥ g = Function.const X c

/-- The matrix admits a gauging at some finite potential. -/
def HasFiniteConcentration (X : Type*) [Fintype X] (M : Matrix X X ℝ) : Prop :=
  ∃ g c, IsGauging X M g c

/-- This is the proposition that, for every nonempty finite metric space `X` with decidable
equality, `HasMicroscopicWeighting X ↔ HasFiniteConcentration X (distanceMatrix X)`.
It asks whether the weighting has a finite limit as the scale tends to zero from above
exactly when the distance matrix admits a gauging at some real potential. -/
def microscopicWeightingIff : Prop :=
  ∀ (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] [MetricSpace X],
    HasMicroscopicWeighting X ↔ HasFiniteConcentration X (distanceMatrix X)

namespace Counterexample

universe u

private abbrev Colour := ULift.{u} (Fin 4)
private abbrev Point := (Colour.{u} × Fin 2) ⊕ (Colour.{u} × Fin 4)

/-- Each block has four colours, with two points per colour on the left and four on the right. -/
private def steps : Point → Point → ℕ
  | .inl (i, a), .inl (j, b) => if i = j then if a = b then 0 else 6 else 4
  | .inr x, .inr y => if x = y then 0 else 4
  | .inl (i, _), .inr (j, _) | .inr (i, _), .inl (j, _) => if i = j then 6 else 3

private theorem steps_self (x : Point) : steps x x = 0 := by
  rcases x with ⟨i, a⟩ | ⟨i, a⟩ <;> simp [steps]

private theorem steps_comm (x y : Point) : steps x y = steps y x := by
  rcases x with ⟨i, a⟩ | ⟨i, a⟩ <;> rcases y with ⟨j, b⟩ | ⟨j, b⟩ <;> simp [steps, eq_comm]

private theorem steps_bounds {x y : Point} (h : x ≠ y) : 3 ≤ steps x y ∧ steps x y ≤ 6 := by
  rcases x with ⟨i, a⟩ | ⟨i, a⟩ <;> rcases y with ⟨j, b⟩ | ⟨j, b⟩ <;> grind [steps]

private noncomputable local instance pointMetric : MetricSpace Point where
  dist x y := steps x y
  dist_self x := by simp [steps_self]
  dist_comm x y := by rw [steps_comm]
  dist_triangle x y z := by
    by_cases hxy : x = y
    · simp [hxy, steps_self]
    by_cases hyz : y = z
    · simp [hyz, steps_self]
    by_cases hxz : x = z
    · simp only [hxz, steps_self, Nat.cast_zero]
      positivity
    exact_mod_cast (show steps x z ≤ steps x y + steps y z by
      have := steps_bounds hxy
      have := steps_bounds hyz
      have := steps_bounds hxz
      omega)
  eq_of_dist_eq_zero {x y} h := by
    by_contra hne
    have := (steps_bounds hne).1
    exact (show steps x y ≠ 0 by omega) (Nat.cast_eq_zero.mp h)

private def blockVec (a b : ℝ) : Point → ℝ := Sum.elim (fun _ => a) (fun _ => b)

private lemma sum_exception {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (a b : ℝ) :
    (∑ j : ι, if i = j then a else b) = a + (Fintype.card ι - 1 : ℝ) * b := by
  have h (j : ι) : (if i = j then a else b) = (if i = j then a - b else 0) + b := by
    split <;> simp [*]
  simp_rw [h, Finset.sum_add_distrib]
  simp
  ring

/-- Row sums for any kernel depending only on distance and any vector constant on each block. -/
private lemma block_rows (f : ℕ → ℝ) (a b : ℝ) :
    (Matrix.of fun i j : Point.{u} => f (steps i j)) *ᵥ blockVec a b =
      blockVec ((f 0 + f 6 + 6 * f 4) * a + (4 * f 6 + 12 * f 3) * b)
        ((2 * f 6 + 6 * f 3) * a + (f 0 + 15 * f 4) * b) := by
  funext i
  rcases i with ⟨i, x⟩ | ⟨i, x⟩ <;>
    simp [mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, blockVec, steps,
      apply_ite f, ite_mul, Fin.sum_univ_succ, Finset.sum_add_distrib, sum_exception, Colour] <;>
    ring

private lemma hasFiniteConcentration : HasFiniteConcentration Point.{u} (distanceMatrix Point) := by
  refine ⟨blockVec (1 / 24) (1 / 24), 15 / 4, ?_, ?_⟩
  · norm_num [Fintype.sum_sum_type, blockVec, Colour]
  · change (Matrix.of fun i j : Point => (steps i j : ℝ)) *ᵥ _ = _
    rw [block_rows]
    funext i
    cases i <;> norm_num [blockVec, Function.const]

open Polynomial Topology

private noncomputable def kernel (q : ℝ) : Matrix Point Point ℝ :=
  Matrix.of fun i j => q ^ steps i j

private lemma similarity_eq_kernel (t : ℝ) :
    similarityMatrix Point.{u} t = kernel (Real.exp (-t)) := by
  ext i j
  change Real.exp (-t * (steps i j : ℝ)) = Real.exp (-t) ^ steps i j
  rw [mul_comm, Real.exp_nat_mul]

/-- The determinant polynomial has constant term one, so only finitely many parameters can
give singular matrices. -/
private lemma eventually_nonsingular :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), IsUnit (similarityMatrix Point.{u} t).det := by
  let P : Matrix Point.{u} Point (Polynomial ℝ) := Matrix.of fun i j => X ^ steps i j
  have eval_det (q : ℝ) : P.det.eval q = (kernel.{u} q).det := by
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [P, kernel]
  have hzero : kernel.{u} 0 = 1 := by
    ext i j
    by_cases h : i = j
    · simp [kernel, Matrix.one_apply, h, steps_self]
    · have hn := (steps_bounds h).1
      simp [kernel, one_apply, h, zero_pow (show steps i j ≠ 0 by omega)]
  have hP : P.det ≠ 0 := by
    intro h
    simpa [h, hzero] using eval_det 0
  have hinj : Function.Injective (fun t : ℝ => Real.exp (-t)) :=
    Real.exp_injective.comp neg_injective
  have ht := hinj.tendsto_cofinite.mono_left
    ((nhdsGT_le_nhdsNE (0 : ℝ)).trans (nhdsNE_le_cofinite 0))
  filter_upwards [ht.eventually (eventually_eval_ne_zero_cofinite hP)] with t ht
  simpa [similarity_eq_kernel, ← eval_det, isUnit_iff_ne_zero] using ht

-- These are the differences of the two entries in each column of the block matrix
-- (with opposite signs), divided by their common factor (q - 1)².
private noncomputable def leftWeight (q : ℝ) :=
  1 + 2 * q + 3 * q ^ 2 - 8 * q ^ 3 - 4 * q ^ 4

private noncomputable def rightWeight (q : ℝ) :=
  1 + 2 * q + 3 * q ^ 2 - 2 * q ^ 3 - q ^ 4

private noncomputable def potential (q : ℝ) :=
  (1 + q ^ 6 + 6 * q ^ 4) * leftWeight q + (4 * q ^ 6 + 12 * q ^ 3) * rightWeight q

private lemma kernel_weights (q : ℝ) :
    kernel.{u} q *ᵥ blockVec (leftWeight q) (rightWeight q) =
      potential q • (1 : Point → ℝ) := by
  unfold kernel
  rw [block_rows]
  funext i
  cases i <;> simp [blockVec, potential, leftWeight, rightWeight]
  ring

private lemma not_hasMicroscopicWeighting : ¬ HasMicroscopicWeighting Point.{u} := by
  rintro ⟨w, hw⟩
  let i : Point.{u} := Sum.inl (⟨0⟩, 0)
  have heq : (fun t => potential (Real.exp (-t)) * weighting Point t i)
      =ᶠ[𝓝[>] 0] fun t => leftWeight (Real.exp (-t)) := by
    filter_upwards [eventually_nonsingular.{u}] with t ht
    have hv := kernel_weights.{u} (Real.exp (-t))
    rw [← similarity_eq_kernel] at hv
    have hinv := congrArg ((similarityMatrix Point t)⁻¹ *ᵥ ·) hv
    rw [mulVec_mulVec, nonsing_inv_mul _ ht, one_mulVec, mulVec_smul] at hinv
    exact (congrFun hinv i).symm
  have hq : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    simpa [Function.comp_def] using (Real.continuous_exp.comp continuous_neg).continuousAt
      (x := (0 : ℝ)) |>.tendsto.mono_left nhdsWithin_le_nhds
  have hp : Continuous potential := by unfold potential leftWeight rightWeight; fun_prop
  have hl : Continuous leftWeight := by unfold leftWeight; fun_prop
  have h := tendsto_nhds_unique_of_eventuallyEq
    ((hp.continuousAt.tendsto.comp hq).mul (tendsto_pi_nhds.mp hw i))
    (hl.continuousAt.tendsto.comp hq) heq
  norm_num [potential, leftWeight, rightWeight] at h

end Counterexample

/--
**Microscopic weighting is not equivalent to finite concentration.** It is not true that every
nonempty finite metric space $X$ has a microscopic weighting if and only if it has finite
concentration. Here, for real $t$, $Z_t$ is the $X \times X$ matrix with entries
$e^{-t\,d(x,y)}$ and $w_t = Z_t^{-1}\mathbf{1}$ is its weighting, where $\mathbf{1}$ is the
all-ones vector and the inverse of a singular matrix is taken to be $0$. The space $X$ has a
microscopic weighting if $w_t$ converges to some $w \colon X \to \mathbb{R}$ as $t \to 0^+$. It
has finite concentration if there are $g \colon X \to \mathbb{R}$ with $\sum_{x \in X} g(x) = 1$
and $c \in \mathbb{R}$ such that $\sum_{y \in X} d(x,y)\,g(y) = c$ for every $x \in X$.

Kenta Kitamura (assisted by ChatGPT) gave an explicit 10-point metric space with finite
concentration but no microscopic weighting.

Source: Kenta Kitamura, microscopic-weighting-counterexample, Lean formalization of the 10-point
counterexample,
https://github.com/KitaKen1/microscopic-weighting-counterexample/blob/eff8979/lean/MicroscopicWeightingCounterexampleFC.lean#L886-L894.
Moved from `OpenConjectures/Analysis/MicroscopicWeighting`.
-/
public theorem microscopicWeightingIff_refuted : ¬ microscopicWeightingIff := by
  intro h
  let := Counterexample.pointMetric
  exact Counterexample.not_hasMicroscopicWeighting
    ((h Counterexample.Point).2 Counterexample.hasFiniteConcentration)

end MathlibExt.Analysis.MicroscopicWeightingWanted
