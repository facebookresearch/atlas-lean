/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import MathlibExt.Analysis.Convex.GradientDescent
import MathlibExt.Analysis.Convex.GradientDescentStronglyConvex

/-!
# Nesterov's estimate-sequence method

The optimal first-order method of Nesterov for an `L`-smooth, `μ`-strongly convex function
(`μ = 0` allowed), analysed as in Section 2.2 of Yu. Nesterov, *Introductory Lectures on Convex
Programming, Volume I: Basic course* (lecture notes, July 2, 1998; hereafter [N98]).

The general scheme (2.2.6) of [N98] keeps three sequences `x k`, `y k`, `v k` and two scalar
sequences `α k ∈ (0, 1]`, `γ k > 0` with

* `L * α k ^ 2 = γ (k + 1) = (1 - α k) * γ k + α k * μ`;
* `y k = (α k * γ k * v k + γ (k + 1) * x k) / (γ k + α k * μ)`;
* `f (x (k + 1)) ≤ f (y k) - ‖∇f (y k)‖ ^ 2 / (2 L)` (for instance a gradient step `1 / L`);
* `v (k + 1) = ((1 - α k) * γ k * v k + α k * μ * y k - α k * ∇f (y k)) / γ (k + 1)`.

The estimate functions `φ k (x) = φ k⋆ + γ k / 2 * ‖x - v k‖ ^ 2` of Lemma 2.2.3 of [N98] are
encoded here by the potential `f (x k) - f u + γ k / 2 * ‖v k - u‖ ^ 2`, which contracts by the
factor `1 - α k` at every step for every point `u`.

## Main results

* `estimateSequence_step`: one step contracts the potential by `1 - α`.
* `estimateSequence_rate`: Theorem 2.2.1 of [N98], `f (x k) - f u ≤ λ k (f (x 0) - f u +
  γ 0 / 2 ‖x 0 - u‖²)` with `λ k = ∏_{i < k} (1 - α i)`.
* `estimateSequence_lambda_le`: Lemma 2.2.4 of [N98], the two bounds on `λ k`.
* `estimateSequence_optimal_rate`: Theorem 2.2.2 of [N98], the rate
  `L min {(1 - √(μ / L)) ^ k, 4 / (k + 2) ^ 2} ‖x 0 - x⋆‖²` for `γ 0 = L`.
* `accelerated_strongly_convex_rate`: the constant-step method with `α = √(μ / L)`
  (`γ 0 = μ`) and its linear rate `(1 - √(μ / L)) ^ k`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.EstimateSequence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Expansion of `‖p • a + q • b - c • g‖ ^ 2` in inner products. -/
private lemma norm_sq_comb (p q c : ℝ) (a b g : E) :
    ‖p • a + q • b - c • g‖ ^ 2 = p ^ 2 * ‖a‖ ^ 2 + q ^ 2 * ‖b‖ ^ 2 + c ^ 2 * ‖g‖ ^ 2
      + 2 * p * q * inner ℝ a b - 2 * p * c * inner ℝ a g - 2 * q * c * inner ℝ b g := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq a,
    ← real_inner_self_eq_norm_sq b, ← real_inner_self_eq_norm_sq g]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm a b, real_inner_comm a g,
    real_inner_comm b g]
  ring

/-- **One step of Nesterov's estimate-sequence method contracts its potential.**
Let `f` be differentiable and `μ`-strongly convex (`μ ≥ 0`) on a real Hilbert space, `L > 0` and
`u` any point. Let `α ∈ [0, 1]`, `γ ≥ 0`, `γ' > 0` with `γ' = (1 - α) γ + α μ = L α ²`, and let
`y, x', v'` satisfy `(γ + α μ) y = α γ v + γ' x`, `f x' ≤ f y - ‖∇f y‖ ^ 2 / (2 L)` and
`γ' v' = (1 - α) γ v + α μ y - α ∇f y`. Then
`f x' - f u + γ' / 2 ‖v' - u‖ ^ 2 ≤ (1 - α) (f x - f u + γ / 2 ‖v - u‖ ^ 2)`.

This is the inductive step of the proof of Theorem 2.2.1 of Yu. Nesterov, *Introductory Lectures
on Convex Programming, Volume I: Basic course* (lecture notes, July 2, 1998), written as a
potential: Lemmas 2.2.2 and 2.2.3 there (the estimate sequence `φ k` and its canonical form
`φ k⋆ + γ k / 2 ‖x - v k‖ ^ 2`) together with the derivation of the scheme (2.2.6), evaluated at
the point `u` instead of being minimised over it. -/
theorem estimateSequence_step {f : E → ℝ} {L μ : ℝ} (hL : 0 < L) (hμ : 0 ≤ μ)
    (hf : StrongConvexOn Set.univ μ f) (hdiff : Differentiable ℝ f) (u : E)
    {α γ γ' : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hγ : 0 ≤ γ) (hγ'pos : 0 < γ')
    (hγ' : γ' = (1 - α) * γ + α * μ) (hαL : L * α ^ 2 = γ')
    {x v y x' v' : E}
    (hy : (γ + α * μ) • y = (α * γ) • v + γ' • x)
    (hdec : f x' ≤ f y - ‖gradient f y‖ ^ 2 / (2 * L))
    (hv : γ' • v' = ((1 - α) * γ) • v + (α * μ) • y - α • gradient f y) :
    f x' - f u + γ' / 2 * ‖v' - u‖ ^ 2 ≤ (1 - α) * (f x - f u + γ / 2 * ‖v - u‖ ^ 2) := by
  set g := gradient f y with hg
  have hgrad : HasGradientAt f g y := (hdiff y).hasGradientAt
  have hcx := GradientDescentStronglyConvex.add_inner_add_le_of_strongConvexOn
    hf (Set.mem_univ y) (Set.mem_univ x) hgrad
  have hcu := GradientDescentStronglyConvex.add_inner_add_le_of_strongConvexOn
    hf (Set.mem_univ y) (Set.mem_univ u) hgrad
  -- the vector recursion for `v' - u`
  have hvu : γ' • (v' - u) = ((1 - α) * γ) • (v - u) + (α * μ) • (y - u) - α • g := by
    rw [smul_sub, hv, hγ']
    module
  have hnorm : γ' ^ 2 * ‖v' - u‖ ^ 2 =
      ‖((1 - α) * γ) • (v - u) + (α * μ) • (y - u) - α • g‖ ^ 2 := by
    rw [← hvu, norm_smul, Real.norm_eq_abs, abs_of_pos hγ'pos, mul_pow]
  rw [norm_sq_comb] at hnorm
  -- the coupling relation for `y`
  have hI : γ' * inner ℝ g (y - x) + α * γ * inner ℝ g (y - v) = 0 := by
    have h := congrArg (inner ℝ g) hy
    simp only [inner_add_right, real_inner_smul_right] at h
    simp only [inner_sub_right]
    rw [hγ'] at h ⊢
    linarith
  -- inner products against `u`
  have e1 : inner ℝ (v - u) g = inner ℝ g v - inner ℝ g u := by
    rw [real_inner_comm, inner_sub_right]
  have e2 : inner ℝ (y - u) g = inner ℝ g y - inner ℝ g u := by
    rw [real_inner_comm, inner_sub_right]
  have e3 : inner ℝ g (y - x) = inner ℝ g y - inner ℝ g x := inner_sub_right _ _ _
  have e4 : inner ℝ g (y - v) = inner ℝ g y - inner ℝ g v := inner_sub_right _ _ _
  have e5 : inner ℝ g (x - y) = inner ℝ g x - inner ℝ g y := inner_sub_right _ _ _
  have e6 : inner ℝ g (u - y) = inner ℝ g u - inner ℝ g y := inner_sub_right _ _ _
  have e7 : ‖u - y‖ = ‖y - u‖ := norm_sub_rev _ _
  rw [e1, e2] at hnorm
  rw [e3, e4] at hI
  rw [e5] at hcx
  rw [e6, e7] at hcu
  -- the weighted convexity of the squared norm
  have hab : 0 ≤ ‖(v - u) - (y - u)‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real] at hab
  have hpq : 0 ≤ ((1 - α) * γ) * (α * μ) := by
    have : 0 ≤ 1 - α := by linarith
    positivity
  have hconvx : 0 ≤ μ / 2 * ‖x - y‖ ^ 2 := by positivity
  -- `γ' / L = α ^ 2`
  have hGL : γ' * (‖g‖ ^ 2 / (2 * L)) = α ^ 2 * ‖g‖ ^ 2 / 2 := by
    rw [← hαL]; field_simp
  have h1α : 0 ≤ 1 - α := by linarith
  have ka := mul_le_mul_of_nonneg_left hdec (by positivity : (0 : ℝ) ≤ 2 * γ')
  have kb := mul_le_mul_of_nonneg_left hcx (by positivity : (0 : ℝ) ≤ 2 * γ' * (1 - α))
  have kc := mul_le_mul_of_nonneg_left hcu (by positivity : (0 : ℝ) ≤ 2 * γ' * α)
  have kd := mul_nonneg hpq hab
  have kx := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * γ' * (1 - α)) hconvx
  -- multiply the goal by `2 γ' > 0`
  rw [← mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 2 * γ')]
  have hgoal : 2 * γ' * (f x' - f u + γ' / 2 * ‖v' - u‖ ^ 2) =
      2 * γ' * (f x' - f u) + γ' ^ 2 * ‖v' - u‖ ^ 2 := by ring
  rw [hgoal, hnorm]
  have kI := congrArg (fun t => 2 * (1 - α) * t) hI
  simp only [mul_zero] at kI
  subst hγ'
  linarith [ka, kb, kc, kd, kx, hGL, kI]

/-- **Nesterov's general optimal scheme.** The sequences `α γ : ℕ → ℝ` and
`x y v : ℕ → E` follow the scheme (2.2.6) of Yu. Nesterov, *Introductory Lectures on Convex
Programming, Volume I: Basic course* (lecture notes, July 2, 1998), for a function `f` with
smoothness constant `L` and strong-convexity parameter `μ`: `γ 0 > 0`, `v 0 = x 0`, and for
every `k`, `α k ∈ (0, 1]` solves `L α k ^ 2 = (1 - α k) γ k + α k μ = γ (k + 1)`,
`y k = (α k γ k v k + γ (k + 1) x k) / (γ k + α k μ)`,
`f (x (k + 1)) ≤ f (y k) - ‖∇f (y k)‖ ^ 2 / (2 L)` and
`v (k + 1) = ((1 - α k) γ k v k + α k μ y k - α k ∇f (y k)) / γ (k + 1)`.
The divisions of the source are written multiplied out. The source asks `α k ∈ (0, 1)`; the
value `α k = 1` is allowed here. A gradient step `x (k + 1) = y k - ∇f (y k) / L` satisfies the
descent condition when `∇f` is `L`-Lipschitz (Constant Step Scheme I, (2.2.7), of the source). -/
structure IsNesterovScheme (f : E → ℝ) (L μ : ℝ) (α γ : ℕ → ℝ) (x y v : ℕ → E) : Prop where
  alpha_pos : ∀ k, 0 < α k
  alpha_le_one : ∀ k, α k ≤ 1
  gamma_zero_pos : 0 < γ 0
  gamma_succ : ∀ k, γ (k + 1) = (1 - α k) * γ k + α k * μ
  alpha_sq : ∀ k, L * α k ^ 2 = γ (k + 1)
  v_zero : v 0 = x 0
  y_eq : ∀ k, (γ k + α k * μ) • y k = (α k * γ k) • v k + γ (k + 1) • x k
  descent : ∀ k, f (x (k + 1)) ≤ f (y k) - ‖gradient f (y k)‖ ^ 2 / (2 * L)
  v_succ : ∀ k, γ (k + 1) • v (k + 1) =
    ((1 - α k) * γ k) • v k + (α k * μ) • y k - α k • gradient f (y k)

private lemma gamma_pos_of {f : E → ℝ} {L μ : ℝ} {α γ : ℕ → ℝ} {x y v : ℕ → E}
    (hS : IsNesterovScheme f L μ α γ x y v) (hL : 0 < L) : ∀ k, 0 < γ k
  | 0 => hS.gamma_zero_pos
  | k + 1 => by rw [← hS.alpha_sq k]; have := hS.alpha_pos k; positivity

private lemma potential_le {f : E → ℝ} {L μ : ℝ} {α γ : ℕ → ℝ} {x y v : ℕ → E}
    (hS : IsNesterovScheme f L μ α γ x y v) (hL : 0 < L) (hμ : 0 ≤ μ)
    (hf : StrongConvexOn Set.univ μ f) (hdiff : Differentiable ℝ f) (u : E) (k : ℕ) :
    f (x k) - f u + γ k / 2 * ‖v k - u‖ ^ 2 ≤
      (∏ i ∈ Finset.range k, (1 - α i)) * (f (x 0) - f u + γ 0 / 2 * ‖x 0 - u‖ ^ 2) := by
  induction k with
  | zero => simp [hS.v_zero]
  | succ k ih =>
    have hstep := estimateSequence_step hL hμ hf hdiff u (hS.alpha_pos k).le
      (hS.alpha_le_one k) (gamma_pos_of hS hL k).le (gamma_pos_of hS hL (k + 1)) (hS.gamma_succ k)
      (hS.alpha_sq k) (hS.y_eq k) (hS.descent k) (hS.v_succ k)
    have h1 : 0 ≤ 1 - α k := by linarith [hS.alpha_le_one k]
    rw [Finset.prod_range_succ]
    calc _ ≤ (1 - α k) * (f (x k) - f u + γ k / 2 * ‖v k - u‖ ^ 2) := hstep
      _ ≤ (1 - α k) * ((∏ i ∈ Finset.range k, (1 - α i)) *
            (f (x 0) - f u + γ 0 / 2 * ‖x 0 - u‖ ^ 2)) := mul_le_mul_of_nonneg_left ih h1
      _ = _ := by ring

/-- **Convergence of Nesterov's estimate-sequence scheme.** Let `f` be differentiable and
`μ`-strongly convex (`μ ≥ 0`) on a real Hilbert space and `L > 0`. If the sequences follow
Nesterov's scheme (2.2.6) (`IsNesterovScheme`), then for every point `u` and every `k`,
`f (x k) - f u ≤ λ k (f (x 0) - f u + γ 0 / 2 ‖x 0 - u‖ ^ 2)` with
`λ k = ∏_{i < k} (1 - α i)`.

This is Theorem 2.2.1 of Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I:
Basic course* (lecture notes, July 2, 1998), stated there with `u = x⋆` a minimiser; here for
every point `u`. -/
theorem estimateSequence_rate {f : E → ℝ} {L μ : ℝ} {α γ : ℕ → ℝ} {x y v : ℕ → E}
    (hS : IsNesterovScheme f L μ α γ x y v) (hL : 0 < L) (hμ : 0 ≤ μ)
    (hf : StrongConvexOn Set.univ μ f) (hdiff : Differentiable ℝ f) (u : E) (k : ℕ) :
    f (x k) - f u ≤
      (∏ i ∈ Finset.range k, (1 - α i)) * (f (x 0) - f u + γ 0 / 2 * ‖x 0 - u‖ ^ 2) := by
  have h := potential_le hS hL hμ hf hdiff u k
  have : 0 ≤ γ k / 2 * ‖v k - u‖ ^ 2 := by have := gamma_pos_of hS hL k; positivity
  linarith

/-- **Decay of the scaling sequence of Nesterov's scheme.** If the sequences follow Nesterov's
scheme (2.2.6) (`IsNesterovScheme`) with `L > 0`, `0 ≤ μ ≤ γ 0`, then
`λ k = ∏_{i < k} (1 - α i)` satisfies `λ k ≤ (1 - √(μ / L)) ^ k` and
`λ k ≤ 4 L / (2 √L + k √(γ 0)) ^ 2`.

This is Lemma 2.2.4 of Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I:
Basic course* (lecture notes, July 2, 1998), which states the minimum of the two bounds. -/
theorem estimateSequence_lambda_le {f : E → ℝ} {L μ : ℝ} {α γ : ℕ → ℝ} {x y v : ℕ → E}
    (hS : IsNesterovScheme f L μ α γ x y v) (hL : 0 < L) (hμ : 0 ≤ μ) (hμγ : μ ≤ γ 0) (k : ℕ) :
    (∏ i ∈ Finset.range k, (1 - α i)) ≤ (1 - √(μ / L)) ^ k ∧
      (∏ i ∈ Finset.range k, (1 - α i)) ≤ 4 * L / (2 * √L + k * √(γ 0)) ^ 2 := by
  set lam : ℕ → ℝ := fun k => ∏ i ∈ Finset.range k, (1 - α i) with hlam
  have hlam_succ : ∀ k, lam (k + 1) = (1 - α k) * lam k := by
    intro k; simp only [hlam, Finset.prod_range_succ]; ring
  have h1α : ∀ k, 0 ≤ 1 - α k := fun k => by linarith [hS.alpha_le_one k]
  have hlam_nonneg : ∀ k, 0 ≤ lam k := fun k =>
    Finset.prod_nonneg fun i _ => h1α i
  -- `γ k ≥ μ` and `α k ≥ √(μ / L)`
  have hγμ : ∀ k, μ ≤ γ k := by
    intro k
    induction k with
    | zero => exact hμγ
    | succ k ih =>
      rw [hS.gamma_succ k]
      nlinarith [h1α k, hS.alpha_pos k]
  have hαμ : ∀ k, √(μ / L) ≤ α k := by
    intro k
    rw [show α k = √(α k ^ 2) by rw [Real.sqrt_sq (hS.alpha_pos k).le]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hL, mul_comm, hS.alpha_sq k]
    exact hγμ (k + 1)
  refine ⟨?_, ?_⟩
  · change lam k ≤ _
    induction k with
    | zero => simp [hlam]
    | succ k ih =>
      rw [hlam_succ, pow_succ, mul_comm (_ ^ k)]
      exact mul_le_mul (by linarith [hαμ k]) ih (hlam_nonneg k)
        (by linarith [hS.alpha_le_one k, hαμ k])
  · change lam k ≤ _
    -- `γ k ≥ γ 0 λ k`
    have hγlam : ∀ k, γ 0 * lam k ≤ γ k := by
      intro k
      induction k with
      | zero => simp [hlam]
      | succ k ih =>
        rw [hlam_succ, hS.gamma_succ k]
        nlinarith [h1α k, hS.alpha_pos k, ih]
    have hγ0 := hS.gamma_zero_pos
    have hsL : 0 < √L := Real.sqrt_pos.mpr hL
    have hsγ : 0 < √(γ 0) := Real.sqrt_pos.mpr hγ0
    -- `√(λ k) (2 √L + k √(γ 0)) ≤ 2 √L`
    have key : ∀ k : ℕ, √(lam k) * (2 * √L + k * √(γ 0)) ≤ 2 * √L := by
      intro k
      induction k with
      | zero => simp [hlam]
      | succ k ih =>
        set s := √(lam k) with hs
        set t := √(lam (k + 1)) with ht
        have hs0 : 0 ≤ s := Real.sqrt_nonneg _
        have ht0 : 0 ≤ t := Real.sqrt_nonneg _
        rcases ht0.lt_or_eq with htpos | htz
        · have hss : s ^ 2 = lam k := Real.sq_sqrt (hlam_nonneg k)
          have htt : t ^ 2 = lam (k + 1) := Real.sq_sqrt (hlam_nonneg (k + 1))
          have hts : t ^ 2 = (1 - α k) * s ^ 2 := by rw [htt, hss, hlam_succ]
          have hspos : 0 < s := by
            rcases hs0.lt_or_eq with h | h
            · exact h
            · rw [← h] at hts; nlinarith
          have hLsq : √L ^ 2 = L := Real.sq_sqrt hL.le
          have hγsq : √(γ 0) ^ 2 = γ 0 := Real.sq_sqrt hγ0.le
          -- `α k √L ≥ √(γ 0) t`
          have hsq : (√(γ 0) * t) ^ 2 ≤ (α k * √L) ^ 2 := by
            rw [mul_pow, mul_pow, hLsq, hγsq, htt, mul_comm _ L, hS.alpha_sq k]
            exact hγlam (k + 1)
          have hαt : √(γ 0) * t ≤ α k * √L :=
            (pow_le_pow_iff_left₀ (by positivity)
              (mul_nonneg (hS.alpha_pos k).le hsL.le) two_ne_zero).mp hsq
          have hts' : t ≤ s := by nlinarith [hS.alpha_pos k]
          -- `2 (s - t) √L ≥ √(γ 0) t s`
          have hdiff : (s - t) * (s + t) = α k * s ^ 2 := by nlinarith
          have H2 : √(γ 0) * t * s ≤ 2 * (s - t) * √L := by
            have h3 : √(γ 0) * t * s ^ 2 ≤ α k * s ^ 2 * √L := by
              nlinarith [mul_le_mul_of_nonneg_right hαt (sq_nonneg s)]
            have h4 : (s - t) * (s + t) * √L ≤ 2 * (s - t) * √L * s := by
              have : 0 ≤ (s - t) * √L := mul_nonneg (by linarith) hsL.le
              nlinarith
            have h5 : s * (√(γ 0) * t * s) ≤ s * (2 * (s - t) * √L) := by
              nlinarith [hdiff]
            exact le_of_mul_le_mul_left h5 hspos
          have hD : s * (t * (2 * √L + (k + 1 : ℕ) * √(γ 0))) ≤ s * (2 * √L) := by
            have := mul_le_mul_of_nonneg_left ih ht0
            push_cast
            nlinarith [this, H2]
          exact le_of_mul_le_mul_left hD hspos
        · rw [← htz, zero_mul]; positivity
    have hD : 0 < 2 * √L + k * √(γ 0) := by positivity
    have hk := key k
    have hsq := mul_self_le_mul_self (mul_nonneg (Real.sqrt_nonneg _) hD.le) hk
    rw [le_div_iff₀ (by positivity)]
    have : √(lam k) * √(lam k) = lam k := Real.mul_self_sqrt (hlam_nonneg k)
    have h4 : 2 * √L * (2 * √L) = 4 * L := by
      rw [show 2 * √L * (2 * √L) = 4 * (√L * √L) by ring, Real.mul_self_sqrt hL.le]
    nlinarith [this, h4, hsq]

/-- **Optimal rate of Nesterov's scheme started at `γ 0 = L`.**
Let `f` be differentiable and `μ`-strongly convex on a real Hilbert space with `L`-Lipschitz
gradient, `0 ≤ μ ≤ L`, `L > 0`, and let `x⋆` minimise `f`. If the sequences follow Nesterov's
scheme (2.2.6) (`IsNesterovScheme`) started with `γ 0 = L`, then for every `k`,
`f (x k) - f x⋆ ≤ L min {(1 - √(μ / L)) ^ k, 4 / (k + 2) ^ 2} ‖x 0 - x⋆‖ ^ 2`.

This is the inequality of Theorem 2.2.2 of Yu. Nesterov, *Introductory Lectures on Convex
Programming, Volume I: Basic course* (lecture notes, July 2, 1998). With `μ = 0` it is the
`O(1 / k²)` rate `4 L ‖x 0 - x⋆‖ ^ 2 / (k + 2) ^ 2`, within a constant factor of the lower
complexity bound `3 L ‖x 0 - x⋆‖ ^ 2 / (32 (k + 1) ^ 2)` of Theorem 2.1.6 there (valid for
`2 k + 1 ≤ n` in dimension `n`). -/
theorem estimateSequence_optimal_rate {f : E → ℝ} {L μ : ℝ} {α γ : ℕ → ℝ} {x y v : ℕ → E}
    (hS : IsNesterovScheme f L μ α γ x y v) (hL : 0 < L) (hμ : 0 ≤ μ) (hμL : μ ≤ L)
    (hf : StrongConvexOn Set.univ μ f) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, hL.le⟩ (gradient f)) (hγ0 : γ 0 = L)
    {xstar : E} (hmin : ∀ z, f xstar ≤ f z) (k : ℕ) :
    f (x k) - f xstar ≤ L * min ((1 - √(μ / L)) ^ k) (4 / ((k : ℝ) + 2) ^ 2) *
      ‖x 0 - xstar‖ ^ 2 := by
  have hrate := estimateSequence_rate hS hL hμ hf hdiff xstar k
  obtain ⟨hl1, hl2⟩ := estimateSequence_lambda_le hS hL hμ (hγ0 ▸ hμL) k
  set lam := ∏ i ∈ Finset.range k, (1 - α i)
  have hlam0 : 0 ≤ lam := Finset.prod_nonneg fun i _ => by linarith [hS.alpha_le_one i]
  -- `f (x 0) - f x⋆ ≤ L / 2 ‖x 0 - x⋆‖ ^ 2`
  have hgrad0 : gradient f xstar = 0 := by
    have h : IsLocalMin f xstar := Filter.Eventually.of_forall hmin
    have h0 : fderiv ℝ f xstar = 0 := IsLocalMin.fderiv_eq_zero h
    simp [gradient, h0]
  have hdesc := MetaMathlibExt.gradientDescent_descent_lemma hL.le hdiff hsmooth xstar
    (x 0 - xstar)
  rw [hgrad0, inner_zero_left, add_sub_cancel] at hdesc
  have hB : f (x 0) - f xstar + γ 0 / 2 * ‖x 0 - xstar‖ ^ 2 ≤ L * ‖x 0 - xstar‖ ^ 2 := by
    rw [hγ0]; linarith
  have hB0 : 0 ≤ f (x 0) - f xstar + γ 0 / 2 * ‖x 0 - xstar‖ ^ 2 := by
    have := hmin (x 0); have := hS.gamma_zero_pos; positivity
  -- `4 L / (2 √L + k √L) ^ 2 = 4 / (k + 2) ^ 2`
  have hsL : 0 < √L := Real.sqrt_pos.mpr hL
  have h42 : 4 * L / (2 * √L + k * √(γ 0)) ^ 2 = 4 / ((k : ℝ) + 2) ^ 2 := by
    rw [hγ0, show 2 * √L + k * √L = ((k : ℝ) + 2) * √L by ring, mul_pow,
      Real.sq_sqrt hL.le]
    field_simp
  rw [h42] at hl2
  have hmin' : lam ≤ min ((1 - √(μ / L)) ^ k) (4 / ((k : ℝ) + 2) ^ 2) := le_min hl1 hl2
  calc f (x k) - f xstar ≤ lam * (f (x 0) - f xstar + γ 0 / 2 * ‖x 0 - xstar‖ ^ 2) := hrate
    _ ≤ lam * (L * ‖x 0 - xstar‖ ^ 2) := mul_le_mul_of_nonneg_left hB hlam0
    _ ≤ min ((1 - √(μ / L)) ^ k) (4 / ((k : ℝ) + 2) ^ 2) * (L * ‖x 0 - xstar‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hmin' (by positivity)
    _ = _ := by ring

/-- **Linear rate of the accelerated gradient method for strongly convex functions.**
Let `f` be differentiable and `μ`-strongly convex on a real Hilbert space with `L`-Lipschitz
gradient, `0 < μ ≤ L`, and put `q = √(μ / L)`. Run, from `x 0 = v 0`,
`y k = (x k + q v k) / (1 + q)`, `x (k + 1) = y k - ∇f (y k) / L` and
`v (k + 1) = (1 - q) v k + q y k - (q / μ) ∇f (y k)`.
Then for every point `u` and every `k`,
`f (x k) - f u ≤ (1 - √(μ / L)) ^ k (f (x 0) - f u + μ / 2 ‖x 0 - u‖ ^ 2)`.

This is Constant Step Scheme I, (2.2.7), of Yu. Nesterov, *Introductory Lectures on Convex
Programming, Volume I: Basic course* (lecture notes, July 2, 1998), with `γ 0 = μ`, for which
`γ k = μ` and `α k = √(μ / L)` for all `k`; the bound is Theorem 2.2.1 there with the first bound
of Lemma 2.2.4, stated there for `u = x⋆`. Against the lower bound
`(μ / 2) ((√(L / μ) - 1) / (√(L / μ) + 1)) ^ (2 k) ‖x 0 - x⋆‖ ^ 2` of Theorem 2.1.12 there, the
number of iterations is optimal up to a constant factor. -/
theorem accelerated_strongly_convex_rate {f : E → ℝ} {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ)
    (hμL : μ ≤ L) (hf : StrongConvexOn Set.univ μ f) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, hL.le⟩ (gradient f)) {x y v : ℕ → E} (hv0 : v 0 = x 0)
    (hy : ∀ k, y k = (1 + √(μ / L))⁻¹ • (x k + √(μ / L) • v k))
    (hx : ∀ k, x (k + 1) = y k - (1 / L) • gradient f (y k))
    (hv : ∀ k, v (k + 1) = (1 - √(μ / L)) • v k + √(μ / L) • y k -
      (√(μ / L) / μ) • gradient f (y k))
    (u : E) (k : ℕ) :
    f (x k) - f u ≤ (1 - √(μ / L)) ^ k * (f (x 0) - f u + μ / 2 * ‖x 0 - u‖ ^ 2) := by
  set q := √(μ / L) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr (div_pos hμ hL)
  have hq1 : q ≤ 1 := by
    rw [hq, Real.sqrt_le_one]; exact (div_le_one hL).mpr hμL
  have hLq : L * q ^ 2 = μ := by
    rw [hq, Real.sq_sqrt (div_pos hμ hL).le]; field_simp
  have hS : IsNesterovScheme f L μ (fun _ => q) (fun _ => μ) x y v :=
    { alpha_pos := fun _ => hq0
      alpha_le_one := fun _ => hq1
      gamma_zero_pos := hμ
      gamma_succ := fun _ => by ring
      alpha_sq := fun _ => hLq
      v_zero := hv0
      y_eq := fun k => by
        rw [hy k, smul_smul, smul_add, smul_smul]
        have h1q : (1 + q) ≠ 0 := by positivity
        rw [show (μ + q * μ) * (1 + q)⁻¹ = μ by field_simp]
        module
      descent := fun k => by
        have h := MetaMathlibExt.gradientDescent_sufficient_decrease hL hdiff hsmooth
          (η := 1 / L) ⟨by positivity, le_rfl⟩ (y k)
        rw [hx k]
        calc f (y k - (1 / L) • gradient f (y k))
            ≤ f (y k) - 1 / L / 2 * ‖gradient f (y k)‖ ^ 2 := h
          _ = f (y k) - ‖gradient f (y k)‖ ^ 2 / (2 * L) := by field_simp
      v_succ := fun k => by
        rw [hv k, smul_sub, smul_add, smul_smul, smul_smul, smul_smul]
        rw [show μ * (q / μ) = q by field_simp]
        module }
  have h := estimateSequence_rate hS hL hμ.le hf hdiff u k
  simpa [Finset.prod_const, Finset.card_range] using h

end MathlibExt.Analysis.Convex.EstimateSequence
