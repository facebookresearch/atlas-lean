/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Reproducing
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Filter.AtTopBot.Defs

/-!
# The representer theorem

Let `H` be a reproducing kernel Hilbert space (Mathlib's `RKHS 𝕜 H X V`) of functions
`X → V` with kernel functions `RKHS.kerFun H x : V →L[𝕜] H`, so that
`⟪kerFun H x v, f⟫ = ⟪v, f x⟫` (for scalar-valued kernels, `V = 𝕜`, `kerFun H x 1` is the
function `k(·, x)`). Fix sample points `x₁, …, xₙ`, a loss `L : (Fin n → V) → ℝ` of the values
`f(x₁), …, f(xₙ)` and a regularizer `Ω : ℝ → ℝ`, and consider the regularized risk

  `J f = L (f x₁, …, f xₙ) + Ω ‖f‖`.

The *kernel expansions* are the functions `∑ i, kerFun H xᵢ cᵢ` (`kernelExpansion`).

## Main results

* `mem_topologicalClosure_range_of_isMinimizer` and `exists_eq_kernelExpansion_of_isMinimizer`:
  **the representer theorem** (Schölkopf, Herbrich and Smola, Theorem 1). If `Ω` is strictly
  increasing on `[0, ∞)`, every minimizer of `J` lies in the closed span of the kernel functions
  at the sample points; when `V` is finite-dimensional (for instance `V = 𝕜`) this span is closed,
  so every minimizer is a kernel expansion `∑ i, kerFun H xᵢ cᵢ`.
* `exists_kernelExpansion_isMinimizer`: existence of a minimizer, which is a kernel expansion,
  for `V` finite-dimensional, `L` continuous and bounded below, and `Ω` continuous, monotone on
  `[0, ∞)` and tending to `∞`.
* `isMinimizer_unique`: uniqueness of the minimizer (real scalars) for convex `L` and `Ω`
  strictly convex and monotone on `[0, ∞)`.
* `kernelRidgeFit` and `kernelRidgeRisk_kernelRidgeFit_le`, `eq_kernelRidgeFit_of_le`: **kernel
  ridge regression** (the penalized least-squares case of Kimeldorf and Wahba). For a real
  scalar kernel with Gram matrix `K i j = k(xᵢ, xⱼ)` and `λ > 0`, the unique minimizer of
  `∑ i (yᵢ - f xᵢ)² + λ ‖f‖²` is the kernel expansion with coefficients `α = (K + λ I)⁻¹ y`,
  and its fitted values are `K α` (`kernelRidgeFit_apply`).

## Conventions

Mathlib's kernel functions satisfy `kerFun H y v x = kernel H x y v`. A *minimizer* of `J` is a
global minimizer (`∀ g, J f ≤ J g`). Nothing is assumed about `L` in the representer theorem
itself, and the hypothesis on `Ω` is that of Schölkopf, Herbrich and Smola; their loss may also
take the value `+∞`, while `L` here is real-valued. Existence uses continuity of `L` rather than
convexity. Uniqueness needs strict convexity of `Ω`: with `Ω t = t` and a convex hinge-type loss
the minimizer can fail to be unique.

The output space `V` may be any Hilbert space for the closed-span form; the span itself is closed
only when `V` is finite-dimensional, which is why the other results assume it.

## References

* G. Kimeldorf and G. Wahba, "Some results on Tchebycheffian spline functions",
  *J. Math. Anal. Appl.* **33** (1971), 82–95.
* B. Schölkopf, R. Herbrich and A. J. Smola, "A generalized representer theorem",
  *COLT 2001*, LNCS **2111** (2001), 416–426, Theorem 1.
-/

@[expose] public section

open Filter Matrix RKHS
open scoped InnerProductSpace

namespace MathlibExt.Analysis.FunctionalAnalysis.RepresenterTheorem

section General

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X V] {n : ℕ}

/-- The regularized risk `L (f x₁, …, f xₙ) + Ω ‖f‖` of `f` in the RKHS `H`. -/
noncomputable def regularizedRisk (x : Fin n → X) (L : (Fin n → V) → ℝ) (Ω : ℝ → ℝ) (f : H) :
    ℝ :=
  L (fun i => f (x i)) + Ω ‖f‖

/-- The kernel expansion map `c ↦ ∑ i, kerFun H (x i) (c i)`. Its range is the span of the
kernel functions at the sample points `x i`. -/
noncomputable def kernelExpansion (x : Fin n → X) : (Fin n → V) →L[𝕜] H :=
  ∑ i, kerFun H (x i) ∘L ContinuousLinearMap.proj i

variable {H}

private theorem kernelExpansion_single (x : Fin n → X) (i : Fin n) (v : V) :
    kernelExpansion H x (Pi.single i v) = kerFun H (x i) v := by
  simp only [kernelExpansion, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- A function orthogonal to every kernel expansion vanishes at the sample points. -/
private theorem apply_eq_zero_of_mem_orthogonal (x : Fin n → X) {h : H}
    (hh : h ∈ (LinearMap.range (kernelExpansion H x).toLinearMap)ᗮ) (i : Fin n) :
    h (x i) = 0 := by
  have h0 := (Submodule.mem_orthogonal' _ _).1 hh (kernelExpansion H x (Pi.single i (h (x i))))
    ⟨_, rfl⟩
  rw [inner_eq_zero_symm, kernelExpansion_single, kerFun_inner] at h0
  exact inner_self_eq_zero.mp h0

/-- The orthogonal projection onto the closed span of the kernel functions keeps the sample
values and does not increase the norm; it decreases it strictly unless it is the identity. -/
private theorem exists_proj (x : Fin n → X) (g : H) :
    ∃ p ∈ (LinearMap.range (kernelExpansion H x).toLinearMap).topologicalClosure,
      (∀ i, p (x i) = g (x i)) ∧ ‖p‖ ≤ ‖g‖ ∧ (p ≠ g → ‖p‖ < ‖g‖) := by
  set K := (LinearMap.range (kernelExpansion H x).toLinearMap).topologicalClosure
  have : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set p := K.starProjection g
  have hpK : p ∈ K := K.starProjection_apply_mem g
  have hh : g - p ∈ Kᗮ := K.sub_starProjection_mem_orthogonal g
  have hh' : g - p ∈ (LinearMap.range (kernelExpansion H x).toLinearMap)ᗮ := by
    rwa [Submodule.orthogonal_closure] at hh
  have hval : ∀ i, (g - p) (x i) = 0 := apply_eq_zero_of_mem_orthogonal x hh'
  have hpy : ‖g‖ * ‖g‖ = ‖p‖ * ‖p‖ + ‖g - p‖ * ‖g - p‖ := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) p (g - p)
      ((K.mem_orthogonal' _).1 hh p hpK |> fun h => by rwa [inner_eq_zero_symm] at h)
    simpa using this
  refine ⟨p, hpK, fun i => ?_, ?_, fun hne => ?_⟩
  · have := hval i
    rw [coe_sub, Pi.sub_apply, sub_eq_zero] at this
    exact this.symm
  · nlinarith [norm_nonneg p, norm_nonneg g, mul_self_nonneg ‖g - p‖]
  · have hpos : 0 < ‖g - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
    nlinarith [norm_nonneg p, norm_nonneg g, mul_pos hpos hpos]

/-- **The representer theorem** (closed-span form): if `Ω` is strictly increasing on `[0, ∞)`,
every global minimizer of the regularized risk lies in the closure of the span of the kernel
functions at the sample points. -/
theorem mem_topologicalClosure_range_of_isMinimizer {x : Fin n → X} {L : (Fin n → V) → ℝ}
    {Ω : ℝ → ℝ} (hΩ : StrictMonoOn Ω (Set.Ici 0)) {f : H}
    (hf : ∀ g : H, regularizedRisk H x L Ω f ≤ regularizedRisk H x L Ω g) :
    f ∈ (LinearMap.range (kernelExpansion H x).toLinearMap).topologicalClosure := by
  obtain ⟨p, hpK, hval, -, hlt⟩ := exists_proj x f
  by_cases hpf : p = f
  · exact hpf ▸ hpK
  have hJ := hf p
  have hfp : (fun i => p (x i)) = fun i => f (x i) := funext hval
  have := hΩ (Set.mem_Ici.mpr (norm_nonneg p)) (Set.mem_Ici.mpr (norm_nonneg f)) (hlt hpf)
  simp only [regularizedRisk, hfp] at hJ
  linarith

/-- **The representer theorem** (Schölkopf, Herbrich and Smola, Theorem 1): for a
finite-dimensional output space `V` (for instance a scalar kernel, `V = 𝕜`) and `Ω` strictly
increasing on `[0, ∞)`, every global minimizer of `L (f x₁, …, f xₙ) + Ω ‖f‖` is a kernel
expansion `∑ i, kerFun H (x i) (c i)`. -/
theorem exists_eq_kernelExpansion_of_isMinimizer [FiniteDimensional 𝕜 V] {x : Fin n → X}
    {L : (Fin n → V) → ℝ} {Ω : ℝ → ℝ} (hΩ : StrictMonoOn Ω (Set.Ici 0)) {f : H}
    (hf : ∀ g : H, regularizedRisk H x L Ω f ≤ regularizedRisk H x L Ω g) :
    ∃ c : Fin n → V, f = kernelExpansion H x c := by
  have hf' := mem_topologicalClosure_range_of_isMinimizer hΩ hf
  rw [(Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq] at hf'
  obtain ⟨c, hc⟩ := hf'
  exact ⟨c, hc.symm⟩

/-- **Existence of a minimizer**: for finite-dimensional `V`, a continuous loss bounded below,
and a continuous regularizer that is monotone on `[0, ∞)` and tends to `∞`, the regularized risk
has a global minimizer, and it can be taken to be a kernel expansion. -/
theorem exists_kernelExpansion_isMinimizer [FiniteDimensional 𝕜 V] (x : Fin n → X)
    {L : (Fin n → V) → ℝ} (hL : Continuous L) (hLb : BddBelow (Set.range L)) {Ω : ℝ → ℝ}
    (hΩc : Continuous Ω) (hΩm : MonotoneOn Ω (Set.Ici 0)) (hΩt : Tendsto Ω atTop atTop) :
    ∃ c : Fin n → V, ∀ g : H,
      regularizedRisk H x L Ω (kernelExpansion H x c) ≤ regularizedRisk H x L Ω g := by
  set W := LinearMap.range (kernelExpansion H x).toLinearMap
  have hWc : IsClosed (W : Set H) := Submodule.closed_of_finiteDimensional _
  have : ProperSpace W := FiniteDimensional.proper_rclike 𝕜 W
  obtain ⟨b, hb⟩ := hLb
  set φ : W → ℝ := fun w => regularizedRisk H x L Ω (w : H)
  have hφc : Continuous φ := by
    refine (hL.comp ?_).add (hΩc.comp (continuous_norm.comp continuous_subtype_val))
    exact continuous_pi fun i => (RKHS.continuous_eval_const (x i)).comp continuous_subtype_val
  have hφt : Tendsto φ (Filter.cocompact W) atTop := by
    have h1 : Tendsto (fun w : W => b + Ω ‖(w : H)‖) (Filter.cocompact W) atTop :=
      tendsto_atTop_add_const_left _ b (hΩt.comp tendsto_norm_cocompact_atTop)
    refine tendsto_atTop_mono (fun w => ?_) h1
    simp only [φ, regularizedRisk]
    linarith [hb ⟨fun i => (w : H) (x i), rfl⟩]
  obtain ⟨w₀, hw₀⟩ := hφc.exists_forall_le hφt
  obtain ⟨c, hc⟩ := w₀.2
  refine ⟨c, fun g => ?_⟩
  obtain ⟨p, hpK, hval, hle, -⟩ := exists_proj x g
  rw [hWc.submodule_topologicalClosure_eq] at hpK
  have h1 := hw₀ ⟨p, hpK⟩
  have hfp : (fun i => p (x i)) = fun i => g (x i) := funext hval
  have h2 : Ω ‖p‖ ≤ Ω ‖g‖ :=
    hΩm (Set.mem_Ici.mpr (norm_nonneg p)) (Set.mem_Ici.mpr (norm_nonneg g)) hle
  simp only [φ, regularizedRisk, hfp] at h1
  rw [show kernelExpansion H x c = (w₀ : H) from hc]
  simp only [regularizedRisk]
  linarith

end General

section Real

variable {X : Type*}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [RKHS ℝ H X V] {n : ℕ}

omit [CompleteSpace V] [CompleteSpace H] in
/-- **Uniqueness of the minimizer** (real scalars): for a convex loss `L` and a regularizer `Ω`
that is strictly convex and monotone on `[0, ∞)` (for instance `Ω t = λ t²` with `λ > 0`), the
regularized risk has at most one global minimizer. -/
theorem isMinimizer_unique {x : Fin n → X} {L : (Fin n → V) → ℝ} (hL : ConvexOn ℝ Set.univ L)
    {Ω : ℝ → ℝ} (hΩc : StrictConvexOn ℝ (Set.Ici 0) Ω) (hΩm : MonotoneOn Ω (Set.Ici 0))
    {f₁ f₂ : H} (h₁ : ∀ g : H, regularizedRisk H x L Ω f₁ ≤ regularizedRisk H x L Ω g)
    (h₂ : ∀ g : H, regularizedRisk H x L Ω f₂ ≤ regularizedRisk H x L Ω g) : f₁ = f₂ := by
  by_contra hne
  have hmono : StrictMonoOn Ω (Set.Ici 0) := by
    intro s hs t ht hst
    have hm : (1 / 2 : ℝ) • s + (1 / 2 : ℝ) • t ∈ Set.Ici (0 : ℝ) := by
      simp only [Set.mem_Ici, smul_eq_mul] at hs ht ⊢; positivity
    have h1 := hΩc.2 hs ht hst.ne (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have h2 := hΩm hs hm (by simp only [smul_eq_mul]; linarith)
    simp only [smul_eq_mul] at h1 h2
    linarith
  set m : H := (1 / 2 : ℝ) • (f₁ + f₂)
  have hvals : (fun i => m (x i)) =
      (1 / 2 : ℝ) • (fun i => f₁ (x i)) + (1 / 2 : ℝ) • (fun i => f₂ (x i)) := by
    funext i
    simp [m, smul_add]
  have hLm : L (fun i => m (x i)) ≤
      (1 / 2 : ℝ) * L (fun i => f₁ (x i)) + (1 / 2 : ℝ) * L (fun i => f₂ (x i)) := by
    rw [hvals]
    exact hL.2 (Set.mem_univ _) (Set.mem_univ _) (by norm_num) (by norm_num) (by norm_num)
  set a := ‖f₁‖
  set b := ‖f₂‖
  have hm_le : ‖m‖ ≤ (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b := by
    simp only [m, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith [norm_add_le f₁ f₂]
  have hΩm' : Ω ‖m‖ < (1 / 2 : ℝ) * Ω a + (1 / 2 : ℝ) * Ω b := by
    rcases eq_or_ne a b with hab | hab
    · have hpar := parallelogram_law_with_norm ℝ f₁ f₂
      have hd : 0 < ‖f₁ - f₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hpar' : ‖f₁ + f₂‖ ^ 2 + ‖f₁ - f₂‖ ^ 2 = 2 * (a ^ 2 + b ^ 2) := hpar
      have ha0 : 0 ≤ a := norm_nonneg f₁
      have hsum : ‖f₁ + f₂‖ < 2 * a := by
        by_contra hc
        rw [not_lt] at hc
        rw [← hab] at hpar'
        nlinarith [mul_pos hd hd, norm_nonneg (f₁ + f₂)]
      have hma : ‖m‖ < a := by
        simp only [m, norm_smul, Real.norm_eq_abs]
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith
      have := hmono (Set.mem_Ici.mpr (norm_nonneg m)) (Set.mem_Ici.mpr (norm_nonneg f₁)) hma
      rw [← hab]
      linarith
    · have h1 := hΩc.2 (Set.mem_Ici.mpr (norm_nonneg f₁)) (Set.mem_Ici.mpr (norm_nonneg f₂))
        hab (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      have hmid : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b ∈ Set.Ici (0 : ℝ) :=
        Set.mem_Ici.mpr (by have := norm_nonneg f₁; have := norm_nonneg f₂; linarith)
      have h2 : Ω ‖m‖ ≤ Ω ((1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b) :=
        hΩm (Set.mem_Ici.mpr (norm_nonneg m)) hmid hm_le
      simp only [smul_eq_mul] at h1
      linarith
  have hJ := h₁ m
  have hJ₁₂ := h₁ f₂
  have hJ₂₁ := h₂ f₁
  simp only [regularizedRisk] at hJ hJ₁₂ hJ₂₁
  linarith

end Real

section KernelRidge

variable {X : Type*}
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [RKHS ℝ H X ℝ] {n : ℕ}

/-- The Gram matrix `K i j = k(x i, x j)` of a real scalar kernel at the sample points, where
`k(x, y) = kernel H x y 1`. -/
noncomputable def kernelGram (x : Fin n → X) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => kernel H (x i) (x j) 1

/-- The kernel ridge objective `∑ i, (y i - f (x i))² + λ ‖f‖²`. -/
noncomputable def kernelRidgeRisk (x : Fin n → X) (y : Fin n → ℝ) (lam : ℝ) (f : H) : ℝ :=
  ∑ i, (y i - f (x i)) ^ 2 + lam * ‖f‖ ^ 2

/-- The kernel ridge fit: the kernel expansion with coefficients `(K + λ I)⁻¹ y`. -/
noncomputable def kernelRidgeFit (x : Fin n → X) (y : Fin n → ℝ) (lam : ℝ) : H :=
  kernelExpansion H x ((kernelGram H x + lam • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ *ᵥ y)

variable {H}

omit [CompleteSpace H] in
/-- The kernel ridge objective is the regularized risk with the squared loss and
`Ω t = λ t²`. -/
theorem kernelRidgeRisk_eq_regularizedRisk (x : Fin n → X) (y : Fin n → ℝ) (lam : ℝ) (f : H) :
    kernelRidgeRisk H x y lam f =
      regularizedRisk H x (fun v => ∑ i, (y i - v i) ^ 2) (fun t => lam * t ^ 2) f :=
  rfl

private theorem kernelExpansion_eq_sum (x : Fin n → X) (c : Fin n → ℝ) :
    kernelExpansion H x c = ∑ i, kerFun H (x i) (c i) := by
  simp [kernelExpansion]

private theorem kernelExpansion_apply (x : Fin n → X) (c : Fin n → ℝ) (z : X) :
    kernelExpansion H x c z = ∑ i, kernel H z (x i) 1 * c i := by
  rw [kernelExpansion_eq_sum, ← eval_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_apply, kerFun_apply, mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- The values of a kernel expansion at the sample points are `K c`. -/
theorem kernelExpansion_apply_sample (x : Fin n → X) (c : Fin n → ℝ) (j : Fin n) :
    kernelExpansion H x c (x j) = (kernelGram H x *ᵥ c) j := by
  rw [kernelExpansion_apply]
  rfl

private theorem inner_kernelExpansion (x : Fin n → X) (c : Fin n → ℝ) (h : H) :
    ⟪kernelExpansion H x c, h⟫_ℝ = ∑ i, c i * h (x i) := by
  rw [kernelExpansion_eq_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kerFun_inner, Real.inner_apply]

/-- The kernel Gram matrix is positive semidefinite. -/
theorem posSemidef_kernelGram (x : Fin n → X) : (kernelGram H x).PosSemidef := by
  have h : kernelGram H x = Matrix.gram ℝ (fun i => kerFun H (x i) (1 : ℝ)) := by
    ext i j
    simp only [kernelGram, Matrix.gram, Matrix.of_apply]
    rw [← kerFun_apply, kerFun_inner, Real.inner_apply, one_mul]
  rw [h]
  exact Matrix.posSemidef_gram ℝ _

private theorem isUnit_det_kernelGram_add (x : Fin n → X) {lam : ℝ} (hlam : 0 < lam) :
    IsUnit (kernelGram H x + lam • (1 : Matrix (Fin n) (Fin n) ℝ)).det :=
  (PosDef.posSemidef_add (posSemidef_kernelGram x) (PosDef.one.smul hlam)).det_pos.ne'.isUnit

/-- The fitted values of kernel ridge regression are `K (K + λ I)⁻¹ y`. -/
theorem kernelRidgeFit_apply (x : Fin n → X) (y : Fin n → ℝ) (lam : ℝ) (j : Fin n) :
    kernelRidgeFit H x y lam (x j) =
      ((kernelGram H x * (kernelGram H x + lam • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹) *ᵥ y) j := by
  rw [kernelRidgeFit, kernelExpansion_apply_sample, mulVec_mulVec]

omit [CompleteSpace H] in
private theorem kernelRidgeRisk_add (x : Fin n → X) (y : Fin n → ℝ) (lam : ℝ) (f h : H) :
    kernelRidgeRisk H x y lam (f + h) = kernelRidgeRisk H x y lam f -
      2 * ∑ i, (y i - f (x i)) * h (x i) + 2 * lam * ⟪f, h⟫_ℝ +
      (∑ i, h (x i) ^ 2 + lam * ‖h‖ ^ 2) := by
  have hs : ∑ i, (y i - (f + h) (x i)) ^ 2 = ∑ i, (y i - f (x i)) ^ 2 -
      2 * ∑ i, (y i - f (x i)) * h (x i) + ∑ i, h (x i) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [coe_add, Pi.add_apply]
    ring
  simp only [kernelRidgeRisk, hs, norm_add_sq_real]
  ring

/-- The excess risk of `kernelRidgeFit + h` over the fit is `∑ h(xᵢ)² + λ ‖h‖²`. -/
private theorem kernelRidgeRisk_fit_add (x : Fin n → X) (y : Fin n → ℝ) {lam : ℝ}
    (hlam : 0 < lam) (h : H) :
    kernelRidgeRisk H x y lam (kernelRidgeFit H x y lam + h) =
      kernelRidgeRisk H x y lam (kernelRidgeFit H x y lam) +
        (∑ i, h (x i) ^ 2 + lam * ‖h‖ ^ 2) := by
  set A := kernelGram H x + lam • (1 : Matrix (Fin n) (Fin n) ℝ)
  set α := A⁻¹ *ᵥ y
  have hA : A *ᵥ α = y := by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_det_kernelGram_add x hlam), one_mulVec]
  have hres : ∀ i, y i - kernelRidgeFit H x y lam (x i) = lam * α i := by
    intro i
    have := congrFun hA i
    rw [kernelRidgeFit, kernelExpansion_apply_sample, ← this]
    simp only [A, add_mulVec, smul_mulVec, one_mulVec, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hin : ⟪kernelRidgeFit H x y lam, h⟫_ℝ = ∑ i, α i * h (x i) := by
    rw [kernelRidgeFit, inner_kernelExpansion]
  rw [kernelRidgeRisk_add, hin]
  simp only [hres, mul_assoc, ← Finset.mul_sum]
  ring

/-- **Kernel ridge regression** (Kimeldorf and Wahba): for `λ > 0` the kernel ridge fit
minimizes `∑ i, (y i - f (x i))² + λ ‖f‖²` over the whole RKHS. -/
theorem kernelRidgeRisk_kernelRidgeFit_le (x : Fin n → X) (y : Fin n → ℝ) {lam : ℝ}
    (hlam : 0 < lam) (g : H) :
    kernelRidgeRisk H x y lam (kernelRidgeFit H x y lam) ≤ kernelRidgeRisk H x y lam g := by
  have h := kernelRidgeRisk_fit_add x y hlam (g - kernelRidgeFit H x y lam)
  rw [add_sub_cancel] at h
  rw [h]
  have : 0 ≤ ∑ i, (g - kernelRidgeFit H x y lam) (x i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [sq_nonneg ‖g - kernelRidgeFit H x y lam‖]

/-- The kernel ridge fit is the unique minimizer for `λ > 0`. -/
theorem eq_kernelRidgeFit_of_le (x : Fin n → X) (y : Fin n → ℝ) {lam : ℝ} (hlam : 0 < lam)
    {g : H}
    (hg : kernelRidgeRisk H x y lam g ≤ kernelRidgeRisk H x y lam (kernelRidgeFit H x y lam)) :
    g = kernelRidgeFit H x y lam := by
  have h := kernelRidgeRisk_fit_add x y hlam (g - kernelRidgeFit H x y lam)
  rw [add_sub_cancel] at h
  have h0 : 0 ≤ ∑ i, (g - kernelRidgeFit H x y lam) (x i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : lam * ‖g - kernelRidgeFit H x y lam‖ ^ 2 ≤ 0 := by linarith
  have h2 : ‖g - kernelRidgeFit H x y lam‖ ^ 2 ≤ 0 := by
    by_contra hc
    linarith [mul_pos hlam (not_le.mp hc)]
  have h3 : ‖g - kernelRidgeFit H x y lam‖ = 0 := by
    nlinarith [norm_nonneg (g - kernelRidgeFit H x y lam)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h3)

end KernelRidge

end MathlibExt.Analysis.FunctionalAnalysis.RepresenterTheorem
