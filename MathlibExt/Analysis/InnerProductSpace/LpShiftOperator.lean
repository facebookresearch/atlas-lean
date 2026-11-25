/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The unilateral shift on `ℓ²(ℕ, 𝕜)`

The unilateral (forward) shift `S` on `ℓ²(ℕ, 𝕜)` inserts a zero in
coordinate `0` and shifts every other coordinate up by one:
`(S x) 0 = 0`, `(S x) (n + 1) = x n`. Its adjoint is the backward
shift `B`, `(B x) n = x (n + 1)`. The shift is the textbook example
of an isometry that is not unitary: `B ∘ S = 1` while
`S ∘ B = 1 - rankOne e₀ e₀`, where `e₀` is the first standard basis
vector, so `S` is injective but not surjective. The spectra of `S`
and `B` (proved in `LpShiftOperatorSpectrum.lean`) are the closed unit
ball in the scalar field: the disc for `ℂ` and the interval `[-1, 1]` for `ℝ`.

These are new derived supporting results. The archived Hilbert-space and
spectral material in
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean` supplies
related context, rather than an exact unilateral-shift target or proof.
The construction reuses Mathlib's `ℓ²` space, coordinate vectors, inner product,
adjoint and rank-one operator APIs.

## Main declarations

* `shiftCLM` : the unilateral shift as a bounded operator on `ℓ²(ℕ, 𝕜)`.
* `backwardCLM` : the backward shift as a bounded operator on `ℓ²(ℕ, 𝕜)`.
* `shiftCLM_apply`, `backwardCLM_apply` : their pointwise actions.
* `norm_shiftCLM_apply` : the shift is an isometry,
  `‖S x‖ = ‖x‖`.
* `norm_shiftCLM` : `‖S‖ = 1`.
* `adjoint_shiftCLM` : `S† = B`.
* `backward_comp_shift` : `B ∘L S = 1`.
* `shift_comp_backward` : `S ∘L B = 1 - rankOne e₀ e₀`.
* `not_surjective_shiftCLM` : `S` is not surjective.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Forward shift of a sequence.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. The
forward shift of a sequence $x : \mathbb{N} \to \mathbb{K}$ is the sequence $S x$ with
$(S x)_0 = 0$ and $(S x)_{n+1} = x_n$ for every $n \in \mathbb{N}$. -/
def shiftFun (x : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => 0
  | n + 1 => x n

/-- **Backward shift of a sequence.** For any type $K$, the backward shift of a sequence
$x \colon \mathbb{N} \to K$ is the sequence $n \mapsto x_{n+1}$: it drops the coordinate $x_0$
and shifts every other coordinate down by one. -/
def backwardFun (x : ℕ → 𝕜) (i : ℕ) : 𝕜 := x (i + 1)

@[simp] theorem shiftFun_zero (x : ℕ → 𝕜) : shiftFun x 0 = 0 := rfl

@[simp] theorem shiftFun_succ (x : ℕ → 𝕜) (n : ℕ) : shiftFun x (n + 1) = x n := rfl

omit [RCLike 𝕜] in
@[simp] theorem backwardFun_apply (x : ℕ → 𝕜) (i : ℕ) : backwardFun x i = x (i + 1) :=
  rfl

/-- **The forward shift of a square-summable sequence is square-summable.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$. For every square-summable sequence $x = (x_0, x_1, x_2, \dots)$ in
$\mathbb{K}$, the forward-shifted sequence $(0, x_0, x_1, \dots)$ is also square-summable, that is,
it belongs to $\ell^2(\mathbb{N}, \mathbb{K})$. -/
theorem memℓp_shiftFun {x : ℓ²(ℕ, 𝕜)} : Memℓp (shiftFun (x : ℕ → 𝕜)) 2 := by
  apply memℓp_gen
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have h' : Summable (fun n => ‖shiftFun (x : ℕ → 𝕜) (n + 1)‖ ^ (2 : ℝ≥0∞).toReal) := by
    simpa only [shiftFun_succ] using h
  exact (summable_nat_add_iff 1).mp h'

/-- **The backward shift of an $\ell^2$ sequence is in $\ell^2$.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$. For every $x \in \ell^2(\mathbb{N}, \mathbb{K})$, the backward
shift $n \mapsto x_{n+1}$ of the sequence $x$ is square-summable, that is, it lies in
$\ell^2(\mathbb{N}, \mathbb{K})$.

Its squared absolute values are a tail of the squared absolute values of $x$. -/
theorem memℓp_backwardFun {x : ℓ²(ℕ, 𝕜)} : Memℓp (backwardFun (x : ℕ → 𝕜)) 2 := by
  apply memℓp_gen
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have h' : Summable (fun n => ‖backwardFun (x : ℕ → 𝕜) n‖ ^ (2 : ℝ≥0∞).toReal) := by
    simpa only [backwardFun_apply] using (summable_nat_add_iff 1).mpr h
  exact h'

/-- **Forward shift as a linear map.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. The
forward shift is the $\mathbb{K}$-linear map
$\ell^2(\mathbb{N}, \mathbb{K}) \to \ell^2(\mathbb{N}, \mathbb{K})$ sending $x$ to the forward
shift of the sequence $x$, that is, to $(0, x_0, x_1, \dots)$, which is again
square-summable. -/
noncomputable def shiftLinMap : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨shiftFun (x : ℕ → 𝕜), memℓp_shiftFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    cases i with
    | zero =>
        simp only [lp.coeFn_add, shiftFun_zero, Pi.add_apply, add_zero]
    | succ n => simp only [lp.coeFn_add, shiftFun_succ, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    cases i with
    | zero =>
        simp only [lp.coeFn_smul, shiftFun_zero, Pi.smul_apply, smul_zero]
    | succ n =>
        simp only [lp.coeFn_smul, shiftFun_succ, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]

/-- **Backward shift as a linear map.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. The
backward-shift linear map is the $\mathbb{K}$-linear map $B$ from $\ell^2(\mathbb{N}, \mathbb{K})$
to itself given by $(Bx)_n = x_{n+1}$ for all $x$ and all $n \in \mathbb{N}$. -/
noncomputable def backwardLinMap : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨backwardFun (x : ℕ → 𝕜), memℓp_backwardFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_add, backwardFun_apply, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, backwardFun_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

/-- **Coordinates of the forward-shift linear map.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. For every $x \in \ell^2(\mathbb{N}, \mathbb{K})$ and every $i \in \mathbb{N}$,
the $i$-th coordinate of the forward-shift linear map applied to $x$ equals the $i$-th term
of the forward shift of the sequence $x$, namely $0$ for $i = 0$ and $x_{i-1}$ for
$i \ge 1$. -/
theorem shiftLinMap_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    shiftLinMap x i = shiftFun (x : ℕ → 𝕜) i :=
  rfl

/-- **Coordinates of the backward-shift linear map.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. For every $x \in \ell^2(\mathbb{N}, \mathbb{K})$ and every $i \in \mathbb{N}$, the
$i$-th coordinate of the image of $x$ under the backward-shift linear map $B$ is the $i$-th term
of the backward shift of the sequence $x$, that is, $(Bx)_i = x_{i+1}$. -/
theorem backwardLinMap_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    backwardLinMap x i = backwardFun (x : ℕ → 𝕜) i :=
  rfl

/-- **Square sum of the forward shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$.
For every $x \in \ell^2(\mathbb{N}, \mathbb{K})$, the forward shift $S x = (0, x_0, x_1, \dots)$
of $x$ satisfies $\sum_{i=0}^{\infty} |(S x)_i|^2 = \sum_{i=0}^{\infty} |x_i|^2$. -/
theorem tsum_shiftFun_norm (x : ℓ²(ℕ, 𝕜)) :
    ∑' i, ‖shiftFun (x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal =
      ∑' i, ‖(x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal := by
  have hs : Summable (fun i => ‖shiftFun (x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    memℓp_shiftFun.summable (by simp)
  rw [hs.tsum_eq_zero_add]
  simp only [shiftFun_zero, shiftFun_succ, norm_zero,
    Real.zero_rpow (by simp : (2 : ℝ≥0∞).toReal ≠ 0), zero_add]

/-- **Square sum of the backward shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$.
For every $x \in \ell^2(\mathbb{N}, \mathbb{K})$, the backward shift $(x_1, x_2, \dots)$ of
$x$ satisfies $\sum_{i=0}^{\infty} |x_{i+1}|^2 \le \sum_{i=0}^{\infty} |x_i|^2$: the left
side is a tail of the right side. -/
theorem tsum_backwardFun_norm_le (x : ℓ²(ℕ, 𝕜)) :
    ∑' i, ‖backwardFun (x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal ≤
      ∑' i, ‖(x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal := by
  have hs : Summable (fun i => ‖(x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp x).summable (by simp)
  rw [hs.tsum_eq_zero_add]
  simp only [backwardFun_apply]
  exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)

/-- **The forward shift linear map preserves norms.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, and let $S$ be the forward shift on the space $\ell^2(\mathbb{N}, \mathbb{K})$ of
square-summable sequences in $\mathbb{K}$, viewed as a linear map and given by
$S(x_0, x_1, \dots) = (0, x_0, x_1, \dots)$. Then $\|Sx\| = \|x\|$ for every
$x \in \ell^2(\mathbb{N}, \mathbb{K})$. -/
theorem norm_shiftLinMap_apply (x : ℓ²(ℕ, 𝕜)) : ‖shiftLinMap x‖ = ‖x‖ := by
  have hpow : ‖shiftLinMap x‖ ^ (2 : ℝ≥0∞).toReal = ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (shiftLinMap x),
      lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact tsum_shiftFun_norm x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [hexp, Real.rpow_two, Real.rpow_two] at hpow
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hpow

/-- **The backward shift linear map does not increase norms.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, and let $B$ be the backward shift on the space $\ell^2(\mathbb{N}, \mathbb{K})$ of
square-summable sequences in $\mathbb{K}$, viewed as a linear map and given by
$(Bx)_n = x_{n+1}$. Then $\|Bx\| \le \|x\|$ for every $x \in \ell^2(\mathbb{N}, \mathbb{K})$. -/
theorem norm_backwardLinMap_apply_le (x : ℓ²(ℕ, 𝕜)) : ‖backwardLinMap x‖ ≤ ‖x‖ := by
  have hpow : ‖backwardLinMap x‖ ^ (2 : ℝ≥0∞).toReal ≤ ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (backwardLinMap x),
      lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact tsum_backwardFun_norm_le x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [hexp, Real.rpow_two, Real.rpow_two] at hpow
  exact le_of_sq_le_sq hpow (norm_nonneg _)

/-- **The unilateral shift operator.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. The
unilateral shift is the bounded linear operator $S$ on the Hilbert space
$\ell^2(\mathbb{N}, \mathbb{K})$ of square-summable sequences in $\mathbb{K}$ given by
$S(x_0, x_1, x_2, \dots) = (0, x_0, x_1, \dots)$. It is bounded because $\|Sx\| = \|x\|$ for every
$x$. -/
noncomputable def shiftCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  shiftLinMap.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact le_of_eq (norm_shiftLinMap_apply x))

/-- **Backward shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. The backward shift is the
bounded linear operator $B$ on $\ell^2(\mathbb{N}, \mathbb{K})$ given by $(Bx)_n = x_{n+1}$ for
all $x \in \ell^2(\mathbb{N}, \mathbb{K})$ and $n \in \mathbb{N}$. -/
noncomputable def backwardCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  backwardLinMap.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact norm_backwardLinMap_apply_le x)

/-- **Coordinates of the unilateral shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and
let $S$ be the unilateral shift on the Hilbert space $\ell^2(\mathbb{N}, \mathbb{K})$ of
square-summable sequences in $\mathbb{K}$. For every $x \in \ell^2(\mathbb{N}, \mathbb{K})$ and
every $i \in \mathbb{N}$, the coordinate $(Sx)_i$ is the $i$-th term of the forward shift of $x$:
$(Sx)_0 = 0$ and $(Sx)_{n+1} = x_n$ for every $n \in \mathbb{N}$. -/
theorem shiftCLM_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    shiftCLM x i = shiftFun (x : ℕ → 𝕜) i :=
  rfl

/-- **Coordinates of the backward shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. For
every $x \in \ell^2(\mathbb{N}, \mathbb{K})$ and every $i \in \mathbb{N}$, the $i$-th coordinate
of the backward shift $Bx$ is the $i$-th term of the backward shift of the sequence $x$,
that is, $(Bx)_i = x_{i+1}$. -/
theorem backwardCLM_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    backwardCLM x i = backwardFun (x : ℕ → 𝕜) i :=
  rfl

/-- **The unilateral shift preserves norms.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and
let $S$ be the unilateral shift on the Hilbert space $\ell^2(\mathbb{N}, \mathbb{K})$ of
square-summable sequences in $\mathbb{K}$, given by $S(x_0, x_1, \dots) = (0, x_0, x_1, \dots)$.
Then $\|Sx\| = \|x\|$ for every $x \in \ell^2(\mathbb{N}, \mathbb{K})$. -/
theorem norm_shiftCLM_apply (x : ℓ²(ℕ, 𝕜)) : ‖shiftCLM x‖ = ‖x‖ :=
  norm_shiftLinMap_apply x

/-- **The unilateral shift preserves distances.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. The unilateral shift $S$ on $\ell^2(\mathbb{N}, \mathbb{K})$ is an isometry:
$\|Sx - Sy\| = \|x - y\|$ for all $x, y \in \ell^2(\mathbb{N}, \mathbb{K})$. -/
theorem isometry_shiftCLM : Isometry (shiftCLM (𝕜 := 𝕜)) := by
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_shiftCLM_apply]

/-- **The unilateral shift has operator norm one.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, and let $S$ be the unilateral shift on the Hilbert space
$\ell^2(\mathbb{N}, \mathbb{K})$ of square-summable sequences in $\mathbb{K}$, given by
$S(x_0, x_1, \dots) = (0, x_0, x_1, \dots)$. Then the operator norm of $S$ is $\|S\| = 1$. -/
theorem norm_shiftCLM : ‖shiftCLM (𝕜 := 𝕜)‖ = 1 := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (by norm_num : (0 : ℝ) ≤ 1)
      (fun x => by rw [one_mul]; exact le_of_eq (norm_shiftLinMap_apply x))
  · have hle : ‖shiftCLM (lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜))‖ ≤
        ‖shiftCLM‖ * ‖(lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜))‖ :=
      ContinuousLinearMap.le_opNorm (σ₁₂ := RingHom.id 𝕜) (f := shiftCLM)
        (x := (lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜)))
    rw [norm_shiftCLM_apply, lp.norm_single (by simp : (0 : ℝ≥0∞) < 2), norm_one,
      mul_one] at hle
    exact hle

/-- **The backward shift has operator norm at most one.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, and let $B$ be the backward shift on the Hilbert space
$\ell^2(\mathbb{N}, \mathbb{K})$ of square-summable sequences in $\mathbb{K}$, given by
$(Bx)_n = x_{n+1}$. Then the operator norm of $B$ satisfies $\|B\| \le 1$. -/
theorem norm_backwardCLM_le : ‖backwardCLM (𝕜 := 𝕜)‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ (by norm_num : (0 : ℝ) ≤ 1)
    (fun x => by rw [one_mul]; exact norm_backwardLinMap_apply_le x)

/-- **Adjoint of the unilateral shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. The
adjoint of the unilateral shift $S$ on $\ell^2(\mathbb{N}, \mathbb{K})$ is the backward shift
$B$: $S^* = B$. -/
theorem adjoint_shiftCLM : (shiftCLM (𝕜 := 𝕜))† = backwardCLM := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have hs : Summable (fun i => ⟪(x : ℕ → 𝕜) i, (shiftCLM y : ℕ → 𝕜) i⟫_𝕜) :=
    lp.summable_inner x (shiftCLM y)
  rw [hs.tsum_eq_zero_add]
  simp [shiftCLM_apply, backwardCLM_apply]

/-- **Left inverse of the unilateral shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$.
The backward shift $B$ is a left inverse of the unilateral shift $S$ on
$\ell^2(\mathbb{N}, \mathbb{K})$: $BS = I$, where $I$ is the identity operator. -/
theorem backward_comp_shift : backwardCLM ∘L shiftCLM = (1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, backwardCLM_apply, shiftCLM_apply,
    backwardFun_apply, shiftFun_succ, one_apply_eq_self]

/-- **The unilateral shift is injective.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. The
unilateral shift on $\ell^2(\mathbb{N}, \mathbb{K})$ is injective. -/
theorem injective_shiftCLM : Function.Injective (shiftCLM (𝕜 := 𝕜)) := by
  apply Function.LeftInverse.injective (g := backwardCLM)
  intro x
  simpa using DFunLike.congr_fun backward_comp_shift x

/-- **Coordinates of the unilateral shift after the backward shift.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, and on the Hilbert space $\ell^2(\mathbb{N}, \mathbb{K})$ of
square-summable sequences in $\mathbb{K}$ let $S$ be the unilateral shift,
$S(x_0, x_1, \dots) = (0, x_0, x_1, \dots)$, and $B$ the backward shift, $(Bx)_n = x_{n+1}$.
Then for every $x \in \ell^2(\mathbb{N}, \mathbb{K})$ and every $i \in \mathbb{N}$, the coordinate
$(SBx)_i$ is $0$ if $i = 0$ and is $x_i$ if $i \ne 0$. -/
theorem shift_comp_backward_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    (shiftCLM ∘L backwardCLM) x i = if i = 0 then 0 else x i := by
  cases i with
  | zero =>
      rw [ite_eq_left rfl]
      simp only [ContinuousLinearMap.comp_apply, shiftCLM_apply, shiftFun_zero]
  | succ n =>
      rw [ite_eq_right (Nat.succ_ne_zero n)]
      simp only [ContinuousLinearMap.comp_apply, shiftCLM_apply, shiftFun_succ,
        backwardCLM_apply, backwardFun_apply]

/-- **The unilateral shift composed with the backward shift.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $S$ be the unilateral (forward) shift and $B$ the
backward shift on $\ell^2(\mathbb{N}, \mathbb{K})$, and let $e_0$ be the first standard
basis vector. Then $S \circ B = 1 - P$, where $P$ is the rank-one operator
$P x = \langle e_0, x \rangle e_0 = x_0 e_0$.

Thus $S \circ B$ is the orthogonal projection onto $\{e_0\}^\perp$. -/
theorem shift_comp_backward :
    shiftCLM ∘L backwardCLM =
      (1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) -
        InnerProductSpace.rankOne 𝕜 (lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜))
          (lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜)) := by
  ext x i
  rw [shift_comp_backward_apply]
  cases i with
  | zero =>
      rw [ite_eq_left rfl]
      simp only [sub_apply, one_apply_eq_self,
        lp.coeFn_sub, InnerProductSpace.rankOne_apply, lp.inner_single_left,
        RCLike.inner_apply, map_one, Pi.sub_apply, lp.coeFn_smul,
        Pi.smul_apply, lp.coeFn_single, Pi.single_eq_same, smul_eq_mul, mul_one,
        sub_self]
  | succ n =>
      rw [ite_eq_right (Nat.succ_ne_zero n)]
      simp only [sub_apply, one_apply_eq_self,
        lp.coeFn_sub, InnerProductSpace.rankOne_apply, lp.inner_single_left,
        RCLike.inner_apply, map_one, Pi.sub_apply, lp.coeFn_smul,
        Pi.smul_apply, lp.coeFn_single, Pi.single_eq_of_ne (Nat.succ_ne_zero n),
        smul_eq_mul, mul_zero, sub_zero]

/-- **The unilateral shift is not surjective.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$,
and let $S$ be the unilateral shift on the Hilbert space $\ell^2(\mathbb{N}, \mathbb{K})$ of
square-summable sequences in $\mathbb{K}$, given by $S(x_0, x_1, \dots) = (0, x_0, x_1, \dots)$.
Then $S$ is not surjective.

The first standard basis vector $e_0 = (1, 0, 0, \dots)$ is not in the range of $S$, since every
vector in the range has $0$ in coordinate $0$. -/
theorem not_surjective_shiftCLM : ¬ Function.Surjective (shiftCLM (𝕜 := 𝕜)) := by
  intro h
  obtain ⟨x, hx⟩ := h (lp.single 2 0 (1 : 𝕜))
  have h0 := congr_fun (congr_arg (fun z : ℓ²(ℕ, 𝕜) => (z : ℕ → 𝕜)) hx) 0
  simp [shiftCLM_apply, lp.single_apply] at h0

end MathlibExt.Analysis.InnerProductSpace.LpShiftOperator
